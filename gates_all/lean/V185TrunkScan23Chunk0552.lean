import V185TrunkScan23Chunk0551

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3262825 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 6, 2, 2]
def baseStart_3262825 : Nat := 118140960795 + 3262825 * 2 ^ 59
def prefixEnd_3262825 : Nat := 4983230072969 + 3 ^ 40 * 3262825 * 2
def baseEnd_3262825 : Nat := 1675397516506301915882047

theorem tailTrace_3262825 : CollatzResearch.WordTrace tailWord_3262825 prefixEnd_3262825 1675397516506301915882047 := by
  unfold tailWord_3262825
  simp only [CollatzResearch.WordTrace]
  refine ⟨119005004404349745990477929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79336669602899830660318619 119005004404349745990477929)
  ·
    refine ⟨89253753303262309492858447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119005004404349745990477929 89253753303262309492858447)
    ·
      refine ⟨133880629954893464239287671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89253753303262309492858447 133880629954893464239287671)
      ·
        refine ⟨200820944932340196358931507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133880629954893464239287671 200820944932340196358931507)
        ·
          refine ⟨301231417398510294538397261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200820944932340196358931507 301231417398510294538397261)
          ·
            refine ⟨112961781524441360451898973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301231417398510294538397261 112961781524441360451898973)
            ·
              refine ⟨42360668071665510169462115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112961781524441360451898973 42360668071665510169462115)
              ·
                refine ⟨63541002107498265254193173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42360668071665510169462115 63541002107498265254193173)
                ·
                  refine ⟨2978484473788981183790305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63541002107498265254193173 2978484473788981183790305)
                  ·
                    refine ⟨2233863355341735887842729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2978484473788981183790305 2233863355341735887842729)
                    ·
                      refine ⟨1675397516506301915882047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233863355341735887842729 1675397516506301915882047)
                      ·
                        rfl

theorem cell23_3262825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2, 2].length) (baseStart_3262825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262825 prefixEnd_3262825 := by exact prefixLift 3262825
  have htrace : WordTrace (prefixWord ++ tailWord_3262825) baseStart_3262825 baseEnd_3262825 := by
    simpa [prefixWord, tailWord_3262825, baseEnd_3262825] using wordTrace_append hprefix tailTrace_3262825
  have hstable : (prefixWord ++ tailWord_3262825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262825).length < 2 ^ (prefixWord ++ tailWord_3262825).sum := by decide
  have hdescent : baseEnd_3262825 < baseStart_3262825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262841 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3262841 : Nat := 118140960795 + 3262841 * 2 ^ 59
def prefixEnd_3262841 : Nat := 4983230072969 + 3 ^ 40 * 3262841 * 2
def baseEnd_3262841 : Nat := 1675405732196773853281973

theorem tailTrace_3262841 : CollatzResearch.WordTrace tailWord_3262841 prefixEnd_3262841 1675405732196773853281973 := by
  unfold tailWord_3262841
  simp only [CollatzResearch.WordTrace]
  refine ⟨119005587972291780723060377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79337058648194520482040251 119005587972291780723060377)
  ·
    refine ⟨89254190979218835542295283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119005587972291780723060377 89254190979218835542295283)
    ·
      refine ⟨133881286468828253313442925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89254190979218835542295283 133881286468828253313442925)
      ·
        refine ⟨50205482425810594992541097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133881286468828253313442925 50205482425810594992541097)
        ·
          refine ⟨37654111819357946244405823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50205482425810594992541097 37654111819357946244405823)
          ·
            refine ⟨56481167729036919366608735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37654111819357946244405823 56481167729036919366608735)
            ·
              refine ⟨84721751593555379049913103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56481167729036919366608735 84721751593555379049913103)
              ·
                refine ⟨127082627390333068574869655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84721751593555379049913103 127082627390333068574869655)
                ·
                  refine ⟨190623941085499602862304483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127082627390333068574869655 190623941085499602862304483)
                  ·
                    refine ⟨285935911628249404293456725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190623941085499602862304483 285935911628249404293456725)
                    ·
                      refine ⟨1675405732196773853281973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 285935911628249404293456725 1675405732196773853281973)
                      ·
                        rfl

theorem cell23_3262841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3262841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262841 prefixEnd_3262841 := by exact prefixLift 3262841
  have htrace : WordTrace (prefixWord ++ tailWord_3262841) baseStart_3262841 baseEnd_3262841 := by
    simpa [prefixWord, tailWord_3262841, baseEnd_3262841] using wordTrace_append hprefix tailTrace_3262841
  have hstable : (prefixWord ++ tailWord_3262841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262841).length < 2 ^ (prefixWord ++ tailWord_3262841).sum := by decide
  have hdescent : baseEnd_3262841 < baseStart_3262841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262859 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 2, 2, 2]
def baseStart_3262859 : Nat := 118140960795 + 3262859 * 2 ^ 59
def prefixEnd_3262859 : Nat := 4983230072969 + 3 ^ 40 * 3262859 * 2
def baseEnd_3262859 : Nat := 1675414974848554782856891

theorem tailTrace_3262859 : CollatzResearch.WordTrace tailWord_3262859 prefixEnd_3262859 1675414974848554782856891 := by
  unfold tailWord_3262859
  simp only [CollatzResearch.WordTrace]
  refine ⟨119006244486226569797215631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79337496324151046531477087 119006244486226569797215631)
  ·
    refine ⟨178509366729339854695823447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119006244486226569797215631 178509366729339854695823447)
    ·
      refine ⟨267764050094009782043735171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178509366729339854695823447 267764050094009782043735171)
      ·
        refine ⟨401646075141014673065602757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267764050094009782043735171 401646075141014673065602757)
        ·
          refine ⟨75308639088940251199800517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401646075141014673065602757 75308639088940251199800517)
          ·
            refine ⟨14120369829176297099962597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75308639088940251199800517 14120369829176297099962597)
            ·
              refine ⟨2647569342970555706242987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14120369829176297099962597 2647569342970555706242987)
              ·
                refine ⟨3971354014455833559364481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647569342970555706242987 3971354014455833559364481)
                ·
                  refine ⟨2978515510841875169523361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971354014455833559364481 2978515510841875169523361)
                  ·
                    refine ⟨2233886633131406377142521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2978515510841875169523361 2233886633131406377142521)
                    ·
                      refine ⟨1675414974848554782856891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233886633131406377142521 1675414974848554782856891)
                      ·
                        rfl

theorem cell23_3262859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 2, 2].length) (baseStart_3262859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262859 prefixEnd_3262859 := by exact prefixLift 3262859
  have htrace : WordTrace (prefixWord ++ tailWord_3262859) baseStart_3262859 baseEnd_3262859 := by
    simpa [prefixWord, tailWord_3262859, baseEnd_3262859] using wordTrace_append hprefix tailTrace_3262859
  have hstable : (prefixWord ++ tailWord_3262859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262859).length < 2 ^ (prefixWord ++ tailWord_3262859).sum := by decide
  have hdescent : baseEnd_3262859 < baseStart_3262859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262932 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3262932 : Nat := 118140960795 + 3262932 * 2 ^ 59
def prefixEnd_3262932 : Nat := 4983230072969 + 3 ^ 40 * 3262932 * 2
def baseEnd_3262932 : Nat := 1675452458936332997244055

theorem tailTrace_3262932 : CollatzResearch.WordTrace tailWord_3262932 prefixEnd_3262932 1675452458936332997244055 := by
  unfold tailWord_3262932
  simp only [CollatzResearch.WordTrace]
  refine ⟨59504453507481051632311525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79339271343308068843082033 59504453507481051632311525)
  ·
    refine ⟨11157085032652697181058411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59504453507481051632311525 11157085032652697181058411)
    ·
      refine ⟨16735627548979045771587617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11157085032652697181058411 16735627548979045771587617)
      ·
        refine ⟨12551720661734284328690713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16735627548979045771587617 12551720661734284328690713)
        ·
          refine ⟨9413790496300713246518035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12551720661734284328690713 9413790496300713246518035)
          ·
            refine ⟨14120685744451069869777053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413790496300713246518035 14120685744451069869777053)
            ·
              refine ⟨5295257154169151201166395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14120685744451069869777053 5295257154169151201166395)
              ·
                refine ⟨7942885731253726801749593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295257154169151201166395 7942885731253726801749593)
                ·
                  refine ⟨5957164298440295101312195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942885731253726801749593 5957164298440295101312195)
                  ·
                    refine ⟨8935746447660442651968293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957164298440295101312195 8935746447660442651968293)
                    ·
                      refine ⟨1675452458936332997244055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8935746447660442651968293 1675452458936332997244055)
                      ·
                        rfl

theorem cell23_3262932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3262932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262932 prefixEnd_3262932 := by exact prefixLift 3262932
  have htrace : WordTrace (prefixWord ++ tailWord_3262932) baseStart_3262932 baseEnd_3262932 := by
    simpa [prefixWord, tailWord_3262932, baseEnd_3262932] using wordTrace_append hprefix tailTrace_3262932
  have hstable : (prefixWord ++ tailWord_3262932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262932).length < 2 ^ (prefixWord ++ tailWord_3262932).sum := by decide
  have hdescent : baseEnd_3262932 < baseStart_3262932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262938 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_3262938 : Nat := 118140960795 + 3262938 * 2 ^ 59
def prefixEnd_3262938 : Nat := 4983230072969 + 3 ^ 40 * 3262938 * 2
def baseEnd_3262938 : Nat := 186161726646695552641003

theorem tailTrace_3262938 : CollatzResearch.WordTrace tailWord_3262938 prefixEnd_3262938 186161726646695552641003 := by
  unfold tailWord_3262938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752281463235091572335367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79339417235293577526227645 29752281463235091572335367)
  ·
    refine ⟨44628422194852637358503051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29752281463235091572335367 44628422194852637358503051)
    ·
      refine ⟨66942633292278956037754577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44628422194852637358503051 66942633292278956037754577)
      ·
        refine ⟨50206974969209217028315933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66942633292278956037754577 50206974969209217028315933)
        ·
          refine ⟨18827615613453456385618475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50206974969209217028315933 18827615613453456385618475)
          ·
            refine ⟨28241423420180184578427713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18827615613453456385618475 28241423420180184578427713)
            ·
              refine ⟨21181067565135138433820785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28241423420180184578427713 21181067565135138433820785)
              ·
                refine ⟨15885800673851353825365589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21181067565135138433820785 15885800673851353825365589)
                ·
                  refine ⟨186161726646695552641003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15885800673851353825365589 186161726646695552641003)
                  ·
                    rfl

theorem cell23_3262938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_3262938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262938 prefixEnd_3262938 := by exact prefixLift 3262938
  have htrace : WordTrace (prefixWord ++ tailWord_3262938) baseStart_3262938 baseEnd_3262938 := by
    simpa [prefixWord, tailWord_3262938, baseEnd_3262938] using wordTrace_append hprefix tailTrace_3262938
  have hstable : (prefixWord ++ tailWord_3262938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262938).length < 2 ^ (prefixWord ++ tailWord_3262938).sum := by decide
  have hdescent : baseEnd_3262938 < baseStart_3262938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3262975 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 5, 2]
def baseStart_3262975 : Nat := 118140960795 + 3262975 * 2 ^ 59
def prefixEnd_3262975 : Nat := 4983230072969 + 3 ^ 40 * 3262975 * 2
def baseEnd_3262975 : Nat := 1675474538604476329006357

theorem tailTrace_3262975 : CollatzResearch.WordTrace tailWord_3262975 prefixEnd_3262975 1675474538604476329006357 := by
  unfold tailWord_3262975
  simp only [CollatzResearch.WordTrace]
  refine ⟨119010475353806321608438379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79340316902537547738958919 119010475353806321608438379)
  ·
    refine ⟨178515713030709482412657569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119010475353806321608438379 178515713030709482412657569)
    ·
      refine ⟨133886784773032111809493177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178515713030709482412657569 133886784773032111809493177)
      ·
        refine ⟨100415088579774083857119883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133886784773032111809493177 100415088579774083857119883)
        ·
          refine ⟨150622632869661125785679825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100415088579774083857119883 150622632869661125785679825)
          ·
            refine ⟨112966974652245844339259869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150622632869661125785679825 112966974652245844339259869)
            ·
              refine ⟨42362615494592191627222451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112966974652245844339259869 42362615494592191627222451)
              ·
                refine ⟨63543923241888287440833677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42362615494592191627222451 63543923241888287440833677)
                ·
                  refine ⟨23828971215708107790312629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63543923241888287440833677 23828971215708107790312629)
                  ·
                    refine ⟨2233966051472635105341809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23828971215708107790312629 2233966051472635105341809)
                    ·
                      refine ⟨1675474538604476329006357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2233966051472635105341809 1675474538604476329006357)
                      ·
                        rfl

theorem cell23_3262975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_3262975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3262975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3262975 prefixEnd_3262975 := by exact prefixLift 3262975
  have htrace : WordTrace (prefixWord ++ tailWord_3262975) baseStart_3262975 baseEnd_3262975 := by
    simpa [prefixWord, tailWord_3262975, baseEnd_3262975] using wordTrace_append hprefix tailTrace_3262975
  have hstable : (prefixWord ++ tailWord_3262975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3262975).length < 2 ^ (prefixWord ++ tailWord_3262975).sum := by decide
  have hdescent : baseEnd_3262975 < baseStart_3262975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3262975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263016 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3263016 : Nat := 118140960795 + 3263016 * 2 ^ 59
def prefixEnd_3263016 : Nat := 4983230072969 + 3 ^ 40 * 3263016 * 2
def baseEnd_3263016 : Nat := 1675495591311310668593669

theorem tailTrace_3263016 : CollatzResearch.WordTrace tailWord_3263016 prefixEnd_3263016 1675495591311310668593669 := by
  unfold tailWord_3263016
  simp only [CollatzResearch.WordTrace]
  refine ⟨59505985373328892805340451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79341313831105190407120601 59505985373328892805340451)
  ·
    refine ⟨89258978059993339208010677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59505985373328892805340451 89258978059993339208010677)
    ·
      refine ⟨8368029193124375550751001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89258978059993339208010677 8368029193124375550751001)
      ·
        refine ⟨6276021894843281663063251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8368029193124375550751001 6276021894843281663063251)
        ·
          refine ⟨9414032842264922494594877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276021894843281663063251 9414032842264922494594877)
          ·
            refine ⟨3530262315849345935473079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9414032842264922494594877 3530262315849345935473079)
            ·
              refine ⟨5295393473774018903209619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530262315849345935473079 5295393473774018903209619)
              ·
                refine ⟨7943090210661028354814429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295393473774018903209619 7943090210661028354814429)
                ·
                  refine ⟨2978658828997885633055411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7943090210661028354814429 2978658828997885633055411)
                  ·
                    refine ⟨4467988243496828449583117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978658828997885633055411 4467988243496828449583117)
                    ·
                      refine ⟨1675495591311310668593669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4467988243496828449583117 1675495591311310668593669)
                      ·
                        rfl

theorem cell23_3263016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3263016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263016 prefixEnd_3263016 := by exact prefixLift 3263016
  have htrace : WordTrace (prefixWord ++ tailWord_3263016) baseStart_3263016 baseEnd_3263016 := by
    simpa [prefixWord, tailWord_3263016, baseEnd_3263016] using wordTrace_append hprefix tailTrace_3263016
  have hstable : (prefixWord ++ tailWord_3263016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263016).length < 2 ^ (prefixWord ++ tailWord_3263016).sum := by decide
  have hdescent : baseEnd_3263016 < baseStart_3263016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263025 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3263025 : Nat := 118140960795 + 3263025 * 2 ^ 59
def prefixEnd_3263025 : Nat := 4983230072969 + 3 ^ 40 * 3263025 * 2
def baseEnd_3263025 : Nat := 1675500212637201133381127

theorem tailTrace_3263025 : CollatzResearch.WordTrace tailWord_3263025 prefixEnd_3263025 1675500212637201133381127 := by
  unfold tailWord_3263025
  simp only [CollatzResearch.WordTrace]
  refine ⟨119012299003625180147758529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79341532669083453431839019 119012299003625180147758529)
  ·
    refine ⟨89259224252718885110818897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119012299003625180147758529 89259224252718885110818897)
    ·
      refine ⟨66944418189539163833114173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89259224252718885110818897 66944418189539163833114173)
      ·
        refine ⟨25104156821077186437417815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66944418189539163833114173 25104156821077186437417815)
        ·
          refine ⟨37656235231615779656126723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25104156821077186437417815 37656235231615779656126723)
          ·
            refine ⟨56484352847423669484190085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37656235231615779656126723 56484352847423669484190085)
            ·
              refine ⟨10590816158891938028285641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56484352847423669484190085 10590816158891938028285641)
              ·
                refine ⟨7943112119168953521214231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10590816158891938028285641 7943112119168953521214231)
                ·
                  refine ⟨11914668178753430281821347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943112119168953521214231 11914668178753430281821347)
                  ·
                    refine ⟨17872002268130145422732021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11914668178753430281821347 17872002268130145422732021)
                    ·
                      refine ⟨1675500212637201133381127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17872002268130145422732021 1675500212637201133381127)
                      ·
                        rfl

theorem cell23_3263025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3263025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263025 prefixEnd_3263025 := by exact prefixLift 3263025
  have htrace : WordTrace (prefixWord ++ tailWord_3263025) baseStart_3263025 baseEnd_3263025 := by
    simpa [prefixWord, tailWord_3263025, baseEnd_3263025] using wordTrace_append hprefix tailTrace_3263025
  have hstable : (prefixWord ++ tailWord_3263025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263025).length < 2 ^ (prefixWord ++ tailWord_3263025).sum := by decide
  have hdescent : baseEnd_3263025 < baseStart_3263025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263032 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_3263032 : Nat := 118140960795 + 3263032 * 2 ^ 59
def prefixEnd_3263032 : Nat := 4983230072969 + 3 ^ 40 * 3263032 * 2
def baseEnd_3263032 : Nat := 558501269000594201997865

theorem tailTrace_3263032 : CollatzResearch.WordTrace tailWord_3263032 prefixEnd_3263032 558501269000594201997865 := by
  unfold tailWord_3263032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59506277157299910171631675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79341702876399880228842233 59506277157299910171631675)
  ·
    refine ⟨89259415735949865257447513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59506277157299910171631675 89259415735949865257447513)
    ·
      refine ⟨66944561801962398943085635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89259415735949865257447513 66944561801962398943085635)
      ·
        refine ⟨100416842702943598414628453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66944561801962398943085635 100416842702943598414628453)
        ·
          refine ⟨18828158006801924702742835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100416842702943598414628453 18828158006801924702742835)
          ·
            refine ⟨28242237010202887054114253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18828158006801924702742835 28242237010202887054114253)
            ·
              refine ⟨10590838878826082645292845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28242237010202887054114253 10590838878826082645292845)
              ·
                refine ⟨3971564579559780991984817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10590838878826082645292845 3971564579559780991984817)
                ·
                  refine ⟨2978673434669835743988613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971564579559780991984817 2978673434669835743988613)
                  ·
                    refine ⟨558501269000594201997865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978673434669835743988613 558501269000594201997865)
                    ·
                      rfl

theorem cell23_3263032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_3263032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263032 prefixEnd_3263032 := by exact prefixLift 3263032
  have htrace : WordTrace (prefixWord ++ tailWord_3263032) baseStart_3263032 baseEnd_3263032 := by
    simpa [prefixWord, tailWord_3263032, baseEnd_3263032] using wordTrace_append hprefix tailTrace_3263032
  have hstable : (prefixWord ++ tailWord_3263032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263032).length < 2 ^ (prefixWord ++ tailWord_3263032).sum := by decide
  have hdescent : baseEnd_3263032 < baseStart_3263032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263055 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_3263055 : Nat := 118140960795 + 3263055 * 2 ^ 59
def prefixEnd_3263055 : Nat := 4983230072969 + 3 ^ 40 * 3263055 * 2
def baseEnd_3263055 : Nat := 1675515617056836016005989

theorem tailTrace_3263055 : CollatzResearch.WordTrace tailWord_3263055 prefixEnd_3263055 1675515617056836016005989 := by
  unfold tailWord_3263055
  simp only [CollatzResearch.WordTrace]
  refine ⟨119013393193516495271350619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79342262129010996847567079 119013393193516495271350619)
  ·
    refine ⟨178520089790274742907025929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119013393193516495271350619 178520089790274742907025929)
    ·
      refine ⟨133890067342706057180269447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178520089790274742907025929 133890067342706057180269447)
      ·
        refine ⟨200835101014059085770404171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133890067342706057180269447 200835101014059085770404171)
        ·
          refine ⟨301252651521088628655606257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200835101014059085770404171 301252651521088628655606257)
          ·
            refine ⟨225939488640816471491704693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301252651521088628655606257 225939488640816471491704693)
            ·
              refine ⟨21181827060076544202347315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225939488640816471491704693 21181827060076544202347315)
              ·
                refine ⟨31772740590114816303520973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21181827060076544202347315 31772740590114816303520973)
                ·
                  refine ⟨11914777721293056113820365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31772740590114816303520973 11914777721293056113820365)
                  ·
                    refine ⟨4468041645484896042682637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11914777721293056113820365 4468041645484896042682637)
                    ·
                      refine ⟨1675515617056836016005989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468041645484896042682637 1675515617056836016005989)
                      ·
                        rfl

theorem cell23_3263055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_3263055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263055 prefixEnd_3263055 := by exact prefixLift 3263055
  have htrace : WordTrace (prefixWord ++ tailWord_3263055) baseStart_3263055 baseEnd_3263055 := by
    simpa [prefixWord, tailWord_3263055, baseEnd_3263055] using wordTrace_append hprefix tailTrace_3263055
  have hstable : (prefixWord ++ tailWord_3263055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263055).length < 2 ^ (prefixWord ++ tailWord_3263055).sum := by decide
  have hdescent : baseEnd_3263055 < baseStart_3263055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263072 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3]
def baseStart_3263072 : Nat := 118140960795 + 3263072 * 2 ^ 59
def prefixEnd_3263072 : Nat := 4983230072969 + 3 ^ 40 * 3263072 * 2
def baseEnd_3263072 : Nat := 1675524346227962449493411

theorem tailTrace_3263072 : CollatzResearch.WordTrace tailWord_3263072 prefixEnd_3263072 1675524346227962449493411 := by
  unfold tailWord_3263072
  simp only [CollatzResearch.WordTrace]
  refine ⟨59507006617227453587359735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79342675489636604783146313 59507006617227453587359735)
  ·
    refine ⟨89260509925841180381039603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59507006617227453587359735 89260509925841180381039603)
    ·
      refine ⟨133890764888761770571559405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89260509925841180381039603 133890764888761770571559405)
      ·
        refine ⟨50209036833285663964334777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133890764888761770571559405 50209036833285663964334777)
        ·
          refine ⟨37656777624964247973251083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50209036833285663964334777 37656777624964247973251083)
          ·
            refine ⟨56485166437446371959876625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37656777624964247973251083 56485166437446371959876625)
            ·
              refine ⟨42363874828084778969907469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56485166437446371959876625 42363874828084778969907469)
              ·
                refine ⟨15886453060531792113715301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42363874828084778969907469 15886453060531792113715301)
                ·
                  refine ⟨2978709948849711021321619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15886453060531792113715301 2978709948849711021321619)
                  ·
                    refine ⟨4468064923274566531982429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2978709948849711021321619 4468064923274566531982429)
                    ·
                      refine ⟨1675524346227962449493411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468064923274566531982429 1675524346227962449493411)
                      ·
                        rfl

theorem cell23_3263072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_3263072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263072 prefixEnd_3263072 := by exact prefixLift 3263072
  have htrace : WordTrace (prefixWord ++ tailWord_3263072) baseStart_3263072 baseEnd_3263072 := by
    simpa [prefixWord, tailWord_3263072, baseEnd_3263072] using wordTrace_append hprefix tailTrace_3263072
  have hstable : (prefixWord ++ tailWord_3263072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263072).length < 2 ^ (prefixWord ++ tailWord_3263072).sum := by decide
  have hdescent : baseEnd_3263072 < baseStart_3263072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263073 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_3263073 : Nat := 118140960795 + 3263073 * 2 ^ 59
def prefixEnd_3263073 : Nat := 4983230072969 + 3 ^ 40 * 3263073 * 2
def baseEnd_3263073 : Nat := 1675524859708616945580907

theorem tailTrace_3263073 : CollatzResearch.WordTrace tailWord_3263073 prefixEnd_3263073 1675524859708616945580907 := by
  unfold tailWord_3263073
  simp only [CollatzResearch.WordTrace]
  refine ⟨119014049707451284345505873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79342699804967522897003915 119014049707451284345505873)
  ·
    refine ⟨89260537280588463259129405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119014049707451284345505873 89260537280588463259129405)
    ·
      refine ⟨33472701480220673722173527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89260537280588463259129405 33472701480220673722173527)
      ·
        refine ⟨50209052220331010583260291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33472701480220673722173527 50209052220331010583260291)
        ·
          refine ⟨75313578330496515874890437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50209052220331010583260291 75313578330496515874890437)
          ·
            refine ⟨14121295936968096726541957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75313578330496515874890437 14121295936968096726541957)
            ·
              refine ⟨2647742988181518136226617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14121295936968096726541957 2647742988181518136226617)
              ·
                refine ⟨1985807241136138602169963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647742988181518136226617 1985807241136138602169963)
                ·
                  refine ⟨2978710861704207903254945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985807241136138602169963 2978710861704207903254945)
                  ·
                    refine ⟨2234033146278155927441209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2978710861704207903254945 2234033146278155927441209)
                    ·
                      refine ⟨1675524859708616945580907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234033146278155927441209 1675524859708616945580907)
                      ·
                        rfl

theorem cell23_3263073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_3263073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263073 prefixEnd_3263073 := by exact prefixLift 3263073
  have htrace : WordTrace (prefixWord ++ tailWord_3263073) baseStart_3263073 baseEnd_3263073 := by
    simpa [prefixWord, tailWord_3263073, baseEnd_3263073] using wordTrace_append hprefix tailTrace_3263073
  have hstable : (prefixWord ++ tailWord_3263073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263073).length < 2 ^ (prefixWord ++ tailWord_3263073).sum := by decide
  have hdescent : baseEnd_3263073 < baseStart_3263073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263105 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3263105 : Nat := 118140960795 + 3263105 * 2 ^ 59
def prefixEnd_3263105 : Nat := 4983230072969 + 3 ^ 40 * 3263105 * 2
def baseEnd_3263105 : Nat := 558513763696520273460253

theorem tailTrace_3263105 : CollatzResearch.WordTrace tailWord_3263105 prefixEnd_3263105 558513763696520273460253 := by
  unfold tailWord_3263105
  simp only [CollatzResearch.WordTrace]
  refine ⟨119015216843335353810670769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79343477895556902540447179 119015216843335353810670769)
  ·
    refine ⟨89261412632501515358003077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119015216843335353810670769 89261412632501515358003077)
    ·
      refine ⟨16736514868594034129625577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89261412632501515358003077 16736514868594034129625577)
      ·
        refine ⟨12552386151445525597219183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16736514868594034129625577 12552386151445525597219183)
        ·
          refine ⟨18828579227168288395828775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552386151445525597219183 18828579227168288395828775)
          ·
            refine ⟨28242868840752432593743163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18828579227168288395828775 28242868840752432593743163)
            ·
              refine ⟨42364303261128648890614745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28242868840752432593743163 42364303261128648890614745)
              ·
                refine ⟨31773227445846486667961059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42364303261128648890614745 31773227445846486667961059)
                ·
                  refine ⟨47659841168769730001941589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31773227445846486667961059 47659841168769730001941589)
                  ·
                    refine ⟨558513763696520273460253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47659841168769730001941589 558513763696520273460253)
                    ·
                      rfl

theorem cell23_3263105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3263105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263105 prefixEnd_3263105 := by exact prefixLift 3263105
  have htrace : WordTrace (prefixWord ++ tailWord_3263105) baseStart_3263105 baseEnd_3263105 := by
    simpa [prefixWord, tailWord_3263105, baseEnd_3263105] using wordTrace_append hprefix tailTrace_3263105
  have hstable : (prefixWord ++ tailWord_3263105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263105).length < 2 ^ (prefixWord ++ tailWord_3263105).sum := by decide
  have hdescent : baseEnd_3263105 < baseStart_3263105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263115 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3]
def baseStart_3263115 : Nat := 118140960795 + 3263115 * 2 ^ 59
def prefixEnd_3263115 : Nat := 4983230072969 + 3 ^ 40 * 3263115 * 2
def baseEnd_3263115 : Nat := 1675546425896105781255713

theorem tailTrace_3263115 : CollatzResearch.WordTrace tailWord_3263115 prefixEnd_3263115 1675546425896105781255713 := by
  unfold tailWord_3263115
  simp only [CollatzResearch.WordTrace]
  refine ⟨119015581573299125518534799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79343721048866083679023199 119015581573299125518534799)
  ·
    refine ⟨178523372359948688277802199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119015581573299125518534799 178523372359948688277802199)
    ·
      refine ⟨267785058539923032416703299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178523372359948688277802199 267785058539923032416703299)
      ·
        refine ⟨401677587809884548625054949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267785058539923032416703299 401677587809884548625054949)
        ·
          refine ⟨75314547714353352867197803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401677587809884548625054949 75314547714353352867197803)
          ·
            refine ⟨112971821571530029300796705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75314547714353352867197803 112971821571530029300796705)
            ·
              refine ⟨84728866178647521975597529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112971821571530029300796705 84728866178647521975597529)
              ·
                refine ⟨63546649633985641481698147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84728866178647521975597529 63546649633985641481698147)
                ·
                  refine ⟨95319974450978462222547221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63546649633985641481698147 95319974450978462222547221)
                  ·
                    refine ⟨4468123802389615416681901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95319974450978462222547221 4468123802389615416681901)
                    ·
                      refine ⟨1675546425896105781255713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468123802389615416681901 1675546425896105781255713)
                      ·
                        rfl

theorem cell23_3263115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3].length) (baseStart_3263115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263115 prefixEnd_3263115 := by exact prefixLift 3263115
  have htrace : WordTrace (prefixWord ++ tailWord_3263115) baseStart_3263115 baseEnd_3263115 := by
    simpa [prefixWord, tailWord_3263115, baseEnd_3263115] using wordTrace_append hprefix tailTrace_3263115
  have hstable : (prefixWord ++ tailWord_3263115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263115).length < 2 ^ (prefixWord ++ tailWord_3263115).sum := by decide
  have hdescent : baseEnd_3263115 < baseStart_3263115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263122 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3263122 : Nat := 118140960795 + 3263122 * 2 ^ 59
def prefixEnd_3263122 : Nat := 4983230072969 + 3 ^ 40 * 3263122 * 2
def baseEnd_3263122 : Nat := 558516673420229084622727

theorem tailTrace_3263122 : CollatzResearch.WordTrace tailWord_3263122 prefixEnd_3263122 558516673420229084622727 := by
  unfold tailWord_3263122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29753959221068441428509905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79343891256182510476026413 29753959221068441428509905)
  ·
    refine ⟨22315469415801331071382429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29753959221068441428509905 22315469415801331071382429)
    ·
      refine ⟨8368301030925499151768411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22315469415801331071382429 8368301030925499151768411)
      ·
        refine ⟨12552451546388248727652617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368301030925499151768411 12552451546388248727652617)
        ·
          refine ⟨9414338659791186545739463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12552451546388248727652617 9414338659791186545739463)
          ·
            refine ⟨14121507989686779818609195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9414338659791186545739463 14121507989686779818609195)
            ·
              refine ⟨21182261984530169727913793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14121507989686779818609195 21182261984530169727913793)
              ·
                refine ⟨15886696488397627295935345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21182261984530169727913793 15886696488397627295935345)
                ·
                  refine ⟨11915022366298220471951509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15886696488397627295935345 11915022366298220471951509)
                  ·
                    refine ⟨558516673420229084622727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11915022366298220471951509 558516673420229084622727)
                    ·
                      rfl

theorem cell23_3263122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3263122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263122 prefixEnd_3263122 := by exact prefixLift 3263122
  have htrace : WordTrace (prefixWord ++ tailWord_3263122) baseStart_3263122 baseEnd_3263122 := by
    simpa [prefixWord, tailWord_3263122, baseEnd_3263122] using wordTrace_append hprefix tailTrace_3263122
  have hstable : (prefixWord ++ tailWord_3263122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263122).length < 2 ^ (prefixWord ++ tailWord_3263122).sum := by decide
  have hdescent : baseEnd_3263122 < baseStart_3263122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263129 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 4, 2, 2]
def baseStart_3263129 : Nat := 118140960795 + 3263129 * 2 ^ 59
def prefixEnd_3263129 : Nat := 4983230072969 + 3 ^ 40 * 3263129 * 2
def baseEnd_3263129 : Nat := 1675553614625268726480649

theorem tailTrace_3263129 : CollatzResearch.WordTrace tailWord_3263129 prefixEnd_3263129 1675553614625268726480649 := by
  unfold tailWord_3263129
  simp only [CollatzResearch.WordTrace]
  refine ⟨119016092195248405909544441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79344061463498937273029627 119016092195248405909544441)
  ·
    refine ⟨89262069146436304432158331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119016092195248405909544441 89262069146436304432158331)
    ·
      refine ⟨133893103719654456648237497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89262069146436304432158331 133893103719654456648237497)
      ·
        refine ⟨100419827789740842486178123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133893103719654456648237497 100419827789740842486178123)
        ·
          refine ⟨150629741684611263729267185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100419827789740842486178123 150629741684611263729267185)
          ·
            refine ⟨112972306263458447796950389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150629741684611263729267185 112972306263458447796950389)
            ·
              refine ⟨10591153712199229480964099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112972306263458447796950389 10591153712199229480964099)
              ·
                refine ⟨15886730568298844221446149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591153712199229480964099 15886730568298844221446149)
                ·
                  refine ⟨2978761981556033291521153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15886730568298844221446149 2978761981556033291521153)
                  ·
                    refine ⟨2234071486167024968640865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2978761981556033291521153 2234071486167024968640865)
                    ·
                      refine ⟨1675553614625268726480649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234071486167024968640865 1675553614625268726480649)
                      ·
                        rfl

theorem cell23_3263129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_3263129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263129 prefixEnd_3263129 := by exact prefixLift 3263129
  have htrace : WordTrace (prefixWord ++ tailWord_3263129) baseStart_3263129 baseEnd_3263129 := by
    simpa [prefixWord, tailWord_3263129, baseEnd_3263129] using wordTrace_append hprefix tailTrace_3263129
  have hstable : (prefixWord ++ tailWord_3263129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263129).length < 2 ^ (prefixWord ++ tailWord_3263129).sum := by decide
  have hdescent : baseEnd_3263129 < baseStart_3263129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263182 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3263182 : Nat := 118140960795 + 3263182 * 2 ^ 59
def prefixEnd_3263182 : Nat := 4983230072969 + 3 ^ 40 * 3263182 * 2
def baseEnd_3263182 : Nat := 558526943033319006372635

theorem tailTrace_3263182 : CollatzResearch.WordTrace tailWord_3263182 prefixEnd_3263182 558526943033319006372635 := by
  unfold tailWord_3263182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877253158007049495152975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79345350176037597307482533 14877253158007049495152975)
  ·
    refine ⟨22315879737010574242729463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877253158007049495152975 22315879737010574242729463)
    ·
      refine ⟨33473819605515861364094195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22315879737010574242729463 33473819605515861364094195)
      ·
        refine ⟨50210729408273792046141293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33473819605515861364094195 50210729408273792046141293)
        ·
          refine ⟨18829023528102672017302985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50210729408273792046141293 18829023528102672017302985)
          ·
            refine ⟨14121767646077004012977239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18829023528102672017302985 14121767646077004012977239)
            ·
              refine ⟨21182651469115506019465859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14121767646077004012977239 21182651469115506019465859)
              ·
                refine ⟨31773977203673259029198789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21182651469115506019465859 31773977203673259029198789)
                ·
                  refine ⟨5957620725688736067974773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31773977203673259029198789 5957620725688736067974773)
                  ·
                    refine ⟨558526943033319006372635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5957620725688736067974773 558526943033319006372635)
                    ·
                      rfl

theorem cell23_3263182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3263182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263182 prefixEnd_3263182 := by exact prefixLift 3263182
  have htrace : WordTrace (prefixWord ++ tailWord_3263182) baseStart_3263182 baseEnd_3263182 := by
    simpa [prefixWord, tailWord_3263182, baseEnd_3263182] using wordTrace_append hprefix tailTrace_3263182
  have hstable : (prefixWord ++ tailWord_3263182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263182).length < 2 ^ (prefixWord ++ tailWord_3263182).sum := by decide
  have hdescent : baseEnd_3263182 < baseStart_3263182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263186 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_3263186 : Nat := 118140960795 + 3263186 * 2 ^ 59
def prefixEnd_3263186 : Nat := 4983230072969 + 3 ^ 40 * 3263186 * 2
def baseEnd_3263186 : Nat := 186175875891397222607543

theorem tailTrace_3263186 : CollatzResearch.WordTrace tailWord_3263186 prefixEnd_3263186 186175875891397222607543 := by
  unfold tailWord_3263186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754542789010476161092353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79345447437361269762912941 29754542789010476161092353)
  ·
    refine ⟨22315907091757857120819265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29754542789010476161092353 22315907091757857120819265)
    ·
      refine ⟨16736930318818392840614449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22315907091757857120819265 16736930318818392840614449)
      ·
        refine ⟨12552697739113794630460837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16736930318818392840614449 12552697739113794630460837)
        ·
          refine ⟨2353630826083836493211407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12552697739113794630460837 2353630826083836493211407)
          ·
            refine ⟨3530446239125754739817111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353630826083836493211407 3530446239125754739817111)
            ·
              refine ⟨5295669358688632109725667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530446239125754739817111 5295669358688632109725667)
              ·
                refine ⟨7943504038032948164588501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295669358688632109725667 7943504038032948164588501)
                ·
                  refine ⟨186175875891397222607543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7943504038032948164588501 186175875891397222607543)
                  ·
                    rfl

theorem cell23_3263186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_3263186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263186 prefixEnd_3263186 := by exact prefixLift 3263186
  have htrace : WordTrace (prefixWord ++ tailWord_3263186) baseStart_3263186 baseEnd_3263186 := by
    simpa [prefixWord, tailWord_3263186, baseEnd_3263186] using wordTrace_append hprefix tailTrace_3263186
  have hstable : (prefixWord ++ tailWord_3263186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263186).length < 2 ^ (prefixWord ++ tailWord_3263186).sum := by decide
  have hdescent : baseEnd_3263186 < baseStart_3263186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263192 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3263192 : Nat := 118140960795 + 3263192 * 2 ^ 59
def prefixEnd_3263192 : Nat := 4983230072969 + 3 ^ 40 * 3263192 * 2
def baseEnd_3263192 : Nat := 1675585963906501979992859

theorem tailTrace_3263192 : CollatzResearch.WordTrace tailWord_3263192 prefixEnd_3263192 1675585963906501979992859 := by
  unfold tailWord_3263192
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509194997010083834543915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79345593329346778446058553 59509194997010083834543915)
  ·
    refine ⟨89263792495515125751815873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59509194997010083834543915 89263792495515125751815873)
    ·
      refine ⟨66947844371636344313861905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89263792495515125751815873 66947844371636344313861905)
      ·
        refine ⟨50210883278727258235396429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66947844371636344313861905 50210883278727258235396429)
        ·
          refine ⟨18829081229522721838273661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50210883278727258235396429 18829081229522721838273661)
          ·
            refine ⟨7060905461071020689352623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18829081229522721838273661 7060905461071020689352623)
            ·
              refine ⟨10591358191606531034028935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060905461071020689352623 10591358191606531034028935)
              ·
                refine ⟨15887037287409796551043403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591358191606531034028935 15887037287409796551043403)
                ·
                  refine ⟨23830555931114694826565105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15887037287409796551043403 23830555931114694826565105)
                  ·
                    refine ⟨17872916948336021119923829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23830555931114694826565105 17872916948336021119923829)
                    ·
                      refine ⟨1675585963906501979992859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17872916948336021119923829 1675585963906501979992859)
                      ·
                        rfl

theorem cell23_3263192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3263192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263192 prefixEnd_3263192 := by exact prefixLift 3263192
  have htrace : WordTrace (prefixWord ++ tailWord_3263192) baseStart_3263192 baseEnd_3263192 := by
    simpa [prefixWord, tailWord_3263192, baseEnd_3263192] using wordTrace_append hprefix tailTrace_3263192
  have hstable : (prefixWord ++ tailWord_3263192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263192).length < 2 ^ (prefixWord ++ tailWord_3263192).sum := by decide
  have hdescent : baseEnd_3263192 < baseStart_3263192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263212 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_3263212 : Nat := 118140960795 + 3263212 * 2 ^ 59
def prefixEnd_3263212 : Nat := 4983230072969 + 3 ^ 40 * 3263212 * 2
def baseEnd_3263212 : Nat := 558532077839863967247589

theorem tailTrace_3263212 : CollatzResearch.WordTrace tailWord_3263212 prefixEnd_3263212 558532077839863967247589 := by
  unfold tailWord_3263212
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509559726973855542407945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79346079635965140723210593 59509559726973855542407945)
  ·
    refine ⟨44632169795230391656805959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59509559726973855542407945 44632169795230391656805959)
    ·
      refine ⟨66948254692845587485208939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44632169795230391656805959 66948254692845587485208939)
      ·
        refine ⟨100422382039268381227813409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66948254692845587485208939 100422382039268381227813409)
        ·
          refine ⟨75316786529451285920860057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100422382039268381227813409 75316786529451285920860057)
          ·
            refine ⟨56487589897088464440645043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75316786529451285920860057 56487589897088464440645043)
            ·
              refine ⟨84731384845632696660967565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56487589897088464440645043 84731384845632696660967565)
              ·
                refine ⟨31774269317112261247862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84731384845632696660967565 31774269317112261247862837)
                ·
                  refine ⟨2978837748479274491987141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31774269317112261247862837 2978837748479274491987141)
                  ·
                    refine ⟨558532077839863967247589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978837748479274491987141 558532077839863967247589)
                    ·
                      rfl

theorem cell23_3263212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_3263212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263212 prefixEnd_3263212 := by exact prefixLift 3263212
  have htrace : WordTrace (prefixWord ++ tailWord_3263212) baseStart_3263212 baseEnd_3263212 := by
    simpa [prefixWord, tailWord_3263212, baseEnd_3263212] using wordTrace_append hprefix tailTrace_3263212
  have hstable : (prefixWord ++ tailWord_3263212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263212).length < 2 ^ (prefixWord ++ tailWord_3263212).sum := by decide
  have hdescent : baseEnd_3263212 < baseStart_3263212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263225 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 10]
def baseStart_3263225 : Nat := 118140960795 + 3263225 * 2 ^ 59
def prefixEnd_3263225 : Nat := 4983230072969 + 3 ^ 40 * 3263225 * 2
def baseEnd_3263225 : Nat := 186178100974233372320023

theorem tailTrace_3263225 : CollatzResearch.WordTrace tailWord_3263225 prefixEnd_3263225 186178100974233372320023 := by
  unfold tailWord_3263225
  simp only [CollatzResearch.WordTrace]
  refine ⟨119019593602900614305039129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79346395735267076203359419 119019593602900614305039129)
  ·
    refine ⟨89264695202175460728779347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119019593602900614305039129 89264695202175460728779347)
    ·
      refine ⟨133897042803263191093169021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89264695202175460728779347 133897042803263191093169021)
      ·
        refine ⟨50211391051223696659938383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133897042803263191093169021 50211391051223696659938383)
        ·
          refine ⟨75317086576835544989907575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50211391051223696659938383 75317086576835544989907575)
          ·
            refine ⟨112975629865253317484861363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75317086576835544989907575 112975629865253317484861363)
            ·
              refine ⟨169463444797879976227292045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112975629865253317484861363 169463444797879976227292045)
              ·
                refine ⟨63548791799204991085234517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169463444797879976227292045 63548791799204991085234517)
                ·
                  refine ⟨186178100974233372320023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63548791799204991085234517 186178100974233372320023)
                  ·
                    rfl

theorem cell23_3263225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_3263225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263225 prefixEnd_3263225 := by exact prefixLift 3263225
  have htrace : WordTrace (prefixWord ++ tailWord_3263225) baseStart_3263225 baseEnd_3263225 := by
    simpa [prefixWord, tailWord_3263225, baseEnd_3263225] using wordTrace_append hprefix tailTrace_3263225
  have hstable : (prefixWord ++ tailWord_3263225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263225).length < 2 ^ (prefixWord ++ tailWord_3263225).sum := by decide
  have hdescent : baseEnd_3263225 < baseStart_3263225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263293 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 6]
def baseStart_3263293 : Nat := 118140960795 + 3263293 * 2 ^ 59
def prefixEnd_3263293 : Nat := 4983230072969 + 3 ^ 40 * 3263293 * 2
def baseEnd_3263293 : Nat := 186181980605845120536655

theorem tailTrace_3263293 : CollatzResearch.WordTrace tailWord_3263293 prefixEnd_3263293 186181980605845120536655 := by
  unfold tailWord_3263293
  simp only [CollatzResearch.WordTrace]
  refine ⟨119022073766654261918514533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79348049177769507945676355 119022073766654261918514533)
  ·
    refine ⟨22316638831247674109721475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119022073766654261918514533 22316638831247674109721475)
    ·
      refine ⟨33474958246871511164582213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22316638831247674109721475 33474958246871511164582213)
      ·
        refine ⟨6276554671288408343359165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33474958246871511164582213 6276554671288408343359165)
        ·
          refine ⟨2353708001733153128759687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6276554671288408343359165 2353708001733153128759687)
          ·
            refine ⟨3530562002599729693139531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353708001733153128759687 3530562002599729693139531)
            ·
              refine ⟨5295843003899594539709297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530562002599729693139531 5295843003899594539709297)
              ·
                refine ⟨3971882252924695904781973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295843003899594539709297 3971882252924695904781973)
                ·
                  refine ⟨186181980605845120536655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3971882252924695904781973 186181980605845120536655)
                  ·
                    rfl

theorem cell23_3263293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_3263293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263293 prefixEnd_3263293 := by exact prefixLift 3263293
  have htrace : WordTrace (prefixWord ++ tailWord_3263293) baseStart_3263293 baseEnd_3263293 := by
    simpa [prefixWord, tailWord_3263293, baseEnd_3263293] using wordTrace_append hprefix tailTrace_3263293
  have hstable : (prefixWord ++ tailWord_3263293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263293).length < 2 ^ (prefixWord ++ tailWord_3263293).sum := by decide
  have hdescent : baseEnd_3263293 < baseStart_3263293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263312 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_3263312 : Nat := 118140960795 + 3263312 * 2 ^ 59
def prefixEnd_3263312 : Nat := 4983230072969 + 3 ^ 40 * 3263312 * 2
def baseEnd_3263312 : Nat := 1675647581585041510492307

theorem tailTrace_3263312 : CollatzResearch.WordTrace tailWord_3263312 prefixEnd_3263312 1675647581585041510492307 := by
  unfold tailWord_3263312
  simp only [CollatzResearch.WordTrace]
  refine ⟨59511383376792714081728095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79348511169056952108970793 59511383376792714081728095)
  ·
    refine ⟨89267075065189071122592143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59511383376792714081728095 89267075065189071122592143)
    ·
      refine ⟨133900612597783606683888215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89267075065189071122592143 133900612597783606683888215)
      ·
        refine ⟨200850918896675410025832323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133900612597783606683888215 200850918896675410025832323)
        ·
          refine ⟨301276378345013115038748485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200850918896675410025832323 301276378345013115038748485)
          ·
            refine ⟨56489320939689959069765341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301276378345013115038748485 56489320939689959069765341)
            ·
              refine ⟨21183495352383734651162003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56489320939689959069765341 21183495352383734651162003)
              ·
                refine ⟨31775243028575601976743005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21183495352383734651162003 31775243028575601976743005)
                ·
                  refine ⟨11915716135715850741278627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31775243028575601976743005 11915716135715850741278627)
                  ·
                    refine ⟨17873574203573776111917941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11915716135715850741278627 17873574203573776111917941)
                    ·
                      refine ⟨1675647581585041510492307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17873574203573776111917941 1675647581585041510492307)
                      ·
                        rfl

theorem cell23_3263312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_3263312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263312 prefixEnd_3263312 := by exact prefixLift 3263312
  have htrace : WordTrace (prefixWord ++ tailWord_3263312) baseStart_3263312 baseEnd_3263312 := by
    simpa [prefixWord, tailWord_3263312, baseEnd_3263312] using wordTrace_append hprefix tailTrace_3263312
  have hstable : (prefixWord ++ tailWord_3263312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263312).length < 2 ^ (prefixWord ++ tailWord_3263312).sum := by decide
  have hdescent : baseEnd_3263312 < baseStart_3263312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263319 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 1, 6]
def baseStart_3263319 : Nat := 118140960795 + 3263319 * 2 ^ 59
def prefixEnd_3263319 : Nat := 4983230072969 + 3 ^ 40 * 3263319 * 2
def baseEnd_3263319 : Nat := 558550391983207661034925

theorem tailTrace_3263319 : CollatzResearch.WordTrace tailWord_3263319 prefixEnd_3263319 558550391983207661034925 := by
  unfold tailWord_3263319
  simp only [CollatzResearch.WordTrace]
  refine ⟨119023022064560068358961011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79348681376373378905974007 119023022064560068358961011)
  ·
    refine ⟨178534533096840102538441517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119023022064560068358961011 178534533096840102538441517)
    ·
      refine ⟨66950449911315038451915569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178534533096840102538441517 66950449911315038451915569)
      ·
        refine ⟨50212837433486278838936677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66950449911315038451915569 50212837433486278838936677)
        ·
          refine ⟨9414907018778677282300627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50212837433486278838936677 9414907018778677282300627)
          ·
            refine ⟨14122360528168015923450941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9414907018778677282300627 14122360528168015923450941)
            ·
              refine ⟨5295885198063005971294103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14122360528168015923450941 5295885198063005971294103)
              ·
                refine ⟨7943827797094508956941155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295885198063005971294103 7943827797094508956941155)
                ·
                  refine ⟨11915741695641763435411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943827797094508956941155 11915741695641763435411733)
                  ·
                    refine ⟨558550391983207661034925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11915741695641763435411733 558550391983207661034925)
                    ·
                      rfl

theorem cell23_3263319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_3263319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263319 prefixEnd_3263319 := by exact prefixLift 3263319
  have htrace : WordTrace (prefixWord ++ tailWord_3263319) baseStart_3263319 baseEnd_3263319 := by
    simpa [prefixWord, tailWord_3263319, baseEnd_3263319] using wordTrace_append hprefix tailTrace_3263319
  have hstable : (prefixWord ++ tailWord_3263319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263319).length < 2 ^ (prefixWord ++ tailWord_3263319).sum := by decide
  have hdescent : baseEnd_3263319 < baseStart_3263319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263346 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3263346 : Nat := 118140960795 + 3263346 * 2 ^ 59
def prefixEnd_3263346 : Nat := 4983230072969 + 3 ^ 40 * 3263346 * 2
def baseEnd_3263346 : Nat := 1675665039927294377467151

theorem tailTrace_3263346 : CollatzResearch.WordTrace tailWord_3263346 prefixEnd_3263346 1675665039927294377467151 := by
  unfold tailWord_3263346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756001708865562992548473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79349337890308167980129261 29756001708865562992548473)
  ·
    refine ⟨22317001281649172244411355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29756001708865562992548473 22317001281649172244411355)
    ·
      refine ⟨33475501922473758366617033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22317001281649172244411355 33475501922473758366617033)
      ·
        refine ⟨25106626441855318774962775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33475501922473758366617033 25106626441855318774962775)
        ·
          refine ⟨37659939662782978162444163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25106626441855318774962775 37659939662782978162444163)
          ·
            refine ⟨56489909494174467243666245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37659939662782978162444163 56489909494174467243666245)
            ·
              refine ⟨10591858030157712608187421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56489909494174467243666245 10591858030157712608187421)
              ·
                refine ⟨3971946761309142228070283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10591858030157712608187421 3971946761309142228070283)
                ·
                  refine ⟨5957920141963713342105425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971946761309142228070283 5957920141963713342105425)
                  ·
                    refine ⟨4468440106472785006579069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5957920141963713342105425 4468440106472785006579069)
                    ·
                      refine ⟨1675665039927294377467151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468440106472785006579069 1675665039927294377467151)
                      ·
                        rfl

theorem cell23_3263346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3263346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263346 prefixEnd_3263346 := by exact prefixLift 3263346
  have htrace : WordTrace (prefixWord ++ tailWord_3263346) baseStart_3263346 baseEnd_3263346 := by
    simpa [prefixWord, tailWord_3263346, baseEnd_3263346] using wordTrace_append hprefix tailTrace_3263346
  have hstable : (prefixWord ++ tailWord_3263346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263346).length < 2 ^ (prefixWord ++ tailWord_3263346).sum := by decide
  have hdescent : baseEnd_3263346 < baseStart_3263346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263349 : List Nat := [1, 3, 4, 1, 1, 4, 9]
def baseStart_3263349 : Nat := 118140960795 + 3263349 * 2 ^ 59
def prefixEnd_3263349 : Nat := 4983230072969 + 3 ^ 40 * 3263349 * 2
def baseEnd_3263349 : Nat := 20687241732953800811477

theorem tailTrace_3263349 : CollatzResearch.WordTrace tailWord_3263349 prefixEnd_3263349 20687241732953800811477 := by
  unfold tailWord_3263349
  simp only [CollatzResearch.WordTrace]
  refine ⟨119024116254451383482553101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79349410836300922321702067 119024116254451383482553101)
  ·
    refine ⟨44634043595419268805957413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119024116254451383482553101 44634043595419268805957413)
    ·
      refine ⟨8368883174141112901117015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44634043595419268805957413 8368883174141112901117015)
      ·
        refine ⟨12553324761211669351675523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368883174141112901117015 12553324761211669351675523)
        ·
          refine ⟨18829987141817504027513285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12553324761211669351675523 18829987141817504027513285)
          ·
            refine ⟨3530622589090782005158741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18829987141817504027513285 3530622589090782005158741)
            ·
              refine ⟨20687241732953800811477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3530622589090782005158741 20687241732953800811477)
              ·
                rfl

theorem cell23_3263349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 9].length) (baseStart_3263349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263349 prefixEnd_3263349 := by exact prefixLift 3263349
  have htrace : WordTrace (prefixWord ++ tailWord_3263349) baseStart_3263349 baseEnd_3263349 := by
    simpa [prefixWord, tailWord_3263349, baseEnd_3263349] using wordTrace_append hprefix tailTrace_3263349
  have hstable : (prefixWord ++ tailWord_3263349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263349).length < 2 ^ (prefixWord ++ tailWord_3263349).sum := by decide
  have hdescent : baseEnd_3263349 < baseStart_3263349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263370 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_3263370 : Nat := 118140960795 + 3263370 * 2 ^ 59
def prefixEnd_3263370 : Nat := 4983230072969 + 3 ^ 40 * 3263370 * 2
def baseEnd_3263370 : Nat := 558559121154334094522347

theorem tailTrace_3263370 : CollatzResearch.WordTrace tailWord_3263370 prefixEnd_3263370 558559121154334094522347 := by
  unfold tailWord_3263370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756220546843826017266891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79349921458250202712711709 29756220546843826017266891)
  ·
    refine ⟨44634330820265739025900337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29756220546843826017266891 44634330820265739025900337)
    ·
      refine ⟨33475748115199304269425253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44634330820265739025900337 33475748115199304269425253)
      ·
        refine ⟨6276702771599869550517235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33475748115199304269425253 6276702771599869550517235)
        ·
          refine ⟨9415054157399804325775853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276702771599869550517235 9415054157399804325775853)
          ·
            refine ⟨3530645309024926622165945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9415054157399804325775853 3530645309024926622165945)
            ·
              refine ⟨2647983981768694966624459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530645309024926622165945 2647983981768694966624459)
              ·
                refine ⟨3971975972653042449936689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647983981768694966624459 3971975972653042449936689)
                ·
                  refine ⟨2978981979489781837452517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971975972653042449936689 2978981979489781837452517)
                  ·
                    refine ⟨558559121154334094522347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978981979489781837452517 558559121154334094522347)
                    ·
                      rfl

theorem cell23_3263370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_3263370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263370 prefixEnd_3263370 := by exact prefixLift 3263370
  have htrace : WordTrace (prefixWord ++ tailWord_3263370) baseStart_3263370 baseEnd_3263370 := by
    simpa [prefixWord, tailWord_3263370, baseEnd_3263370] using wordTrace_append hprefix tailTrace_3263370
  have hstable : (prefixWord ++ tailWord_3263370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263370).length < 2 ^ (prefixWord ++ tailWord_3263370).sum := by decide
  have hdescent : baseEnd_3263370 < baseStart_3263370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263439 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 7]
def baseStart_3263439 : Nat := 118140960795 + 3263439 * 2 ^ 59
def prefixEnd_3263439 : Nat := 4983230072969 + 3 ^ 40 * 3263439 * 2
def baseEnd_3263439 : Nat := 186190310403129168178247

theorem tailTrace_3263439 : CollatzResearch.WordTrace tailWord_3263439 prefixEnd_3263439 186190310403129168178247 := by
  unfold tailWord_3263439
  simp only [CollatzResearch.WordTrace]
  refine ⟨119027398824125328853329371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79351599216083552568886247 119027398824125328853329371)
  ·
    refine ⟨178541098236187993279994057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119027398824125328853329371 178541098236187993279994057)
    ·
      refine ⟨133905823677140994959995543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178541098236187993279994057 133905823677140994959995543)
      ·
        refine ⟨200858735515711492439993315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133905823677140994959995543 200858735515711492439993315)
        ·
          refine ⟨301288103273567238659989973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200858735515711492439993315 301288103273567238659989973)
          ·
            refine ⟨7061439920474232156093515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 301288103273567238659989973 7061439920474232156093515)
            ·
              refine ⟨10592159880711348234140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061439920474232156093515 10592159880711348234140273)
              ·
                refine ⟨7944119910533511175605205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10592159880711348234140273 7944119910533511175605205)
                ·
                  refine ⟨186190310403129168178247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7944119910533511175605205 186190310403129168178247)
                  ·
                    rfl

theorem cell23_3263439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 7].length) (baseStart_3263439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263439 prefixEnd_3263439 := by exact prefixLift 3263439
  have htrace : WordTrace (prefixWord ++ tailWord_3263439) baseStart_3263439 baseEnd_3263439 := by
    simpa [prefixWord, tailWord_3263439, baseEnd_3263439] using wordTrace_append hprefix tailTrace_3263439
  have hstable : (prefixWord ++ tailWord_3263439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263439).length < 2 ^ (prefixWord ++ tailWord_3263439).sum := by decide
  have hdescent : baseEnd_3263439 < baseStart_3263439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263466 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3263466 : Nat := 118140960795 + 3263466 * 2 ^ 59
def prefixEnd_3263466 : Nat := 4983230072969 + 3 ^ 40 * 3263466 * 2
def baseEnd_3263466 : Nat := 1675726657605833907966599

theorem tailTrace_3263466 : CollatzResearch.WordTrace tailWord_3263466 prefixEnd_3263466 1675726657605833907966599 := by
  unfold tailWord_3263466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29757095898756878116140563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79352255730018341643041501 29757095898756878116140563)
  ·
    refine ⟨44635643848135317174210845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29757095898756878116140563 44635643848135317174210845)
    ·
      refine ⟨16738366443050743940329067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44635643848135317174210845 16738366443050743940329067)
      ·
        refine ⟨25107549664576115910493601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16738366443050743940329067 25107549664576115910493601)
        ·
          refine ⟨18830662248432086932870201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25107549664576115910493601 18830662248432086932870201)
          ·
            refine ⟨14122996686324065199652651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18830662248432086932870201 14122996686324065199652651)
            ·
              refine ⟨21184495029486097799478977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14122996686324065199652651 21184495029486097799478977)
              ·
                refine ⟨15888371272114573349609233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21184495029486097799478977 15888371272114573349609233)
                ·
                  refine ⟨11916278454085930012206925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15888371272114573349609233 11916278454085930012206925)
                  ·
                    refine ⟨4468604420282223754577597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916278454085930012206925 4468604420282223754577597)
                    ·
                      refine ⟨1675726657605833907966599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468604420282223754577597 1675726657605833907966599)
                      ·
                        rfl

theorem cell23_3263466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3263466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263466 prefixEnd_3263466 := by exact prefixLift 3263466
  have htrace : WordTrace (prefixWord ++ tailWord_3263466) baseStart_3263466 baseEnd_3263466 := by
    simpa [prefixWord, tailWord_3263466, baseEnd_3263466] using wordTrace_append hprefix tailTrace_3263466
  have hstable : (prefixWord ++ tailWord_3263466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263466).length < 2 ^ (prefixWord ++ tailWord_3263466).sum := by decide
  have hdescent : baseEnd_3263466 < baseStart_3263466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263583 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 2, 3, 2]
def baseStart_3263583 : Nat := 118140960795 + 3263583 * 2 ^ 59
def prefixEnd_3263583 : Nat := 4983230072969 + 3 ^ 40 * 3263583 * 2
def baseEnd_3263583 : Nat := 1675786734842409950203561

theorem tailTrace_3263583 : CollatzResearch.WordTrace tailWord_3263583 prefixEnd_3263583 1675786734842409950203561 := by
  unfold tailWord_3263583
  simp only [CollatzResearch.WordTrace]
  refine ⟨119032650935603641446571403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79355100623735760964380935 119032650935603641446571403)
  ·
    refine ⟨178548976403405462169857105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119032650935603641446571403 178548976403405462169857105)
    ·
      refine ⟨133911732302554096627392829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178548976403405462169857105 133911732302554096627392829)
      ·
        refine ⟨50216899613457786235272311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133911732302554096627392829 50216899613457786235272311)
        ·
          refine ⟨75325349420186679352908467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50216899613457786235272311 75325349420186679352908467)
          ·
            refine ⟨112988024130280019029362701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75325349420186679352908467 112988024130280019029362701)
            ·
              refine ⟨42370509048855007136011013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112988024130280019029362701 42370509048855007136011013)
              ·
                refine ⟨7944470446660313838002065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42370509048855007136011013 7944470446660313838002065)
                ·
                  refine ⟨5958352834995235378501549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7944470446660313838002065 5958352834995235378501549)
                  ·
                    refine ⟨2234382313123213266938081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5958352834995235378501549 2234382313123213266938081)
                    ·
                      refine ⟨1675786734842409950203561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234382313123213266938081 1675786734842409950203561)
                      ·
                        rfl

theorem cell23_3263583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_3263583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263583 prefixEnd_3263583 := by exact prefixLift 3263583
  have htrace : WordTrace (prefixWord ++ tailWord_3263583) baseStart_3263583 baseEnd_3263583 := by
    simpa [prefixWord, tailWord_3263583, baseEnd_3263583] using wordTrace_append hprefix tailTrace_3263583
  have hstable : (prefixWord ++ tailWord_3263583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263583).length < 2 ^ (prefixWord ++ tailWord_3263583).sum := by decide
  have hdescent : baseEnd_3263583 < baseStart_3263583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263596 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_3263596 : Nat := 118140960795 + 3263596 * 2 ^ 59
def prefixEnd_3263596 : Nat := 4983230072969 + 3 ^ 40 * 3263596 * 2
def baseEnd_3263596 : Nat := 1675793410090918399341001

theorem tailTrace_3263596 : CollatzResearch.WordTrace tailWord_3263596 prefixEnd_3263596 1675793410090918399341001 := by
  unfold tailWord_3263596
  simp only [CollatzResearch.WordTrace]
  refine ⟨59516562542278272333397321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79355416723037696444529761 59516562542278272333397321)
  ·
    refine ⟨44637421906708704250047991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59516562542278272333397321 44637421906708704250047991)
    ·
      refine ⟨66956132860063056375071987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44637421906708704250047991 66956132860063056375071987)
      ·
        refine ⟨100434199290094584562607981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66956132860063056375071987 100434199290094584562607981)
        ·
          refine ⟨37662824733785469210977993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100434199290094584562607981 37662824733785469210977993)
          ·
            refine ⟨28247118550339101908233495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37662824733785469210977993 28247118550339101908233495)
            ·
              refine ⟨42370677825508652862350243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28247118550339101908233495 42370677825508652862350243)
              ·
                refine ⟨63556016738262979293525365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42370677825508652862350243 63556016738262979293525365)
                ·
                  refine ⟨5958376569212154308768003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63556016738262979293525365 5958376569212154308768003)
                  ·
                    refine ⟨8937564853818231463152005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958376569212154308768003 8937564853818231463152005)
                    ·
                      refine ⟨1675793410090918399341001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8937564853818231463152005 1675793410090918399341001)
                      ·
                        rfl

theorem cell23_3263596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_3263596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263596 prefixEnd_3263596 := by exact prefixLift 3263596
  have htrace : WordTrace (prefixWord ++ tailWord_3263596) baseStart_3263596 baseEnd_3263596 := by
    simpa [prefixWord, tailWord_3263596, baseEnd_3263596] using wordTrace_append hprefix tailTrace_3263596
  have hstable : (prefixWord ++ tailWord_3263596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263596).length < 2 ^ (prefixWord ++ tailWord_3263596).sum := by decide
  have hdescent : baseEnd_3263596 < baseStart_3263596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263613 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_3263613 : Nat := 118140960795 + 3263613 * 2 ^ 59
def prefixEnd_3263613 : Nat := 4983230072969 + 3 ^ 40 * 3263613 * 2
def baseEnd_3263613 : Nat := 1675802139262044832828423

theorem tailTrace_3263613 : CollatzResearch.WordTrace tailWord_3263613 prefixEnd_3263613 1675802139262044832828423 := by
  unfold tailWord_3263613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119033745125494956570163493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79355830083663304380108995 119033745125494956570163493)
  ·
    refine ⟨22318827211030304356905655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119033745125494956570163493 22318827211030304356905655)
    ·
      refine ⟨33478240816545456535358483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22318827211030304356905655 33478240816545456535358483)
      ·
        refine ⟨50217361224818184803037725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33478240816545456535358483 50217361224818184803037725)
        ·
          refine ⟨18831510459306819301139147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50217361224818184803037725 18831510459306819301139147)
          ·
            refine ⟨28247265688960228951708721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18831510459306819301139147 28247265688960228951708721)
            ·
              refine ⟨21185449266720171713781541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28247265688960228951708721 21185449266720171713781541)
              ·
                refine ⟨3972271737510032196334039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21185449266720171713781541 3972271737510032196334039)
                ·
                  refine ⟨5958407606265048294501059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972271737510032196334039 5958407606265048294501059)
                  ·
                    refine ⟨8937611409397572441751589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958407606265048294501059 8937611409397572441751589)
                    ·
                      refine ⟨1675802139262044832828423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8937611409397572441751589 1675802139262044832828423)
                      ·
                        rfl

theorem cell23_3263613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_3263613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263613 prefixEnd_3263613 := by exact prefixLift 3263613
  have htrace : WordTrace (prefixWord ++ tailWord_3263613) baseStart_3263613 baseEnd_3263613 := by
    simpa [prefixWord, tailWord_3263613, baseEnd_3263613] using wordTrace_append hprefix tailTrace_3263613
  have hstable : (prefixWord ++ tailWord_3263613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263613).length < 2 ^ (prefixWord ++ tailWord_3263613).sum := by decide
  have hdescent : baseEnd_3263613 < baseStart_3263613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263617 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_3263617 : Nat := 118140960795 + 3263617 * 2 ^ 59
def prefixEnd_3263617 : Nat := 4983230072969 + 3 ^ 40 * 3263617 * 2
def baseEnd_3263617 : Nat := 1675804193184662817178405

theorem tailTrace_3263617 : CollatzResearch.WordTrace tailWord_3263617 prefixEnd_3263617 1675804193184662817178405 := by
  unfold tailWord_3263617
  simp only [CollatzResearch.WordTrace]
  refine ⟨119033891017480465253309105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79355927344986976835539403 119033891017480465253309105)
  ·
    refine ⟨89275418263110348939981829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119033891017480465253309105 89275418263110348939981829)
    ·
      refine ⟨16739140924333190426246593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89275418263110348939981829 16739140924333190426246593)
      ·
        refine ⟨12554355693249892819684945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16739140924333190426246593 12554355693249892819684945)
        ·
          refine ⟨9415766769937419614763709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12554355693249892819684945 9415766769937419614763709)
          ·
            refine ⟨3530912538726532355536391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9415766769937419614763709 3530912538726532355536391)
            ·
              refine ⟨5296368808089798533304587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530912538726532355536391 5296368808089798533304587)
              ·
                refine ⟨7944553212134697799956881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296368808089798533304587 7944553212134697799956881)
                ·
                  refine ⟨5958414909101023349967661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7944553212134697799956881 5958414909101023349967661)
                  ·
                    refine ⟨2234405590912883756237873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5958414909101023349967661 2234405590912883756237873)
                    ·
                      refine ⟨1675804193184662817178405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234405590912883756237873 1675804193184662817178405)
                      ·
                        rfl

theorem cell23_3263617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_3263617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263617 prefixEnd_3263617 := by exact prefixLift 3263617
  have htrace : WordTrace (prefixWord ++ tailWord_3263617) baseStart_3263617 baseEnd_3263617 := by
    simpa [prefixWord, tailWord_3263617, baseEnd_3263617] using wordTrace_append hprefix tailTrace_3263617
  have hstable : (prefixWord ++ tailWord_3263617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263617).length < 2 ^ (prefixWord ++ tailWord_3263617).sum := by decide
  have hdescent : baseEnd_3263617 < baseStart_3263617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263624 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3263624 : Nat := 118140960795 + 3263624 * 2 ^ 59
def prefixEnd_3263624 : Nat := 4983230072969 + 3 ^ 40 * 3263624 * 2
def baseEnd_3263624 : Nat := 1675807787549244289790873

theorem tailTrace_3263624 : CollatzResearch.WordTrace tailWord_3263624 prefixEnd_3263624 1675807787549244289790873 := by
  unfold tailWord_3263624
  simp only [CollatzResearch.WordTrace]
  refine ⟨59517073164227552724406963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79356097552303403632542617 59517073164227552724406963)
  ·
    refine ⟨89275609746341329086610445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59517073164227552724406963 89275609746341329086610445)
    ·
      refine ⟨33478353654877998407478917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89275609746341329086610445 33478353654877998407478917)
      ·
        refine ⟨6277191310289624701402297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33478353654877998407478917 6277191310289624701402297)
        ·
          refine ⟨4707893482717218526051723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6277191310289624701402297 4707893482717218526051723)
          ·
            refine ⟨7061840224075827789077585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707893482717218526051723 7061840224075827789077585)
            ·
              refine ⟨5296380168056870841808189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7061840224075827789077585 5296380168056870841808189)
              ·
                refine ⟨1986142563021326565678071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5296380168056870841808189 1986142563021326565678071)
                ·
                  refine ⟨2979213844531989848517107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986142563021326565678071 2979213844531989848517107)
                  ·
                    refine ⟨4468820766797984772775661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979213844531989848517107 4468820766797984772775661)
                    ·
                      refine ⟨1675807787549244289790873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468820766797984772775661 1675807787549244289790873)
                      ·
                        rfl

theorem cell23_3263624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3263624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263624 prefixEnd_3263624 := by exact prefixLift 3263624
  have htrace : WordTrace (prefixWord ++ tailWord_3263624) baseStart_3263624 baseEnd_3263624 := by
    simpa [prefixWord, tailWord_3263624, baseEnd_3263624] using wordTrace_append hprefix tailTrace_3263624
  have hstable : (prefixWord ++ tailWord_3263624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263624).length < 2 ^ (prefixWord ++ tailWord_3263624).sum := by decide
  have hdescent : baseEnd_3263624 < baseStart_3263624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263630 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3263630 : Nat := 118140960795 + 3263630 * 2 ^ 59
def prefixEnd_3263630 : Nat := 4983230072969 + 3 ^ 40 * 3263630 * 2
def baseEnd_3263630 : Nat := 1675810868433171266315845

theorem tailTrace_3263630 : CollatzResearch.WordTrace tailWord_3263630 prefixEnd_3263630 1675810868433171266315845 := by
  unfold tailWord_3263630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14879295645804171059191543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79356243444288912315688229 14879295645804171059191543)
  ·
    refine ⟨22318943468706256588787315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14879295645804171059191543 22318943468706256588787315)
    ·
      refine ⟨33478415203059384883180973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22318943468706256588787315 33478415203059384883180973)
      ·
        refine ⟨12554405701147269331192865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33478415203059384883180973 12554405701147269331192865)
        ·
          refine ⟨9415804275860451998394649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12554405701147269331192865 9415804275860451998394649)
          ·
            refine ⟨7061853206895338998795987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9415804275860451998394649 7061853206895338998795987)
            ·
              refine ⟨10592779810343008498193981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061853206895338998795987 10592779810343008498193981)
              ·
                refine ⟨3972292428878628186822743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10592779810343008498193981 3972292428878628186822743)
                ·
                  refine ⟨5958438643317942280234115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972292428878628186822743 5958438643317942280234115)
                  ·
                    refine ⟨8937657964976913420351173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958438643317942280234115 8937657964976913420351173)
                    ·
                      refine ⟨1675810868433171266315845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8937657964976913420351173 1675810868433171266315845)
                      ·
                        rfl

theorem cell23_3263630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3263630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263630 prefixEnd_3263630 := by exact prefixLift 3263630
  have htrace : WordTrace (prefixWord ++ tailWord_3263630) baseStart_3263630 baseEnd_3263630 := by
    simpa [prefixWord, tailWord_3263630, baseEnd_3263630] using wordTrace_append hprefix tailTrace_3263630
  have hstable : (prefixWord ++ tailWord_3263630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263630).length < 2 ^ (prefixWord ++ tailWord_3263630).sum := by decide
  have hdescent : baseEnd_3263630 < baseStart_3263630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263640 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_3263640 : Nat := 118140960795 + 3263640 * 2 ^ 59
def prefixEnd_3263640 : Nat := 4983230072969 + 3 ^ 40 * 3263640 * 2
def baseEnd_3263640 : Nat := 558605334413238742396933

theorem tailTrace_3263640 : CollatzResearch.WordTrace tailWord_3263640 prefixEnd_3263640 558605334413238742396933 := by
  unfold tailWord_3263640
  simp only [CollatzResearch.WordTrace]
  refine ⟨59517364948198570090698187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79356486597598093454264249 59517364948198570090698187)
  ·
    refine ⟨89276047422297855136047281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59517364948198570090698187 89276047422297855136047281)
    ·
      refine ⟨66957035566723391352035461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89276047422297855136047281 66957035566723391352035461)
      ·
        refine ⟨12554444168760635878506649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66957035566723391352035461 12554444168760635878506649)
        ·
          refine ⟨9415833126570476908879987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12554444168760635878506649 9415833126570476908879987)
          ·
            refine ⟨14123749689855715363319981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415833126570476908879987 14123749689855715363319981)
            ·
              refine ⟨5296406133695893261244993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14123749689855715363319981 5296406133695893261244993)
              ·
                refine ⟨3972304600271919945933745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5296406133695893261244993 3972304600271919945933745)
                ·
                  refine ⟨2979228450203939959450309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972304600271919945933745 2979228450203939959450309)
                  ·
                    refine ⟨558605334413238742396933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979228450203939959450309 558605334413238742396933)
                    ·
                      rfl

theorem cell23_3263640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_3263640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263640 prefixEnd_3263640 := by exact prefixLift 3263640
  have htrace : WordTrace (prefixWord ++ tailWord_3263640) baseStart_3263640 baseEnd_3263640 := by
    simpa [prefixWord, tailWord_3263640, baseEnd_3263640] using wordTrace_append hprefix tailTrace_3263640
  have hstable : (prefixWord ++ tailWord_3263640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263640).length < 2 ^ (prefixWord ++ tailWord_3263640).sum := by decide
  have hdescent : baseEnd_3263640 < baseStart_3263640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263650 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3263650 : Nat := 118140960795 + 3263650 * 2 ^ 59
def prefixEnd_3263650 : Nat := 4983230072969 + 3 ^ 40 * 3263650 * 2
def baseEnd_3263650 : Nat := 1675821138046261188065753

theorem tailTrace_3263650 : CollatzResearch.WordTrace tailWord_3263650 prefixEnd_3263650 1675821138046261188065753 := by
  unfold tailWord_3263650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29758773656590227972315101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79356729750907274592840269 29758773656590227972315101)
  ·
    refine ⟨11159540121221335489618163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29758773656590227972315101 11159540121221335489618163)
    ·
      refine ⟨16739310181832003234427245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11159540121221335489618163 16739310181832003234427245)
      ·
        refine ⟨6277241318187001212910217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16739310181832003234427245 6277241318187001212910217)
        ·
          refine ⟨4707930988640250909682663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6277241318187001212910217 4707930988640250909682663)
          ·
            refine ⟨7061896482960376364523995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707930988640250909682663 7061896482960376364523995)
            ·
              refine ⟨10592844724440564546785993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061896482960376364523995 10592844724440564546785993)
              ·
                refine ⟨7944633543330423410089495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10592844724440564546785993 7944633543330423410089495)
                ·
                  refine ⟨11916950314995635115134243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944633543330423410089495 11916950314995635115134243)
                  ·
                    refine ⟨17875425472493452672701365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11916950314995635115134243 17875425472493452672701365)
                    ·
                      refine ⟨1675821138046261188065753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17875425472493452672701365 1675821138046261188065753)
                      ·
                        rfl

theorem cell23_3263650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3263650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263650 prefixEnd_3263650 := by exact prefixLift 3263650
  have htrace : WordTrace (prefixWord ++ tailWord_3263650) baseStart_3263650 baseEnd_3263650 := by
    simpa [prefixWord, tailWord_3263650, baseEnd_3263650] using wordTrace_append hprefix tailTrace_3263650
  have hstable : (prefixWord ++ tailWord_3263650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263650).length < 2 ^ (prefixWord ++ tailWord_3263650).sum := by decide
  have hdescent : baseEnd_3263650 < baseStart_3263650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263663 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_3263663 : Nat := 118140960795 + 3263663 * 2 ^ 59
def prefixEnd_3263663 : Nat := 4983230072969 + 3 ^ 40 * 3263663 * 2
def baseEnd_3263663 : Nat := 1675827813294769637203193

theorem tailTrace_3263663 : CollatzResearch.WordTrace tailWord_3263663 prefixEnd_3263663 1675827813294769637203193 := by
  unfold tailWord_3263663
  simp only [CollatzResearch.WordTrace]
  refine ⟨119035568775313815109483643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79357045850209210072989095 119035568775313815109483643)
  ·
    refine ⟨178553353162970722664225465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119035568775313815109483643 178553353162970722664225465)
    ·
      refine ⟨133915014872228041998169099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178553353162970722664225465 133915014872228041998169099)
      ·
        refine ⟨200872522308342062997253649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133915014872228041998169099 200872522308342062997253649)
        ·
          refine ⟨150654391731256547247940237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200872522308342062997253649 150654391731256547247940237)
          ·
            refine ⟨56495396899221205217977589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150654391731256547247940237 56495396899221205217977589)
            ·
              refine ⟨5296443459301987989185399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56495396899221205217977589 5296443459301987989185399)
              ·
                refine ⟨7944665188952981983778099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296443459301987989185399 7944665188952981983778099)
                ·
                  refine ⟨11916997783429472975667149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944665188952981983778099 11916997783429472975667149)
                  ·
                    refine ⟨4468874168786052365875181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916997783429472975667149 4468874168786052365875181)
                    ·
                      refine ⟨1675827813294769637203193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468874168786052365875181 1675827813294769637203193)
                      ·
                        rfl

theorem cell23_3263663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_3263663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263663 prefixEnd_3263663 := by exact prefixLift 3263663
  have htrace : WordTrace (prefixWord ++ tailWord_3263663) baseStart_3263663 baseEnd_3263663 := by
    simpa [prefixWord, tailWord_3263663, baseEnd_3263663] using wordTrace_append hprefix tailTrace_3263663
  have hstable : (prefixWord ++ tailWord_3263663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263663).length < 2 ^ (prefixWord ++ tailWord_3263663).sum := by decide
  have hdescent : baseEnd_3263663 < baseStart_3263663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263681 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3263681 : Nat := 118140960795 + 3263681 * 2 ^ 59
def prefixEnd_3263681 : Nat := 4983230072969 + 3 ^ 40 * 3263681 * 2
def baseEnd_3263681 : Nat := 1675837055946550566778111

theorem tailTrace_3263681 : CollatzResearch.WordTrace tailWord_3263681 prefixEnd_3263681 1675837055946550566778111 := by
  unfold tailWord_3263681
  simp only [CollatzResearch.WordTrace]
  refine ⟨119036225289248604183638897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79357483526165736122425931 119036225289248604183638897)
  ·
    refine ⟨89277168966936453137729173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119036225289248604183638897 89277168966936453137729173)
    ·
      refine ⟨4184867295325146240831055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89277168966936453137729173 4184867295325146240831055)
      ·
        refine ⟨6277300942987719361246583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4184867295325146240831055 6277300942987719361246583)
        ·
          refine ⟨9415951414481579041869875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277300942987719361246583 9415951414481579041869875)
          ·
            refine ⟨14123927121722368562804813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415951414481579041869875 14123927121722368562804813)
            ·
              refine ⟨5296472670645888211051805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14123927121722368562804813 5296472670645888211051805)
              ·
                refine ⟨1986177251492208079144427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5296472670645888211051805 1986177251492208079144427)
                ·
                  refine ⟨2979265877238312118716641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986177251492208079144427 2979265877238312118716641)
                  ·
                    refine ⟨2234449407928734089037481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979265877238312118716641 2234449407928734089037481)
                    ·
                      refine ⟨1675837055946550566778111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234449407928734089037481 1675837055946550566778111)
                      ·
                        rfl

theorem cell23_3263681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3263681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263681 prefixEnd_3263681 := by exact prefixLift 3263681
  have htrace : WordTrace (prefixWord ++ tailWord_3263681) baseStart_3263681 baseEnd_3263681 := by
    simpa [prefixWord, tailWord_3263681, baseEnd_3263681] using wordTrace_append hprefix tailTrace_3263681
  have hstable : (prefixWord ++ tailWord_3263681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263681).length < 2 ^ (prefixWord ++ tailWord_3263681).sum := by decide
  have hdescent : baseEnd_3263681 < baseStart_3263681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263706 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3263706 : Nat := 118140960795 + 3263706 * 2 ^ 59
def prefixEnd_3263706 : Nat := 4983230072969 + 3 ^ 40 * 3263706 * 2
def baseEnd_3263706 : Nat := 1675849892962912968965495

theorem tailTrace_3263706 : CollatzResearch.WordTrace tailWord_3263706 prefixEnd_3263706 1675849892962912968965495 := by
  unfold tailWord_3263706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29759284278539508363324743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79358091409438688968865981 29759284278539508363324743)
  ·
    refine ⟨44638926417809262544987115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29759284278539508363324743 44638926417809262544987115)
    ·
      refine ⟨66958389626713893817480673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44638926417809262544987115 66958389626713893817480673)
      ·
        refine ⟨50218792220035420363110505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66958389626713893817480673 50218792220035420363110505)
        ·
          refine ⟨37664094165026565272332879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50218792220035420363110505 37664094165026565272332879)
          ·
            refine ⟨56496141247539847908499319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37664094165026565272332879 56496141247539847908499319)
            ·
              refine ⟨84744211871309771862748979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56496141247539847908499319 84744211871309771862748979)
              ·
                refine ⟨127116317806964657794123469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84744211871309771862748979 127116317806964657794123469)
                ·
                  refine ⟨47668619177611746672796301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127116317806964657794123469 47668619177611746672796301)
                  ·
                    refine ⟨17875732191604405002298613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47668619177611746672796301 17875732191604405002298613)
                    ·
                      refine ⟨1675849892962912968965495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17875732191604405002298613 1675849892962912968965495)
                      ·
                        rfl

theorem cell23_3263706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3263706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263706 prefixEnd_3263706 := by exact prefixLift 3263706
  have htrace : WordTrace (prefixWord ++ tailWord_3263706) baseStart_3263706 baseEnd_3263706 := by
    simpa [prefixWord, tailWord_3263706, baseEnd_3263706] using wordTrace_append hprefix tailTrace_3263706
  have hstable : (prefixWord ++ tailWord_3263706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263706).length < 2 ^ (prefixWord ++ tailWord_3263706).sum := by decide
  have hdescent : baseEnd_3263706 < baseStart_3263706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263720 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_3263720 : Nat := 118140960795 + 3263720 * 2 ^ 59
def prefixEnd_3263720 : Nat := 4983230072969 + 3 ^ 40 * 3263720 * 2
def baseEnd_3263720 : Nat := 1675857081692075914190431

theorem tailTrace_3263720 : CollatzResearch.WordTrace tailWord_3263720 prefixEnd_3263720 1675857081692075914190431 := by
  unfold tailWord_3263720
  simp only [CollatzResearch.WordTrace]
  refine ⟨59518823868053656922154307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79358431824071542562872409 59518823868053656922154307)
  ·
    refine ⟨89278235802080485383231461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59518823868053656922154307 89278235802080485383231461)
    ·
      refine ⟨16739669212890091009355899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89278235802080485383231461 16739669212890091009355899)
      ·
        refine ⟨25109503819335136514033849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16739669212890091009355899 25109503819335136514033849)
        ·
          refine ⟨18832127864501352385525387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25109503819335136514033849 18832127864501352385525387)
          ·
            refine ⟨28248191796752028578288081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18832127864501352385525387 28248191796752028578288081)
            ·
              refine ⟨21186143847564021433716061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28248191796752028578288081 21186143847564021433716061)
              ·
                refine ⟨7944803942836508037643523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21186143847564021433716061 7944803942836508037643523)
                ·
                  refine ⟨11917205914254762056465285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944803942836508037643523 11917205914254762056465285)
                  ·
                    refine ⟨2234476108922767885587241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11917205914254762056465285 2234476108922767885587241)
                    ·
                      refine ⟨1675857081692075914190431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234476108922767885587241 1675857081692075914190431)
                      ·
                        rfl

theorem cell23_3263720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_3263720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263720 prefixEnd_3263720 := by exact prefixLift 3263720
  have htrace : WordTrace (prefixWord ++ tailWord_3263720) baseStart_3263720 baseEnd_3263720 := by
    simpa [prefixWord, tailWord_3263720, baseEnd_3263720] using wordTrace_append hprefix tailTrace_3263720
  have hstable : (prefixWord ++ tailWord_3263720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263720).length < 2 ^ (prefixWord ++ tailWord_3263720).sum := by decide
  have hdescent : baseEnd_3263720 < baseStart_3263720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263753 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_3263753 : Nat := 118140960795 + 3263753 * 2 ^ 59
def prefixEnd_3263753 : Nat := 4983230072969 + 3 ^ 40 * 3263753 * 2
def baseEnd_3263753 : Nat := 1675874026553674285077779

theorem tailTrace_3263753 : CollatzResearch.WordTrace tailWord_3263753 prefixEnd_3263753 1675874026553674285077779 := by
  unfold tailWord_3263753
  simp only [CollatzResearch.WordTrace]
  refine ⟨119038851344987760480259913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79359234229991840320173275 119038851344987760480259913)
  ·
    refine ⟨89279138508740820360194935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119038851344987760480259913 89279138508740820360194935)
    ·
      refine ⟨133918707763111230540292403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89279138508740820360194935 133918707763111230540292403)
      ·
        refine ⟨200878061644666845810438605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133918707763111230540292403 200878061644666845810438605)
        ·
          refine ⟨75329273116750067178914477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200878061644666845810438605 75329273116750067178914477)
          ·
            refine ⟨28248477418781275192092929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75329273116750067178914477 28248477418781275192092929)
            ·
              refine ⟨21186358064085956394069697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28248477418781275192092929 21186358064085956394069697)
              ·
                refine ⟨15889768548064467295552273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21186358064085956394069697 15889768548064467295552273)
                ·
                  refine ⟨11917326411048350471664205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15889768548064467295552273 11917326411048350471664205)
                  ·
                    refine ⟨4468997404143131426874077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11917326411048350471664205 4468997404143131426874077)
                    ·
                      refine ⟨1675874026553674285077779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4468997404143131426874077 1675874026553674285077779)
                      ·
                        rfl

theorem cell23_3263753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_3263753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263753 prefixEnd_3263753 := by exact prefixLift 3263753
  have htrace : WordTrace (prefixWord ++ tailWord_3263753) baseStart_3263753 baseEnd_3263753 := by
    simpa [prefixWord, tailWord_3263753, baseEnd_3263753] using wordTrace_append hprefix tailTrace_3263753
  have hstable : (prefixWord ++ tailWord_3263753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263753).length < 2 ^ (prefixWord ++ tailWord_3263753).sum := by decide
  have hdescent : baseEnd_3263753 < baseStart_3263753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263770 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3263770 : Nat := 118140960795 + 3263770 * 2 ^ 59
def prefixEnd_3263770 : Nat := 4983230072969 + 3 ^ 40 * 3263770 * 2
def baseEnd_3263770 : Nat := 1675882755724800718565201

theorem tailTrace_3263770 : CollatzResearch.WordTrace tailWord_3263770 prefixEnd_3263770 1675882755724800718565201 := by
  unfold tailWord_3263770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29759867846481543095907191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79359647590617448255752509 29759867846481543095907191)
  ·
    refine ⟨44639801769722314643860787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29759867846481543095907191 44639801769722314643860787)
    ·
      refine ⟨66959702654583471965791181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44639801769722314643860787 66959702654583471965791181)
      ·
        refine ⟨25109888495468801987171693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66959702654583471965791181 25109888495468801987171693)
        ·
          refine ⟨9416208185800800745189385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25109888495468801987171693 9416208185800800745189385)
          ·
            refine ⟨7062156139350600558892039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9416208185800800745189385 7062156139350600558892039)
            ·
              refine ⟨10593234209025900838338059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062156139350600558892039 10593234209025900838338059)
              ·
                refine ⟨15889851313538851257507089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10593234209025900838338059 15889851313538851257507089)
                ·
                  refine ⟨11917388485154138443130317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15889851313538851257507089 11917388485154138443130317)
                  ·
                    refine ⟨4469020681932801916173869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11917388485154138443130317 4469020681932801916173869)
                    ·
                      refine ⟨1675882755724800718565201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469020681932801916173869 1675882755724800718565201)
                      ·
                        rfl

theorem cell23_3263770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3263770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263770 prefixEnd_3263770 := by exact prefixLift 3263770
  have htrace : WordTrace (prefixWord ++ tailWord_3263770) baseStart_3263770 baseEnd_3263770 := by
    simpa [prefixWord, tailWord_3263770, baseEnd_3263770] using wordTrace_append hprefix tailTrace_3263770
  have hstable : (prefixWord ++ tailWord_3263770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263770).length < 2 ^ (prefixWord ++ tailWord_3263770).sum := by decide
  have hdescent : baseEnd_3263770 < baseStart_3263770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263780 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_3263780 : Nat := 118140960795 + 3263780 * 2 ^ 59
def prefixEnd_3263780 : Nat := 4983230072969 + 3 ^ 40 * 3263780 * 2
def baseEnd_3263780 : Nat := 1675887890531345679440155

theorem tailTrace_3263780 : CollatzResearch.WordTrace tailWord_3263780 prefixEnd_3263780 1675887890531345679440155 := by
  unfold tailWord_3263780
  simp only [CollatzResearch.WordTrace]
  refine ⟨59519918057944972045746397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79359890743926629394328529 59519918057944972045746397)
  ·
    refine ⟨22319969271729364517154899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59519918057944972045746397 22319969271729364517154899)
    ·
      refine ⟨33479953907594046775732349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22319969271729364517154899 33479953907594046775732349)
      ·
        refine ⟨12554982715347767540899631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33479953907594046775732349 12554982715347767540899631)
        ·
          refine ⟨18832474073021651311349447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12554982715347767540899631 18832474073021651311349447)
          ·
            refine ⟨28248711109532476967024171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18832474073021651311349447 28248711109532476967024171)
            ·
              refine ⟨42373066664298715450536257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28248711109532476967024171 42373066664298715450536257)
              ·
                refine ⟨31779799998224036587902193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42373066664298715450536257 31779799998224036587902193)
                ·
                  refine ⟨23834849998668027440926645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31779799998224036587902193 23834849998668027440926645)
                  ·
                    refine ⟨2234517187375127572586873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23834849998668027440926645 2234517187375127572586873)
                    ·
                      refine ⟨1675887890531345679440155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234517187375127572586873 1675887890531345679440155)
                      ·
                        rfl

theorem cell23_3263780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_3263780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263780 prefixEnd_3263780 := by exact prefixLift 3263780
  have htrace : WordTrace (prefixWord ++ tailWord_3263780) baseStart_3263780 baseEnd_3263780 := by
    simpa [prefixWord, tailWord_3263780, baseEnd_3263780] using wordTrace_append hprefix tailTrace_3263780
  have hstable : (prefixWord ++ tailWord_3263780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263780).length < 2 ^ (prefixWord ++ tailWord_3263780).sum := by decide
  have hdescent : baseEnd_3263780 < baseStart_3263780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263820 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_3263820 : Nat := 118140960795 + 3263820 * 2 ^ 59
def prefixEnd_3263820 : Nat := 4983230072969 + 3 ^ 40 * 3263820 * 2
def baseEnd_3263820 : Nat := 558636143252508507646657

theorem tailTrace_3263820 : CollatzResearch.WordTrace tailWord_3263820 prefixEnd_3263820 558636143252508507646657 := by
  unfold tailWord_3263820
  simp only [CollatzResearch.WordTrace]
  refine ⟨59520647517872515461474457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79360863357163353948632609 59520647517872515461474457)
  ·
    refine ⟨44640485638404386596105843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59520647517872515461474457 44640485638404386596105843)
    ·
      refine ⟨66960728457606579894158765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44640485638404386596105843 66960728457606579894158765)
      ·
        refine ⟨25110273171602467460309537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66960728457606579894158765 25110273171602467460309537)
        ·
          refine ⟨18832704878701850595232153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25110273171602467460309537 18832704878701850595232153)
          ·
            refine ⟨14124528659026387946424115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18832704878701850595232153 14124528659026387946424115)
            ·
              refine ⟨21186792988539581919636173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14124528659026387946424115 21186792988539581919636173)
              ·
                refine ⟨7945047370702343219863565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21186792988539581919636173 7945047370702343219863565)
                ·
                  refine ⟨2979392764013378707448837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7945047370702343219863565 2979392764013378707448837)
                  ·
                    refine ⟨558636143252508507646657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979392764013378707448837 558636143252508507646657)
                    ·
                      rfl

theorem cell23_3263820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_3263820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263820 prefixEnd_3263820 := by exact prefixLift 3263820
  have htrace : WordTrace (prefixWord ++ tailWord_3263820) baseStart_3263820 baseEnd_3263820 := by
    simpa [prefixWord, tailWord_3263820, baseEnd_3263820] using wordTrace_append hprefix tailTrace_3263820
  have hstable : (prefixWord ++ tailWord_3263820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263820).length < 2 ^ (prefixWord ++ tailWord_3263820).sum := by decide
  have hdescent : baseEnd_3263820 < baseStart_3263820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263833 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 6]
def baseStart_3263833 : Nat := 118140960795 + 3263833 * 2 ^ 59
def prefixEnd_3263833 : Nat := 4983230072969 + 3 ^ 40 * 3263833 * 2
def baseEnd_3263833 : Nat := 186212789445114885786379

theorem tailTrace_3263833 : CollatzResearch.WordTrace tailWord_3263833 prefixEnd_3263833 186212789445114885786379 := by
  unfold tailWord_3263833
  simp only [CollatzResearch.WordTrace]
  refine ⟨119041769184697934143172153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79361179456465289428781435 119041769184697934143172153)
  ·
    refine ⟨89281326888523450607379115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119041769184697934143172153 89281326888523450607379115)
    ·
      refine ⟨133921990332785175911068673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89281326888523450607379115 133921990332785175911068673)
      ·
        refine ⟨100441492749588881933301505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133921990332785175911068673 100441492749588881933301505)
        ·
          refine ⟨75331119562191661449976129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100441492749588881933301505 75331119562191661449976129)
          ·
            refine ⟨56498339671643746087482097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75331119562191661449976129 56498339671643746087482097)
            ·
              refine ⟨42373754753732809565611573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56498339671643746087482097 42373754753732809565611573)
              ·
                refine ⟨3972539508162450896776085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42373754753732809565611573 3972539508162450896776085)
                ·
                  refine ⟨186212789445114885786379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3972539508162450896776085 186212789445114885786379)
                  ·
                    rfl

theorem cell23_3263833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_3263833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263833 prefixEnd_3263833 := by exact prefixLift 3263833
  have htrace : WordTrace (prefixWord ++ tailWord_3263833) baseStart_3263833 baseEnd_3263833 := by
    simpa [prefixWord, tailWord_3263833, baseEnd_3263833] using wordTrace_append hprefix tailTrace_3263833
  have hstable : (prefixWord ++ tailWord_3263833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263833).length < 2 ^ (prefixWord ++ tailWord_3263833).sum := by decide
  have hdescent : baseEnd_3263833 < baseStart_3263833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263877 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_3263877 : Nat := 118140960795 + 3263877 * 2 ^ 59
def prefixEnd_3263877 : Nat := 4983230072969 + 3 ^ 40 * 3263877 * 2
def baseEnd_3263877 : Nat := 1675937698154831799927209

theorem tailTrace_3263877 : CollatzResearch.WordTrace tailWord_3263877 prefixEnd_3263877 1675937698154831799927209 := by
  unfold tailWord_3263877
  simp only [CollatzResearch.WordTrace]
  refine ⟨119043373996538529657773885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79362249331025686438515923 119043373996538529657773885)
  ·
    refine ⟨44641265248701948621665207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119043373996538529657773885 44641265248701948621665207)
    ·
      refine ⟨66961897873052922932497811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44641265248701948621665207 66961897873052922932497811)
      ·
        refine ⟨100442846809579384398746717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66961897873052922932497811 100442846809579384398746717)
        ·
          refine ⟨37666067553592269149530019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100442846809579384398746717 37666067553592269149530019)
          ·
            refine ⟨56499101330388403724295029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37666067553592269149530019 56499101330388403724295029)
            ·
              refine ⟨5296790749723912849152659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56499101330388403724295029 5296790749723912849152659)
              ·
                refine ⟨7945186124585869273728989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296790749723912849152659 7945186124585869273728989)
                ·
                  refine ⟨2979444796719700977648371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7945186124585869273728989 2979444796719700977648371)
                  ·
                    refine ⟨4469167195079551466472557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979444796719700977648371 4469167195079551466472557)
                    ·
                      refine ⟨1675937698154831799927209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469167195079551466472557 1675937698154831799927209)
                      ·
                        rfl

theorem cell23_3263877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_3263877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263877 prefixEnd_3263877 := by exact prefixLift 3263877
  have htrace : WordTrace (prefixWord ++ tailWord_3263877) baseStart_3263877 baseEnd_3263877 := by
    simpa [prefixWord, tailWord_3263877, baseEnd_3263877] using wordTrace_append hprefix tailTrace_3263877
  have hstable : (prefixWord ++ tailWord_3263877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263877).length < 2 ^ (prefixWord ++ tailWord_3263877).sum := by decide
  have hdescent : baseEnd_3263877 < baseStart_3263877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263897 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_3263897 : Nat := 118140960795 + 3263897 * 2 ^ 59
def prefixEnd_3263897 : Nat := 4983230072969 + 3 ^ 40 * 3263897 * 2
def baseEnd_3263897 : Nat := 558649322589307240559039

theorem tailTrace_3263897 : CollatzResearch.WordTrace tailWord_3263897 prefixEnd_3263897 558649322589307240559039 := by
  unfold tailWord_3263897
  simp only [CollatzResearch.WordTrace]
  refine ⟨119044103456466073073501945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79362735637644048715667963 119044103456466073073501945)
  ·
    refine ⟨89283077592349554805126459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119044103456466073073501945 89283077592349554805126459)
    ·
      refine ⟨133924616388524332207689689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89283077592349554805126459 133924616388524332207689689)
      ·
        refine ⟨100443462291393249155767267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133924616388524332207689689 100443462291393249155767267)
        ·
          refine ⟨150665193437089873733650901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100443462291393249155767267 150665193437089873733650901)
          ·
            refine ⟨3531215471181793915632443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150665193437089873733650901 3531215471181793915632443)
            ·
              refine ⟨5296823206772690873448665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531215471181793915632443 5296823206772690873448665)
              ·
                refine ⟨3972617405079518155086499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5296823206772690873448665 3972617405079518155086499)
                ·
                  refine ⟨5958926107619277232629749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972617405079518155086499 5958926107619277232629749)
                  ·
                    refine ⟨558649322589307240559039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5958926107619277232629749 558649322589307240559039)
                    ·
                      rfl

theorem cell23_3263897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_3263897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263897 prefixEnd_3263897 := by exact prefixLift 3263897
  have htrace : WordTrace (prefixWord ++ tailWord_3263897) baseStart_3263897 baseEnd_3263897 := by
    simpa [prefixWord, tailWord_3263897, baseEnd_3263897] using wordTrace_append hprefix tailTrace_3263897
  have hstable : (prefixWord ++ tailWord_3263897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263897).length < 2 ^ (prefixWord ++ tailWord_3263897).sum := by decide
  have hdescent : baseEnd_3263897 < baseStart_3263897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263927 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 2, 4]
def baseStart_3263927 : Nat := 118140960795 + 3263927 * 2 ^ 59
def prefixEnd_3263927 : Nat := 4983230072969 + 3 ^ 40 * 3263927 * 2
def baseEnd_3263927 : Nat := 558654457395852201433993

theorem tailTrace_3263927 : CollatzResearch.WordTrace tailWord_3263927 prefixEnd_3263927 558654457395852201433993 := by
  unfold tailWord_3263927
  simp only [CollatzResearch.WordTrace]
  refine ⟨119045197646357388197094035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79363465097571592131396023 119045197646357388197094035)
  ·
    refine ⟨178567796469536082295641053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119045197646357388197094035 178567796469536082295641053)
    ·
      refine ⟨66962923676076030860865395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178567796469536082295641053 66962923676076030860865395)
      ·
        refine ⟨100444385514114046291298093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66962923676076030860865395 100444385514114046291298093)
        ·
          refine ⟨37666644567792767359236785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100444385514114046291298093 37666644567792767359236785)
          ·
            refine ⟨28249983425844575519427589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37666644567792767359236785 28249983425844575519427589)
            ·
              refine ⟨5296871892345857909892673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28249983425844575519427589 5296871892345857909892673)
              ·
                refine ⟨3972653919259393432419505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5296871892345857909892673 3972653919259393432419505)
                ·
                  refine ⟨2979490439444545074314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972653919259393432419505 2979490439444545074314629)
                  ·
                    refine ⟨558654457395852201433993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979490439444545074314629 558654457395852201433993)
                    ·
                      rfl

theorem cell23_3263927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_3263927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263927 prefixEnd_3263927 := by exact prefixLift 3263927
  have htrace : WordTrace (prefixWord ++ tailWord_3263927) baseStart_3263927 baseEnd_3263927 := by
    simpa [prefixWord, tailWord_3263927, baseEnd_3263927] using wordTrace_append hprefix tailTrace_3263927
  have hstable : (prefixWord ++ tailWord_3263927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263927).length < 2 ^ (prefixWord ++ tailWord_3263927).sum := by decide
  have hdescent : baseEnd_3263927 < baseStart_3263927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263934 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_3263934 : Nat := 118140960795 + 3263934 * 2 ^ 59
def prefixEnd_3263934 : Nat := 4983230072969 + 3 ^ 40 * 3263934 * 2
def baseEnd_3263934 : Nat := 1675966966552138076914447

theorem tailTrace_3263934 : CollatzResearch.WordTrace tailWord_3263934 prefixEnd_3263934 1675966966552138076914447 := by
  unfold tailWord_3263934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14880681619666503549074857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79363635304888018928399237 14880681619666503549074857)
  ·
    refine ⟨11160511214749877661806143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14880681619666503549074857 11160511214749877661806143)
    ·
      refine ⟨16740766822124816492709215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11160511214749877661806143 16740766822124816492709215)
      ·
        refine ⟨25111150233187224739063823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16740766822124816492709215 25111150233187224739063823)
        ·
          refine ⟨37666725349780837108595735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25111150233187224739063823 37666725349780837108595735)
          ·
            refine ⟨56500088024671255662893603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37666725349780837108595735 56500088024671255662893603)
            ·
              refine ⟨84750132037006883494340405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56500088024671255662893603 84750132037006883494340405)
              ·
                refine ⟨7945324878469395327594413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84750132037006883494340405 7945324878469395327594413)
                ·
                  refine ⟨2979496829426023247847905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7945324878469395327594413 2979496829426023247847905)
                  ·
                    refine ⟨2234622622069517435885929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979496829426023247847905 2234622622069517435885929)
                    ·
                      refine ⟨1675966966552138076914447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234622622069517435885929 1675966966552138076914447)
                      ·
                        rfl

theorem cell23_3263934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_3263934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263934 prefixEnd_3263934 := by exact prefixLift 3263934
  have htrace : WordTrace (prefixWord ++ tailWord_3263934) baseStart_3263934 baseEnd_3263934 := by
    simpa [prefixWord, tailWord_3263934, baseEnd_3263934] using wordTrace_append hprefix tailTrace_3263934
  have hstable : (prefixWord ++ tailWord_3263934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263934).length < 2 ^ (prefixWord ++ tailWord_3263934).sum := by decide
  have hdescent : baseEnd_3263934 < baseStart_3263934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263963 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_3263963 : Nat := 118140960795 + 3263963 * 2 ^ 59
def prefixEnd_3263963 : Nat := 4983230072969 + 3 ^ 40 * 3263963 * 2
def baseEnd_3263963 : Nat := 1675981857491118463451813

theorem tailTrace_3263963 : CollatzResearch.WordTrace tailWord_3263963 prefixEnd_3263963 1675981857491118463451813 := by
  unfold tailWord_3263963
  simp only [CollatzResearch.WordTrace]
  refine ⟨119046510674226966345404543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79364340449484644230269695 119046510674226966345404543)
  ·
    refine ⟨178569766011340449518106815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119046510674226966345404543 178569766011340449518106815)
    ·
      refine ⟨267854649017010674277160223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178569766011340449518106815 267854649017010674277160223)
      ·
        refine ⟨401781973525516011415740335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267854649017010674277160223 401781973525516011415740335)
        ·
          refine ⟨602672960288274017123610503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401781973525516011415740335 602672960288274017123610503)
          ·
            refine ⟨904009440432411025685415755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602672960288274017123610503 904009440432411025685415755)
            ·
              refine ⟨1356014160648616538528123633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904009440432411025685415755 1356014160648616538528123633)
              ·
                refine ⟨1017010620486462403896092725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356014160648616538528123633 1017010620486462403896092725)
                ·
                  refine ⟨95344745670605850365258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1017010620486462403896092725 95344745670605850365258693)
                  ·
                    refine ⟨17877139813238596943486005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95344745670605850365258693 17877139813238596943486005)
                    ·
                      refine ⟨1675981857491118463451813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17877139813238596943486005 1675981857491118463451813)
                      ·
                        rfl

theorem cell23_3263963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_3263963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263963 prefixEnd_3263963 := by exact prefixLift 3263963
  have htrace : WordTrace (prefixWord ++ tailWord_3263963) baseStart_3263963 baseEnd_3263963 := by
    simpa [prefixWord, tailWord_3263963, baseEnd_3263963] using wordTrace_append hprefix tailTrace_3263963
  have hstable : (prefixWord ++ tailWord_3263963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263963).length < 2 ^ (prefixWord ++ tailWord_3263963).sum := by decide
  have hdescent : baseEnd_3263963 < baseStart_3263963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263967 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 3]
def baseStart_3263967 : Nat := 118140960795 + 3263967 * 2 ^ 59
def prefixEnd_3263967 : Nat := 4983230072969 + 3 ^ 40 * 3263967 * 2
def baseEnd_3263967 : Nat := 1675983911413736447801795

theorem tailTrace_3263967 : CollatzResearch.WordTrace tailWord_3263967 prefixEnd_3263967 1675983911413736447801795 := by
  unfold tailWord_3263967
  simp only [CollatzResearch.WordTrace]
  refine ⟨119046656566212475028550155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79364437710808316685700103 119046656566212475028550155)
  ·
    refine ⟨178569984849318712542825233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119046656566212475028550155 178569984849318712542825233)
    ·
      refine ⟨133927488636989034407118925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178569984849318712542825233 133927488636989034407118925)
      ·
        refine ⟨50222808238870887902669597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133927488636989034407118925 50222808238870887902669597)
        ·
          refine ⟨18833553089576582963501099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50222808238870887902669597 18833553089576582963501099)
          ·
            refine ⟨28250329634364874445251649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18833553089576582963501099 28250329634364874445251649)
            ·
              refine ⟨21187747225773655833938737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28250329634364874445251649 21187747225773655833938737)
              ·
                refine ⟨15890810419330241875454053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21187747225773655833938737 15890810419330241875454053)
                ·
                  refine ⟨2979526953624420351647635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15890810419330241875454053 2979526953624420351647635)
                  ·
                    refine ⟨4469290430436630527471453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979526953624420351647635 4469290430436630527471453)
                    ·
                      refine ⟨1675983911413736447801795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469290430436630527471453 1675983911413736447801795)
                      ·
                        rfl

theorem cell23_3263967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_3263967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263967 prefixEnd_3263967 := by exact prefixLift 3263967
  have htrace : WordTrace (prefixWord ++ tailWord_3263967) baseStart_3263967 baseEnd_3263967 := by
    simpa [prefixWord, tailWord_3263967, baseEnd_3263967] using wordTrace_append hprefix tailTrace_3263967
  have hstable : (prefixWord ++ tailWord_3263967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263967).length < 2 ^ (prefixWord ++ tailWord_3263967).sum := by decide
  have hdescent : baseEnd_3263967 < baseStart_3263967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263971 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 1, 2, 3]
def baseStart_3263971 : Nat := 118140960795 + 3263971 * 2 ^ 59
def prefixEnd_3263971 : Nat := 4983230072969 + 3 ^ 40 * 3263971 * 2
def baseEnd_3263971 : Nat := 1675985965336354432151777

theorem tailTrace_3263971 : CollatzResearch.WordTrace tailWord_3263971 prefixEnd_3263971 1675985965336354432151777 := by
  unfold tailWord_3263971
  simp only [CollatzResearch.WordTrace]
  refine ⟨119046802458197983711695767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79364534972131989141130511 119046802458197983711695767)
  ·
    refine ⟨178570203687296975567543651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119046802458197983711695767 178570203687296975567543651)
    ·
      refine ⟨267855305530945463351315477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178570203687296975567543651 267855305530945463351315477)
      ·
        refine ⟨12555717446763068594592913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267855305530945463351315477 12555717446763068594592913)
        ·
          refine ⟨9416788085072301445944685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12555717446763068594592913 9416788085072301445944685)
          ·
            refine ⟨3531295531902113042229257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9416788085072301445944685 3531295531902113042229257)
            ·
              refine ⟨2648471648926584781671943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531295531902113042229257 2648471648926584781671943)
              ·
                refine ⟨3972707473389877172507915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648471648926584781671943 3972707473389877172507915)
                ·
                  refine ⟨5959061210084815758761873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972707473389877172507915 5959061210084815758761873)
                  ·
                    refine ⟨4469295907563611819071405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959061210084815758761873 4469295907563611819071405)
                    ·
                      refine ⟨1675985965336354432151777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469295907563611819071405 1675985965336354432151777)
                      ·
                        rfl

theorem cell23_3263971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_3263971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263971 prefixEnd_3263971 := by exact prefixLift 3263971
  have htrace : WordTrace (prefixWord ++ tailWord_3263971) baseStart_3263971 baseEnd_3263971 := by
    simpa [prefixWord, tailWord_3263971, baseEnd_3263971] using wordTrace_append hprefix tailTrace_3263971
  have hstable : (prefixWord ++ tailWord_3263971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263971).length < 2 ^ (prefixWord ++ tailWord_3263971).sum := by decide
  have hdescent : baseEnd_3263971 < baseStart_3263971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263984 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3]
def baseStart_3263984 : Nat := 118140960795 + 3263984 * 2 ^ 59
def prefixEnd_3263984 : Nat := 4983230072969 + 3 ^ 40 * 3263984 * 2
def baseEnd_3263984 : Nat := 1675992640584862881289217

theorem tailTrace_3263984 : CollatzResearch.WordTrace tailWord_3263984 prefixEnd_3263984 1675992640584862881289217 := by
  unfold tailWord_3263984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59523638303575443465959503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79364851071433924621279337 59523638303575443465959503)
  ·
    refine ⟨89285457455363165198939255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59523638303575443465959503 89285457455363165198939255)
    ·
      refine ⟨133928186183044747798408883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89285457455363165198939255 133928186183044747798408883)
      ·
        refine ⟨200892279274567121697613325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133928186183044747798408883 200892279274567121697613325)
        ·
          refine ⟨75334604727962670636604997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200892279274567121697613325 75334604727962670636604997)
          ·
            refine ⟨14125238386493000744363437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75334604727962670636604997 14125238386493000744363437)
            ·
              refine ⟨5296964394934875279136289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14125238386493000744363437 5296964394934875279136289)
              ·
                refine ⟨3972723296201156459352217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5296964394934875279136289 3972723296201156459352217)
                ·
                  refine ⟨2979542472150867344514163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972723296201156459352217 2979542472150867344514163)
                  ·
                    refine ⟨4469313708226301016771245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2979542472150867344514163 4469313708226301016771245)
                    ·
                      refine ⟨1675992640584862881289217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469313708226301016771245 1675992640584862881289217)
                      ·
                        rfl

theorem cell23_3263984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_3263984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263984 prefixEnd_3263984 := by exact prefixLift 3263984
  have htrace : WordTrace (prefixWord ++ tailWord_3263984) baseStart_3263984 baseEnd_3263984 := by
    simpa [prefixWord, tailWord_3263984, baseEnd_3263984] using wordTrace_append hprefix tailTrace_3263984
  have hstable : (prefixWord ++ tailWord_3263984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263984).length < 2 ^ (prefixWord ++ tailWord_3263984).sum := by decide
  have hdescent : baseEnd_3263984 < baseStart_3263984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3263998 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3263998 : Nat := 118140960795 + 3263998 * 2 ^ 59
def prefixEnd_3263998 : Nat := 4983230072969 + 3 ^ 40 * 3263998 * 2
def baseEnd_3263998 : Nat := 1675999829314025826514153

theorem tailTrace_3263998 : CollatzResearch.WordTrace tailWord_3263998 prefixEnd_3263998 1675999829314025826514153 := by
  unfold tailWord_3263998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14880973403637520915366081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79365191486066778215285765 14880973403637520915366081)
  ·
    refine ⟨11160730052728140686524561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14880973403637520915366081 11160730052728140686524561)
    ·
      refine ⟨8370547539546105514893421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11160730052728140686524561 8370547539546105514893421)
      ·
        refine ⟨3138955327329789568085033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8370547539546105514893421 3138955327329789568085033)
        ·
          refine ⟨2354216495497342176063775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3138955327329789568085033 2354216495497342176063775)
          ·
            refine ⟨3531324743246013264095663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354216495497342176063775 3531324743246013264095663)
            ·
              refine ⟨5296987114869019896143495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531324743246013264095663 5296987114869019896143495)
              ·
                refine ⟨7945480672303529844215243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296987114869019896143495 7945480672303529844215243)
                ·
                  refine ⟨11918221008455294766322865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945480672303529844215243 11918221008455294766322865)
                  ·
                    refine ⟨8938665756341471074742149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11918221008455294766322865 8938665756341471074742149)
                    ·
                      refine ⟨1675999829314025826514153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8938665756341471074742149 1675999829314025826514153)
                      ·
                        rfl

theorem cell23_3263998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3263998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3263998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3263998 prefixEnd_3263998 := by exact prefixLift 3263998
  have htrace : WordTrace (prefixWord ++ tailWord_3263998) baseStart_3263998 baseEnd_3263998 := by
    simpa [prefixWord, tailWord_3263998, baseEnd_3263998] using wordTrace_append hprefix tailTrace_3263998
  have hstable : (prefixWord ++ tailWord_3263998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3263998).length < 2 ^ (prefixWord ++ tailWord_3263998).sum := by decide
  have hdescent : baseEnd_3263998 < baseStart_3263998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3263998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264001 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_3264001 : Nat := 118140960795 + 3264001 * 2 ^ 59
def prefixEnd_3264001 : Nat := 4983230072969 + 3 ^ 40 * 3264001 * 2
def baseEnd_3264001 : Nat := 1676001369755989314776639

theorem tailTrace_3264001 : CollatzResearch.WordTrace tailWord_3264001 prefixEnd_3264001 1676001369755989314776639 := by
  unfold tailWord_3264001
  simp only [CollatzResearch.WordTrace]
  refine ⟨119047896648089298835287857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79365264432059532556858571 119047896648089298835287857)
  ·
    refine ⟨89285922486066974126465893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119047896648089298835287857 89285922486066974126465893)
    ·
      refine ⟨16741110466137557648712355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89285922486066974126465893 16741110466137557648712355)
      ·
        refine ⟨25111665699206336473068533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16741110466137557648712355 25111665699206336473068533)
        ·
          refine ⟨2354218659300594044350175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25111665699206336473068533 2354218659300594044350175)
          ·
            refine ⟨3531327988950891066525263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354218659300594044350175 3531327988950891066525263)
            ·
              refine ⟨5296991983426336599787895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531327988950891066525263 5296991983426336599787895)
              ·
                refine ⟨7945487975139504899681843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296991983426336599787895 7945487975139504899681843)
                ·
                  refine ⟨11918231962709257349522765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945487975139504899681843 11918231962709257349522765)
                  ·
                    refine ⟨4469336986015971506071037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11918231962709257349522765 4469336986015971506071037)
                    ·
                      refine ⟨1676001369755989314776639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469336986015971506071037 1676001369755989314776639)
                      ·
                        rfl

theorem cell23_3264001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_3264001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264001 prefixEnd_3264001 := by exact prefixLift 3264001
  have htrace : WordTrace (prefixWord ++ tailWord_3264001) baseStart_3264001 baseEnd_3264001 := by
    simpa [prefixWord, tailWord_3264001, baseEnd_3264001] using wordTrace_append hprefix tailTrace_3264001
  have hstable : (prefixWord ++ tailWord_3264001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264001).length < 2 ^ (prefixWord ++ tailWord_3264001).sum := by decide
  have hdescent : baseEnd_3264001 < baseStart_3264001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264011 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 1, 3, 2]
def baseStart_3264011 : Nat := 118140960795 + 3264011 * 2 ^ 59
def prefixEnd_3264011 : Nat := 4983230072969 + 3 ^ 40 * 3264011 * 2
def baseEnd_3264011 : Nat := 1676006504562534275651593

theorem tailTrace_3264011 : CollatzResearch.WordTrace tailWord_3264011 prefixEnd_3264011 1676006504562534275651593 := by
  unfold tailWord_3264011
  simp only [CollatzResearch.WordTrace]
  refine ⟨119048261378053070543151887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79365507585368713695434591 119048261378053070543151887)
  ·
    refine ⟨178572392067079605814727831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119048261378053070543151887 178572392067079605814727831)
    ·
      refine ⟨267858588100619408722091747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178572392067079605814727831 267858588100619408722091747)
      ·
        refine ⟨401787882150929113083137621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267858588100619408722091747 401787882150929113083137621)
        ·
          refine ⟨4708451743956200543943019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 401787882150929113083137621 4708451743956200543943019)
          ·
            refine ⟨7062677615934300815914529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708451743956200543943019 7062677615934300815914529)
            ·
              refine ⟨5297008211950725611935897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7062677615934300815914529 5297008211950725611935897)
              ·
                refine ⟨3972756158963044208951923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297008211950725611935897 3972756158963044208951923)
                ·
                  refine ⟨5959134238444566313427885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972756158963044208951923 5959134238444566313427885)
                  ·
                    refine ⟨2234675339416712367535457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5959134238444566313427885 2234675339416712367535457)
                    ·
                      refine ⟨1676006504562534275651593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234675339416712367535457 1676006504562534275651593)
                      ·
                        rfl

theorem cell23_3264011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3, 2].length) (baseStart_3264011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264011 prefixEnd_3264011 := by exact prefixLift 3264011
  have htrace : WordTrace (prefixWord ++ tailWord_3264011) baseStart_3264011 baseEnd_3264011 := by
    simpa [prefixWord, tailWord_3264011, baseEnd_3264011] using wordTrace_append hprefix tailTrace_3264011
  have hstable : (prefixWord ++ tailWord_3264011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264011).length < 2 ^ (prefixWord ++ tailWord_3264011).sum := by decide
  have hdescent : baseEnd_3264011 < baseStart_3264011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264097 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_3264097 : Nat := 118140960795 + 3264097 * 2 ^ 59
def prefixEnd_3264097 : Nat := 4983230072969 + 3 ^ 40 * 3264097 * 2
def baseEnd_3264097 : Nat := 1676050663898820939176197

theorem tailTrace_3264097 : CollatzResearch.WordTrace tailWord_3264097 prefixEnd_3264097 1676050663898820939176197 := by
  unfold tailWord_3264097
  simp only [CollatzResearch.WordTrace]
  refine ⟨119051398055741507230782545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79367598703827671487188363 119051398055741507230782545)
  ·
    refine ⟨89288548541806130423086909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119051398055741507230782545 89288548541806130423086909)
    ·
      refine ⟨33483205703177298908657591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89288548541806130423086909 33483205703177298908657591)
      ·
        refine ⟨50224808554765948362986387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33483205703177298908657591 50224808554765948362986387)
        ·
          refine ⟨75337212832148922544479581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50224808554765948362986387 75337212832148922544479581)
          ·
            refine ⟨28251454812055845954179843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75337212832148922544479581 28251454812055845954179843)
            ·
              refine ⟨42377182218083768931269765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28251454812055845954179843 42377182218083768931269765)
              ·
                refine ⟨7945721665890706674613081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42377182218083768931269765 7945721665890706674613081)
                ·
                  refine ⟨5959291249418030005959811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7945721665890706674613081 5959291249418030005959811)
                  ·
                    refine ⟨8938936874127045008939717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5959291249418030005959811 8938936874127045008939717)
                    ·
                      refine ⟨1676050663898820939176197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8938936874127045008939717 1676050663898820939176197)
                      ·
                        rfl

theorem cell23_3264097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_3264097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264097 prefixEnd_3264097 := by exact prefixLift 3264097
  have htrace : WordTrace (prefixWord ++ tailWord_3264097) baseStart_3264097 baseEnd_3264097 := by
    simpa [prefixWord, tailWord_3264097, baseEnd_3264097] using wordTrace_append hprefix tailTrace_3264097
  have hstable : (prefixWord ++ tailWord_3264097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264097).length < 2 ^ (prefixWord ++ tailWord_3264097).sum := by decide
  have hdescent : baseEnd_3264097 < baseStart_3264097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264114 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3264114 : Nat := 118140960795 + 3264114 * 2 ^ 59
def prefixEnd_3264114 : Nat := 4983230072969 + 3 ^ 40 * 3264114 * 2
def baseEnd_3264114 : Nat := 1676059393069947372663619

theorem tailTrace_3264114 : CollatzResearch.WordTrace tailWord_3264114 prefixEnd_3264114 1676059393069947372663619 := by
  unfold tailWord_3264114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763004524169979783537849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79368012064453279422767597 29763004524169979783537849)
  ·
    refine ⟨22322253393127484837653387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29763004524169979783537849 22322253393127484837653387)
    ·
      refine ⟨33483380089691227256480081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22322253393127484837653387 33483380089691227256480081)
      ·
        refine ⟨25112535067268420442360061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33483380089691227256480081 25112535067268420442360061)
        ·
          refine ⟨9417200650225657665885023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25112535067268420442360061 9417200650225657665885023)
          ·
            refine ⟨14125800975338486498827535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9417200650225657665885023 14125800975338486498827535)
            ·
              refine ⟨21188701463007729748241303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14125800975338486498827535 21188701463007729748241303)
              ·
                refine ⟨31783052194511594622361955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21188701463007729748241303 31783052194511594622361955)
                ·
                  refine ⟨47674578291767391933542933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31783052194511594622361955 47674578291767391933542933)
                  ·
                    refine ⟨2234745857426596496884825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47674578291767391933542933 2234745857426596496884825)
                    ·
                      refine ⟨1676059393069947372663619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234745857426596496884825 1676059393069947372663619)
                      ·
                        rfl

theorem cell23_3264114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3264114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264114 prefixEnd_3264114 := by exact prefixLift 3264114
  have htrace : WordTrace (prefixWord ++ tailWord_3264114) baseStart_3264114 baseEnd_3264114 := by
    simpa [prefixWord, tailWord_3264114, baseEnd_3264114] using wordTrace_append hprefix tailTrace_3264114
  have hstable : (prefixWord ++ tailWord_3264114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264114).length < 2 ^ (prefixWord ++ tailWord_3264114).sum := by decide
  have hdescent : baseEnd_3264114 < baseStart_3264114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264158 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3264158 : Nat := 118140960795 + 3264158 * 2 ^ 59
def prefixEnd_3264158 : Nat := 4983230072969 + 3 ^ 40 * 3264158 * 2
def baseEnd_3264158 : Nat := 558693995406248400171139

theorem tailTrace_3264158 : CollatzResearch.WordTrace tailWord_3264158 prefixEnd_3264158 558693995406248400171139 := by
  unfold tailWord_3264158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14881702863565064331094141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79369081939013676432502085 14881702863565064331094141)
  ·
    refine ⟨5580638573836899124160303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14881702863565064331094141 5580638573836899124160303)
    ·
      refine ⟨8370957860755348686240455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5580638573836899124160303 8370957860755348686240455)
      ·
        refine ⟨12556436791133023029360683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370957860755348686240455 12556436791133023029360683)
        ·
          refine ⟨18834655186699534544041025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556436791133023029360683 18834655186699534544041025)
          ·
            refine ⟨14125991390024650908030769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18834655186699534544041025 14125991390024650908030769)
            ·
              refine ⟨10594493542518488181023077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14125991390024650908030769 10594493542518488181023077)
              ·
                refine ⟨1986467539222216533941827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10594493542518488181023077 1986467539222216533941827)
                ·
                  refine ⟨2979701308833324800912741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986467539222216533941827 2979701308833324800912741)
                  ·
                    refine ⟨558693995406248400171139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979701308833324800912741 558693995406248400171139)
                    ·
                      rfl

theorem cell23_3264158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3264158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264158 prefixEnd_3264158 := by exact prefixLift 3264158
  have htrace : WordTrace (prefixWord ++ tailWord_3264158) baseStart_3264158 baseEnd_3264158 := by
    simpa [prefixWord, tailWord_3264158, baseEnd_3264158] using wordTrace_append hprefix tailTrace_3264158
  have hstable : (prefixWord ++ tailWord_3264158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264158).length < 2 ^ (prefixWord ++ tailWord_3264158).sum := by decide
  have hdescent : baseEnd_3264158 < baseStart_3264158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264187 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4]
def baseStart_3264187 : Nat := 118140960795 + 3264187 * 2 ^ 59
def prefixEnd_3264187 : Nat := 4983230072969 + 3 ^ 40 * 3264187 * 2
def baseEnd_3264187 : Nat := 1676096877157725587050783

theorem tailTrace_3264187 : CollatzResearch.WordTrace tailWord_3264187 prefixEnd_3264187 1676096877157725587050783 := by
  unfold tailWord_3264187
  simp only [CollatzResearch.WordTrace]
  refine ⟨119054680625415452601558815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79369787083610301734372543 119054680625415452601558815)
  ·
    refine ⟨178582020938123178902338223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119054680625415452601558815 178582020938123178902338223)
    ·
      refine ⟨267873031407184768353507335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178582020938123178902338223 267873031407184768353507335)
      ·
        refine ⟨401809547110777152530261003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267873031407184768353507335 401809547110777152530261003)
        ·
          refine ⟨602714320666165728795391505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401809547110777152530261003 602714320666165728795391505)
          ·
            refine ⟨452035740499624296596543629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602714320666165728795391505 452035740499624296596543629)
            ·
              refine ⟨169513402687359111223703861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452035740499624296596543629 169513402687359111223703861)
              ·
                refine ⟨15891881501939916677222237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169513402687359111223703861 15891881501939916677222237)
                ·
                  refine ⟨5959455563227468753958339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15891881501939916677222237 5959455563227468753958339)
                  ·
                    refine ⟨8939183344841203130937509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5959455563227468753958339 8939183344841203130937509)
                    ·
                      refine ⟨1676096877157725587050783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8939183344841203130937509 1676096877157725587050783)
                      ·
                        rfl

theorem cell23_3264187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4].length) (baseStart_3264187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264187 prefixEnd_3264187 := by exact prefixLift 3264187
  have htrace : WordTrace (prefixWord ++ tailWord_3264187) baseStart_3264187 baseEnd_3264187 := by
    simpa [prefixWord, tailWord_3264187, baseEnd_3264187] using wordTrace_append hprefix tailTrace_3264187
  have hstable : (prefixWord ++ tailWord_3264187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264187).length < 2 ^ (prefixWord ++ tailWord_3264187).sum := by decide
  have hdescent : baseEnd_3264187 < baseStart_3264187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264217 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3264217 : Nat := 118140960795 + 3264217 * 2 ^ 59
def prefixEnd_3264217 : Nat := 4983230072969 + 3 ^ 40 * 3264217 * 2
def baseEnd_3264217 : Nat := 1676112281577360469675645

theorem tailTrace_3264217 : CollatzResearch.WordTrace tailWord_3264217 prefixEnd_3264217 1676112281577360469675645 := by
  unfold tailWord_3264217
  simp only [CollatzResearch.WordTrace]
  refine ⟨119055774815306767725150905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79370516543537845150100603 119055774815306767725150905)
  ·
    refine ⟨89291831111480075793863179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119055774815306767725150905 89291831111480075793863179)
    ·
      refine ⟨133937746667220113690794769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89291831111480075793863179 133937746667220113690794769)
      ·
        refine ⟨100453310000415085268096077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133937746667220113690794769 100453310000415085268096077)
        ·
          refine ⟨37669991250155656975536029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100453310000415085268096077 37669991250155656975536029)
          ·
            refine ⟨14126246718808371365826011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37669991250155656975536029 14126246718808371365826011)
            ·
              refine ⟨21189370078212557048739017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14126246718808371365826011 21189370078212557048739017)
              ·
                refine ⟨15892027558659417786554263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21189370078212557048739017 15892027558659417786554263)
                ·
                  refine ⟨23838041337989126679831395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892027558659417786554263 23838041337989126679831395)
                  ·
                    refine ⟨35757062006983690019747093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23838041337989126679831395 35757062006983690019747093)
                    ·
                      refine ⟨1676112281577360469675645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35757062006983690019747093 1676112281577360469675645)
                      ·
                        rfl

theorem cell23_3264217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3264217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264217 prefixEnd_3264217 := by exact prefixLift 3264217
  have htrace : WordTrace (prefixWord ++ tailWord_3264217) baseStart_3264217 baseEnd_3264217 := by
    simpa [prefixWord, tailWord_3264217, baseEnd_3264217] using wordTrace_append hprefix tailTrace_3264217
  have hstable : (prefixWord ++ tailWord_3264217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264217).length < 2 ^ (prefixWord ++ tailWord_3264217).sum := by decide
  have hdescent : baseEnd_3264217 < baseStart_3264217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264241 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_3264241 : Nat := 118140960795 + 3264241 * 2 ^ 59
def prefixEnd_3264241 : Nat := 4983230072969 + 3 ^ 40 * 3264241 * 2
def baseEnd_3264241 : Nat := 1676124605113068375775535

theorem tailTrace_3264241 : CollatzResearch.WordTrace tailWord_3264241 prefixEnd_3264241 1676124605113068375775535 := by
  unfold tailWord_3264241
  simp only [CollatzResearch.WordTrace]
  refine ⟨119056650167219819824024577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79371100111479879882683051 119056650167219819824024577)
  ·
    refine ⟨89292487625414864868018433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119056650167219819824024577 89292487625414864868018433)
    ·
      refine ⟨66969365719061148651013825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89292487625414864868018433 66969365719061148651013825)
      ·
        refine ⟨50227024289295861488260369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66969365719061148651013825 50227024289295861488260369)
        ·
          refine ⟨37670268216971896116195277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50227024289295861488260369 37670268216971896116195277)
          ·
            refine ⟨14126350581364461043573229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37670268216971896116195277 14126350581364461043573229)
            ·
              refine ⟨5297381468011672891339961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14126350581364461043573229 5297381468011672891339961)
              ·
                refine ⟨3973036101008754668504971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297381468011672891339961 3973036101008754668504971)
                ·
                  refine ⟨5959554151513132002757457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973036101008754668504971 5959554151513132002757457)
                  ·
                    refine ⟨4469665613634849002068093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959554151513132002757457 4469665613634849002068093)
                    ·
                      refine ⟨1676124605113068375775535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4469665613634849002068093 1676124605113068375775535)
                      ·
                        rfl

theorem cell23_3264241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_3264241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264241 prefixEnd_3264241 := by exact prefixLift 3264241
  have htrace : WordTrace (prefixWord ++ tailWord_3264241) baseStart_3264241 baseEnd_3264241 := by
    simpa [prefixWord, tailWord_3264241, baseEnd_3264241] using wordTrace_append hprefix tailTrace_3264241
  have hstable : (prefixWord ++ tailWord_3264241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264241).length < 2 ^ (prefixWord ++ tailWord_3264241).sum := by decide
  have hdescent : baseEnd_3264241 < baseStart_3264241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264267 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_3264267 : Nat := 118140960795 + 3264267 * 2 ^ 59
def prefixEnd_3264267 : Nat := 4983230072969 + 3 ^ 40 * 3264267 * 2
def baseEnd_3264267 : Nat := 1676137955610085274050415

theorem tailTrace_3264267 : CollatzResearch.WordTrace tailWord_3264267 prefixEnd_3264267 1676137955610085274050415 := by
  unfold tailWord_3264267
  simp only [CollatzResearch.WordTrace]
  refine ⟨119057598465125626264471055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79371732310083750842980703 119057598465125626264471055)
  ·
    refine ⟨178586397697688439396706583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119057598465125626264471055 178586397697688439396706583)
    ·
      refine ⟨267879596546532659095059875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178586397697688439396706583 267879596546532659095059875)
      ·
        refine ⟨401819394819798988642589813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267879596546532659095059875 401819394819798988642589813)
        ·
          refine ⟨37670568264356155185242795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 401819394819798988642589813 37670568264356155185242795)
          ·
            refine ⟨56505852396534232777864193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37670568264356155185242795 56505852396534232777864193)
            ·
              refine ⟨42379389297400674583398145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56505852396534232777864193 42379389297400674583398145)
              ·
                refine ⟨31784541973050505937548609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42379389297400674583398145 31784541973050505937548609)
                ·
                  refine ⟨23838406479787879453161457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31784541973050505937548609 23838406479787879453161457)
                  ·
                    refine ⟨17878804859840909589871093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23838406479787879453161457 17878804859840909589871093)
                    ·
                      refine ⟨1676137955610085274050415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17878804859840909589871093 1676137955610085274050415)
                      ·
                        rfl

theorem cell23_3264267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_3264267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264267 prefixEnd_3264267 := by exact prefixLift 3264267
  have htrace : WordTrace (prefixWord ++ tailWord_3264267) baseStart_3264267 baseEnd_3264267 := by
    simpa [prefixWord, tailWord_3264267, baseEnd_3264267] using wordTrace_append hprefix tailTrace_3264267
  have hstable : (prefixWord ++ tailWord_3264267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264267).length < 2 ^ (prefixWord ++ tailWord_3264267).sum := by decide
  have hdescent : baseEnd_3264267 < baseStart_3264267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264328 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_3264328 : Nat := 118140960795 + 3264328 * 2 ^ 59
def prefixEnd_3264328 : Nat := 4983230072969 + 3 ^ 40 * 3264328 * 2
def baseEnd_3264328 : Nat := 1676169277930009535387635

theorem tailTrace_3264328 : CollatzResearch.WordTrace tailWord_3264328 prefixEnd_3264328 1676169277930009535387635 := by
  unfold tailWord_3264328
  simp only [CollatzResearch.WordTrace]
  refine ⟨59529911658952316841220819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79373215545269755788294425 59529911658952316841220819)
  ·
    refine ⟨89294867488428475261831229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59529911658952316841220819 89294867488428475261831229)
    ·
      refine ⟨33485575308160678223186711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89294867488428475261831229 33485575308160678223186711)
      ·
        refine ⟨50228362962241017334780067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33485575308160678223186711 50228362962241017334780067)
        ·
          refine ⟨75342544443361526002170101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50228362962241017334780067 75342544443361526002170101)
          ·
            refine ⟨7063363541565143062703447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75342544443361526002170101 7063363541565143062703447)
            ·
              refine ⟨10595045312347714594055171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063363541565143062703447 10595045312347714594055171)
              ·
                refine ⟨15892567968521571891082757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595045312347714594055171 15892567968521571891082757)
                ·
                  refine ⟨2979856494097794729578017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15892567968521571891082757 2979856494097794729578017)
                  ·
                    refine ⟨2234892370573346047183513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979856494097794729578017 2234892370573346047183513)
                    ·
                      refine ⟨1676169277930009535387635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234892370573346047183513 1676169277930009535387635)
                      ·
                        rfl

theorem cell23_3264328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_3264328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264328 prefixEnd_3264328 := by exact prefixLift 3264328
  have htrace : WordTrace (prefixWord ++ tailWord_3264328) baseStart_3264328 baseEnd_3264328 := by
    simpa [prefixWord, tailWord_3264328, baseEnd_3264328] using wordTrace_append hprefix tailTrace_3264328
  have hstable : (prefixWord ++ tailWord_3264328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264328).length < 2 ^ (prefixWord ++ tailWord_3264328).sum := by decide
  have hdescent : baseEnd_3264328 < baseStart_3264328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264345 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 2, 2, 2]
def baseStart_3264345 : Nat := 118140960795 + 3264345 * 2 ^ 59
def prefixEnd_3264345 : Nat := 4983230072969 + 3 ^ 40 * 3264345 * 2
def baseEnd_3264345 : Nat := 1676178007101135968875057

theorem tailTrace_3264345 : CollatzResearch.WordTrace tailWord_3264345 prefixEnd_3264345 1676178007101135968875057 := by
  unfold tailWord_3264345
  simp only [CollatzResearch.WordTrace]
  refine ⟨119060443358843045585810489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79373628905895363723873659 119060443358843045585810489)
  ·
    refine ⟨89295332519132284189357867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119060443358843045585810489 89295332519132284189357867)
    ·
      refine ⟨133942998778698426284036801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89295332519132284189357867 133942998778698426284036801)
      ·
        refine ⟨100457249084023819713027601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133942998778698426284036801 100457249084023819713027601)
        ·
          refine ⟨75342936813017864784770701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100457249084023819713027601 75342936813017864784770701)
          ·
            refine ⟨28253601304881699294289013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75342936813017864784770701 28253601304881699294289013)
            ·
              refine ⟨2648775122332659308839595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28253601304881699294289013 2648775122332659308839595)
              ·
                refine ⟨3973162683498988963259393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648775122332659308839595 3973162683498988963259393)
                ·
                  refine ⟨2979872012624241722444545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3973162683498988963259393 2979872012624241722444545)
                  ·
                    refine ⟨2234904009468181291833409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2979872012624241722444545 2234904009468181291833409)
                    ·
                      refine ⟨1676178007101135968875057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234904009468181291833409 1676178007101135968875057)
                      ·
                        rfl

theorem cell23_3264345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_3264345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264345 prefixEnd_3264345 := by exact prefixLift 3264345
  have htrace : WordTrace (prefixWord ++ tailWord_3264345) baseStart_3264345 baseEnd_3264345 := by
    simpa [prefixWord, tailWord_3264345, baseEnd_3264345] using wordTrace_append hprefix tailTrace_3264345
  have hstable : (prefixWord ++ tailWord_3264345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264345).length < 2 ^ (prefixWord ++ tailWord_3264345).sum := by decide
  have hdescent : baseEnd_3264345 < baseStart_3264345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264364 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_3264364 : Nat := 118140960795 + 3264364 * 2 ^ 59
def prefixEnd_3264364 : Nat := 4983230072969 + 3 ^ 40 * 3264364 * 2
def baseEnd_3264364 : Nat := 558729254411190464845823

theorem tailTrace_3264364 : CollatzResearch.WordTrace tailWord_3264364 prefixEnd_3264364 558729254411190464845823 := by
  unfold tailWord_3264364
  simp only [CollatzResearch.WordTrace]
  refine ⟨59530568172887105915376073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79374090897182807887168097 59530568172887105915376073)
  ·
    refine ⟨44647926129665329436532055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59530568172887105915376073 44647926129665329436532055)
    ·
      refine ⟨66971889194497994154798083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44647926129665329436532055 66971889194497994154798083)
      ·
        refine ⟨100457833791746991232197125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66971889194497994154798083 100457833791746991232197125)
        ·
          refine ⟨18835843835952560856036961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100457833791746991232197125 18835843835952560856036961)
          ·
            refine ⟨14126882876964420642027721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18835843835952560856036961 14126882876964420642027721)
            ·
              refine ⟨10595162157723315481520791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14126882876964420642027721 10595162157723315481520791)
              ·
                refine ⟨15892743236584973222281187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595162157723315481520791 15892743236584973222281187)
                ·
                  refine ⟨23839114854877459833421781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892743236584973222281187 23839114854877459833421781)
                  ·
                    refine ⟨558729254411190464845823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23839114854877459833421781 558729254411190464845823)
                    ·
                      rfl

theorem cell23_3264364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_3264364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264364 prefixEnd_3264364 := by exact prefixLift 3264364
  have htrace : WordTrace (prefixWord ++ tailWord_3264364) baseStart_3264364 baseEnd_3264364 := by
    simpa [prefixWord, tailWord_3264364, baseEnd_3264364] using wordTrace_append hprefix tailTrace_3264364
  have hstable : (prefixWord ++ tailWord_3264364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264364).length < 2 ^ (prefixWord ++ tailWord_3264364).sum := by decide
  have hdescent : baseEnd_3264364 < baseStart_3264364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264385 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 7]
def baseStart_3264385 : Nat := 118140960795 + 3264385 * 2 ^ 59
def prefixEnd_3264385 : Nat := 4983230072969 + 3 ^ 40 * 3264385 * 2
def baseEnd_3264385 : Nat := 186244282925257312486097

theorem tailTrace_3264385 : CollatzResearch.WordTrace tailWord_3264385 prefixEnd_3264385 186244282925257312486097 := by
  unfold tailWord_3264385
  simp only [CollatzResearch.WordTrace]
  refine ⟨119061902278698132417266609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79374601519132088278177739 119061902278698132417266609)
  ·
    refine ⟨89296426709023599312949957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119061902278698132417266609 89296426709023599312949957)
    ·
      refine ⟨16743080007941924871178117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89296426709023599312949957 16743080007941924871178117)
      ·
        refine ⟨3139327501489110913345897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16743080007941924871178117 3139327501489110913345897)
        ·
          refine ⟨2354495626116833185009423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139327501489110913345897 2354495626116833185009423)
          ·
            refine ⟨3531743439175249777514135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354495626116833185009423 3531743439175249777514135)
            ·
              refine ⟨5297615158762874666271203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531743439175249777514135 5297615158762874666271203)
              ·
                refine ⟨7946422738144311999406805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297615158762874666271203 7946422738144311999406805)
                ·
                  refine ⟨186244282925257312486097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7946422738144311999406805 186244282925257312486097)
                  ·
                    rfl

theorem cell23_3264385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 7].length) (baseStart_3264385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264385 prefixEnd_3264385 := by exact prefixLift 3264385
  have htrace : WordTrace (prefixWord ++ tailWord_3264385) baseStart_3264385 baseEnd_3264385 := by
    simpa [prefixWord, tailWord_3264385, baseEnd_3264385] using wordTrace_append hprefix tailTrace_3264385
  have hstable : (prefixWord ++ tailWord_3264385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264385).length < 2 ^ (prefixWord ++ tailWord_3264385).sum := by decide
  have hdescent : baseEnd_3264385 < baseStart_3264385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264391 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3264391 : Nat := 118140960795 + 3264391 * 2 ^ 59
def prefixEnd_3264391 : Nat := 4983230072969 + 3 ^ 40 * 3264391 * 2
def baseEnd_3264391 : Nat := 1676201627211242788899845

theorem tailTrace_3264391 : CollatzResearch.WordTrace tailWord_3264391 prefixEnd_3264391 1676201627211242788899845 := by
  unfold tailWord_3264391
  simp only [CollatzResearch.WordTrace]
  refine ⟨119062121116676395441985027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79374747411117596961323351 119062121116676395441985027)
  ·
    refine ⟨178593181675014593162977541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119062121116676395441985027 178593181675014593162977541)
    ·
      refine ⟨33486221564065236218058289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178593181675014593162977541 33486221564065236218058289)
      ·
        refine ⟨25114666173048927163543717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33486221564065236218058289 25114666173048927163543717)
        ·
          refine ⟨4708999907446673843164447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25114666173048927163543717 4708999907446673843164447)
          ·
            refine ⟨7063499861170010764746671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708999907446673843164447 7063499861170010764746671)
            ·
              refine ⟨10595249791755016147120007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063499861170010764746671 10595249791755016147120007)
              ·
                refine ⟨15892874687632524220680011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595249791755016147120007 15892874687632524220680011)
                ·
                  refine ⟨23839312031448786331020017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892874687632524220680011 23839312031448786331020017)
                  ·
                    refine ⟨17879484023586589748265013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23839312031448786331020017 17879484023586589748265013)
                    ·
                      refine ⟨1676201627211242788899845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17879484023586589748265013 1676201627211242788899845)
                      ·
                        rfl

theorem cell23_3264391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3264391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264391 prefixEnd_3264391 := by exact prefixLift 3264391
  have htrace : WordTrace (prefixWord ++ tailWord_3264391) baseStart_3264391 baseEnd_3264391 := by
    simpa [prefixWord, tailWord_3264391, baseEnd_3264391] using wordTrace_append hprefix tailTrace_3264391
  have hstable : (prefixWord ++ tailWord_3264391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264391).length < 2 ^ (prefixWord ++ tailWord_3264391).sum := by decide
  have hdescent : baseEnd_3264391 < baseStart_3264391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264401 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_3264401 : Nat := 118140960795 + 3264401 * 2 ^ 59
def prefixEnd_3264401 : Nat := 4983230072969 + 3 ^ 40 * 3264401 * 2
def baseEnd_3264401 : Nat := 1676206762017787749774799

theorem tailTrace_3264401 : CollatzResearch.WordTrace tailWord_3264401 prefixEnd_3264401 1676206762017787749774799 := by
  unfold tailWord_3264401
  simp only [CollatzResearch.WordTrace]
  refine ⟨119062485846640167149849057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79374990564426778099899371 119062485846640167149849057)
  ·
    refine ⟨89296864384980125362386793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119062485846640167149849057 89296864384980125362386793)
    ·
      refine ⟨66972648288735094021790095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89296864384980125362386793 66972648288735094021790095)
      ·
        refine ⟨100458972433102641032685143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66972648288735094021790095 100458972433102641032685143)
        ·
          refine ⟨150688458649653961549027715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100458972433102641032685143 150688458649653961549027715)
          ·
            refine ⟨226032687974480942323541573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150688458649653961549027715 226032687974480942323541573)
            ·
              refine ⟨42381128995215176685664045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226032687974480942323541573 42381128995215176685664045)
              ·
                refine ⟨15892923373205691257124017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42381128995215176685664045 15892923373205691257124017)
                ·
                  refine ⟨11919692529904268442843013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15892923373205691257124017 11919692529904268442843013)
                  ·
                    refine ⟨2234942349357050333033065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11919692529904268442843013 2234942349357050333033065)
                    ·
                      refine ⟨1676206762017787749774799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2234942349357050333033065 1676206762017787749774799)
                      ·
                        rfl

theorem cell23_3264401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_3264401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264401 prefixEnd_3264401 := by exact prefixLift 3264401
  have htrace : WordTrace (prefixWord ++ tailWord_3264401) baseStart_3264401 baseEnd_3264401 := by
    simpa [prefixWord, tailWord_3264401, baseEnd_3264401] using wordTrace_append hprefix tailTrace_3264401
  have hstable : (prefixWord ++ tailWord_3264401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264401).length < 2 ^ (prefixWord ++ tailWord_3264401).sum := by decide
  have hdescent : baseEnd_3264401 < baseStart_3264401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264441 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 6]
def baseStart_3264441 : Nat := 118140960795 + 3264441 * 2 ^ 59
def prefixEnd_3264441 : Nat := 4983230072969 + 3 ^ 40 * 3264441 * 2
def baseEnd_3264441 : Nat := 186247477915996399252735

theorem tailTrace_3264441 : CollatzResearch.WordTrace tailWord_3264441 prefixEnd_3264441 186247477915996399252735 := by
  unfold tailWord_3264441
  simp only [CollatzResearch.WordTrace]
  refine ⟨119063944766495253981305177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79375963177663502654203451 119063944766495253981305177)
  ·
    refine ⟨89297958574871440485978883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119063944766495253981305177 89297958574871440485978883)
    ·
      refine ⟨133946937862307160728968325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89297958574871440485978883 133946937862307160728968325)
      ·
        refine ⟨25115050849182592636681561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133946937862307160728968325 25115050849182592636681561)
        ·
          refine ⟨18836288136886944477511171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25115050849182592636681561 18836288136886944477511171)
          ·
            refine ⟨28254432205330416716266757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18836288136886944477511171 28254432205330416716266757)
            ·
              refine ⟨5297706038499453134300017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28254432205330416716266757 5297706038499453134300017)
              ·
                refine ⟨3973279528874589850725013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297706038499453134300017 3973279528874589850725013)
                ·
                  refine ⟨186247477915996399252735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3973279528874589850725013 186247477915996399252735)
                  ·
                    rfl

theorem cell23_3264441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_3264441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264441 prefixEnd_3264441 := by exact prefixLift 3264441
  have htrace : WordTrace (prefixWord ++ tailWord_3264441) baseStart_3264441 baseEnd_3264441 := by
    simpa [prefixWord, tailWord_3264441, baseEnd_3264441] using wordTrace_append hprefix tailTrace_3264441
  have hstable : (prefixWord ++ tailWord_3264441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264441).length < 2 ^ (prefixWord ++ tailWord_3264441).sum := by decide
  have hdescent : baseEnd_3264441 < baseStart_3264441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264445 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_3264445 : Nat := 118140960795 + 3264445 * 2 ^ 59
def prefixEnd_3264445 : Nat := 4983230072969 + 3 ^ 40 * 3264445 * 2
def baseEnd_3264445 : Nat := 558743118388861859208199

theorem tailTrace_3264445 : CollatzResearch.WordTrace tailWord_3264445 prefixEnd_3264445 558743118388861859208199 := by
  unfold tailWord_3264445
  simp only [CollatzResearch.WordTrace]
  refine ⟨119064090658480762664450789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79376060438987175109633859 119064090658480762664450789)
  ·
    refine ⟨22324516998465142999584523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119064090658480762664450789 22324516998465142999584523)
    ·
      refine ⟨33486775497697714499376785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22324516998465142999584523 33486775497697714499376785)
      ·
        refine ⟨25115081623273285874532589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33486775497697714499376785 25115081623273285874532589)
        ·
          refine ⟨9418155608727482202949721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25115081623273285874532589 9418155608727482202949721)
          ·
            refine ⟨7063616706545611652212291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9418155608727482202949721 7063616706545611652212291)
            ·
              refine ⟨10595425059818417478318437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063616706545611652212291 10595425059818417478318437)
              ·
                refine ⟨1986642198715953277184707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10595425059818417478318437 1986642198715953277184707)
                ·
                  refine ⟨2979963298073929915777061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986642198715953277184707 2979963298073929915777061)
                  ·
                    refine ⟨558743118388861859208199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979963298073929915777061 558743118388861859208199)
                    ·
                      rfl

theorem cell23_3264445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_3264445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264445 prefixEnd_3264445 := by exact prefixLift 3264445
  have htrace : WordTrace (prefixWord ++ tailWord_3264445) baseStart_3264445 baseEnd_3264445 := by
    simpa [prefixWord, tailWord_3264445, baseEnd_3264445] using wordTrace_append hprefix tailTrace_3264445
  have hstable : (prefixWord ++ tailWord_3264445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264445).length < 2 ^ (prefixWord ++ tailWord_3264445).sum := by decide
  have hdescent : baseEnd_3264445 < baseStart_3264445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264471 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 1, 5]
def baseStart_3264471 : Nat := 118140960795 + 3264471 * 2 ^ 59
def prefixEnd_3264471 : Nat := 4983230072969 + 3 ^ 40 * 3264471 * 2
def baseEnd_3264471 : Nat := 558747568554534158633159

theorem tailTrace_3264471 : CollatzResearch.WordTrace tailWord_3264471 prefixEnd_3264471 558747568554534158633159 := by
  unfold tailWord_3264471
  simp only [CollatzResearch.WordTrace]
  refine ⟨119065038956386569104897267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79376692637591046069931511 119065038956386569104897267)
  ·
    refine ⟨178597558434579853657345901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119065038956386569104897267 178597558434579853657345901)
    ·
      refine ⟨66974084412967445121504713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178597558434579853657345901 66974084412967445121504713)
      ·
        refine ⟨50230563309725583841128535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66974084412967445121504713 50230563309725583841128535)
        ·
          refine ⟨75345844964588375761692803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50230563309725583841128535 75345844964588375761692803)
          ·
            refine ⟨113018767446882563642539205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75345844964588375761692803 113018767446882563642539205)
            ·
              refine ⟨21191018896290480682976101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113018767446882563642539205 21191018896290480682976101)
              ·
                refine ⟨3973316043054465128058019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21191018896290480682976101 3973316043054465128058019)
                ·
                  refine ⟨5959974064581697692087029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973316043054465128058019 5959974064581697692087029)
                  ·
                    refine ⟨558747568554534158633159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5959974064581697692087029 558747568554534158633159)
                    ·
                      rfl

theorem cell23_3264471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_3264471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264471 prefixEnd_3264471 := by exact prefixLift 3264471
  have htrace : WordTrace (prefixWord ++ tailWord_3264471) baseStart_3264471 baseEnd_3264471 := by
    simpa [prefixWord, tailWord_3264471, baseEnd_3264471] using wordTrace_append hprefix tailTrace_3264471
  have hstable : (prefixWord ++ tailWord_3264471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264471).length < 2 ^ (prefixWord ++ tailWord_3264471).sum := by decide
  have hdescent : baseEnd_3264471 < baseStart_3264471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264491 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 8, 2]
def baseStart_3264491 : Nat := 118140960795 + 3264491 * 2 ^ 59
def prefixEnd_3264491 : Nat := 4983230072969 + 3 ^ 40 * 3264491 * 2
def baseEnd_3264491 : Nat := 1676252975276692397649385

theorem tailTrace_3264491 : CollatzResearch.WordTrace tailWord_3264491 prefixEnd_3264491 1676252975276692397649385 := by
  unfold tailWord_3264491
  simp only [CollatzResearch.WordTrace]
  refine ⟨119065768416314112520625327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79377178944209408347083551 119065768416314112520625327)
  ·
    refine ⟨178598652624471168780937991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119065768416314112520625327 178598652624471168780937991)
    ·
      refine ⟨267897978936706753171406987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178598652624471168780937991 267897978936706753171406987)
      ·
        refine ⟨401846968405060129757110481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267897978936706753171406987 401846968405060129757110481)
        ·
          refine ⟨301385226303795097317832861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401846968405060129757110481 301385226303795097317832861)
          ·
            refine ⟨113019459863923161494187323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301385226303795097317832861 113019459863923161494187323)
            ·
              refine ⟨169529189795884742241280985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113019459863923161494187323 169529189795884742241280985)
              ·
                refine ⟨127146892346913556680960739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169529189795884742241280985 127146892346913556680960739)
                ·
                  refine ⟨190720338520370335021441109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127146892346913556680960739 190720338520370335021441109)
                  ·
                    refine ⟨2235003967035589863532513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 190720338520370335021441109 2235003967035589863532513)
                    ·
                      refine ⟨1676252975276692397649385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235003967035589863532513 1676252975276692397649385)
                      ·
                        rfl

theorem cell23_3264491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8, 2].length) (baseStart_3264491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264491 prefixEnd_3264491 := by exact prefixLift 3264491
  have htrace : WordTrace (prefixWord ++ tailWord_3264491) baseStart_3264491 baseEnd_3264491 := by
    simpa [prefixWord, tailWord_3264491, baseEnd_3264491] using wordTrace_append hprefix tailTrace_3264491
  have hstable : (prefixWord ++ tailWord_3264491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264491).length < 2 ^ (prefixWord ++ tailWord_3264491).sum := by decide
  have hdescent : baseEnd_3264491 < baseStart_3264491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264502 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3264502 : Nat := 118140960795 + 3264502 * 2 ^ 59
def prefixEnd_3264502 : Nat := 4983230072969 + 3 ^ 40 * 3264502 * 2
def baseEnd_3264502 : Nat := 1676258623563891854611835

theorem tailTrace_3264502 : CollatzResearch.WordTrace tailWord_3264502 prefixEnd_3264502 1676258623563891854611835 := by
  unfold tailWord_3264502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441635601204641337454735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79377446412849507599517173 7441635601204641337454735)
  ·
    refine ⟨11162453401806962006182103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7441635601204641337454735 11162453401806962006182103)
    ·
      refine ⟨16743680102710443009273155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11162453401806962006182103 16743680102710443009273155)
      ·
        refine ⟨25115520154065664513909733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16743680102710443009273155 25115520154065664513909733)
        ·
          refine ⟨4709160028887312096358075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25115520154065664513909733 4709160028887312096358075)
          ·
            refine ⟨7063740043330968144537113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709160028887312096358075 7063740043330968144537113)
            ·
              refine ⟨5297805032498226108402835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7063740043330968144537113 5297805032498226108402835)
              ·
                refine ⟨7946707548747339162604253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297805032498226108402835 7946707548747339162604253)
                ·
                  refine ⟨2980015330780252185976595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7946707548747339162604253 2980015330780252185976595)
                  ·
                    refine ⟨4470022996170378278964893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2980015330780252185976595 4470022996170378278964893)
                    ·
                      refine ⟨1676258623563891854611835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470022996170378278964893 1676258623563891854611835)
                      ·
                        rfl

theorem cell23_3264502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3264502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264502 prefixEnd_3264502 := by exact prefixLift 3264502
  have htrace : WordTrace (prefixWord ++ tailWord_3264502) baseStart_3264502 baseEnd_3264502 := by
    simpa [prefixWord, tailWord_3264502, baseEnd_3264502] using wordTrace_append hprefix tailTrace_3264502
  have hstable : (prefixWord ++ tailWord_3264502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264502).length < 2 ^ (prefixWord ++ tailWord_3264502).sum := by decide
  have hdescent : baseEnd_3264502 < baseStart_3264502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264511 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_3264511 : Nat := 118140960795 + 3264511 * 2 ^ 59
def prefixEnd_3264511 : Nat := 4983230072969 + 3 ^ 40 * 3264511 * 2
def baseEnd_3264511 : Nat := 1676263244889782319399293

theorem tailTrace_3264511 : CollatzResearch.WordTrace tailWord_3264511 prefixEnd_3264511 1676263244889782319399293 := by
  unfold tailWord_3264511
  simp only [CollatzResearch.WordTrace]
  refine ⟨119066497876241655936353387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79377665250827770624235591 119066497876241655936353387)
  ·
    refine ⟨178599746814362483904530081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119066497876241655936353387 178599746814362483904530081)
    ·
      refine ⟨133949810110771862928397561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178599746814362483904530081 133949810110771862928397561)
      ·
        refine ⟨100462357583078897196298171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133949810110771862928397561 100462357583078897196298171)
        ·
          refine ⟨150693536374618345794447257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100462357583078897196298171 150693536374618345794447257)
          ·
            refine ⟨113020152280963759345835443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150693536374618345794447257 113020152280963759345835443)
            ·
              refine ⟨169530228421445639018753165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113020152280963759345835443 169530228421445639018753165)
              ·
                refine ⟨63573835658042114632032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169530228421445639018753165 63573835658042114632032437)
                ·
                  refine ⟨5960047092941448246753041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63573835658042114632032437 5960047092941448246753041)
                  ·
                    refine ⟨4470035319706086185064781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5960047092941448246753041 4470035319706086185064781)
                    ·
                      refine ⟨1676263244889782319399293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470035319706086185064781 1676263244889782319399293)
                      ·
                        rfl

theorem cell23_3264511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_3264511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264511 prefixEnd_3264511 := by exact prefixLift 3264511
  have htrace : WordTrace (prefixWord ++ tailWord_3264511) baseStart_3264511 baseEnd_3264511 := by
    simpa [prefixWord, tailWord_3264511, baseEnd_3264511] using wordTrace_append hprefix tailTrace_3264511
  have hstable : (prefixWord ++ tailWord_3264511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264511).length < 2 ^ (prefixWord ++ tailWord_3264511).sum := by decide
  have hdescent : baseEnd_3264511 < baseStart_3264511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264531 : List Nat := [1, 1, 1, 2, 1, 4, 6, 7]
def baseStart_3264531 : Nat := 118140960795 + 3264531 * 2 ^ 59
def prefixEnd_3264531 : Nat := 4983230072969 + 3 ^ 40 * 3264531 * 2
def baseEnd_3264531 : Nat := 62084204240847120042563

theorem tailTrace_3264531 : CollatzResearch.WordTrace tailWord_3264531 prefixEnd_3264531 62084204240847120042563 := by
  unfold tailWord_3264531
  simp only [CollatzResearch.WordTrace]
  refine ⟨119067227336169199352081447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79378151557446132901387631 119067227336169199352081447)
  ·
    refine ⟨178600841004253799028122171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119067227336169199352081447 178600841004253799028122171)
    ·
      refine ⟨267901261506380698542183257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178600841004253799028122171 267901261506380698542183257)
      ·
        refine ⟨200925946129785523906637443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267901261506380698542183257 200925946129785523906637443)
        ·
          refine ⟨301388919194678285859956165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200925946129785523906637443 301388919194678285859956165)
          ·
            refine ⟨56510422349002178598741781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301388919194678285859956165 56510422349002178598741781)
            ·
              refine ⟨2648926047609477121816021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56510422349002178598741781 2648926047609477121816021)
              ·
                refine ⟨62084204240847120042563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2648926047609477121816021 62084204240847120042563)
                ·
                  rfl

theorem cell23_3264531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 7].length) (baseStart_3264531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264531 prefixEnd_3264531 := by exact prefixLift 3264531
  have htrace : WordTrace (prefixWord ++ tailWord_3264531) baseStart_3264531 baseEnd_3264531 := by
    simpa [prefixWord, tailWord_3264531, baseEnd_3264531] using wordTrace_append hprefix tailTrace_3264531
  have hstable : (prefixWord ++ tailWord_3264531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264531).length < 2 ^ (prefixWord ++ tailWord_3264531).sum := by decide
  have hdescent : baseEnd_3264531 < baseStart_3264531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264548 : List Nat := [2, 3, 1, 4, 2, 2, 9]
def baseStart_3264548 : Nat := 118140960795 + 3264548 * 2 ^ 59
def prefixEnd_3264548 : Nat := 4983230072969 + 3 ^ 40 * 3264548 * 2
def baseEnd_3264548 : Nat := 20694842514493810797983

theorem tailTrace_3264548 : CollatzResearch.WordTrace tailWord_3264548 prefixEnd_3264548 20694842514493810797983 := by
  unfold tailWord_3264548
  simp only [CollatzResearch.WordTrace]
  refine ⟨59533923688553805627725149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79378564918071740836966865 59533923688553805627725149)
  ·
    refine ⟨22325221383207677110396931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59533923688553805627725149 22325221383207677110396931)
    ·
      refine ⟨33487832074811515665595397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22325221383207677110396931 33487832074811515665595397)
      ·
        refine ⟨6278968514027159187299137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33487832074811515665595397 6278968514027159187299137)
        ·
          refine ⟨4709226385520369390474353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6278968514027159187299137 4709226385520369390474353)
          ·
            refine ⟨3531919789140277042855765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709226385520369390474353 3531919789140277042855765)
            ·
              refine ⟨20694842514493810797983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3531919789140277042855765 20694842514493810797983)
              ·
                rfl

theorem cell23_3264548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 9].length) (baseStart_3264548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264548 prefixEnd_3264548 := by exact prefixLift 3264548
  have htrace : WordTrace (prefixWord ++ tailWord_3264548) baseStart_3264548 baseEnd_3264548 := by
    simpa [prefixWord, tailWord_3264548, baseEnd_3264548] using wordTrace_append hprefix tailTrace_3264548
  have hstable : (prefixWord ++ tailWord_3264548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264548).length < 2 ^ (prefixWord ++ tailWord_3264548).sum := by decide
  have hdescent : baseEnd_3264548 < baseStart_3264548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264569 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 2, 4]
def baseStart_3264569 : Nat := 118140960795 + 3264569 * 2 ^ 59
def prefixEnd_3264569 : Nat := 4983230072969 + 3 ^ 40 * 3264569 * 2
def baseEnd_3264569 : Nat := 558764342255914364158009

theorem tailTrace_3264569 : CollatzResearch.WordTrace tailWord_3264569 prefixEnd_3264569 558764342255914364158009 := by
  unfold tailWord_3264569
  simp only [CollatzResearch.WordTrace]
  refine ⟨119068613310031531841964761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79379075540021021227976507 119068613310031531841964761)
  ·
    refine ⟨89301459982523648881473571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119068613310031531841964761 89301459982523648881473571)
    ·
      refine ⟨133952189973785473322210357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89301459982523648881473571 133952189973785473322210357)
      ·
        refine ⟨12558017810042388123957221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133952189973785473322210357 12558017810042388123957221)
        ·
          refine ⟨2354628339382947773241979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12558017810042388123957221 2354628339382947773241979)
          ·
            refine ⟨3531942509074421659862969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354628339382947773241979 3531942509074421659862969)
            ·
              refine ⟨2648956881805816244897227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531942509074421659862969 2648956881805816244897227)
              ·
                refine ⟨3973435322708724367345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648956881805816244897227 3973435322708724367345841)
                ·
                  refine ⟨2980076492031543275509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3973435322708724367345841 2980076492031543275509381)
                  ·
                    refine ⟨558764342255914364158009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980076492031543275509381 558764342255914364158009)
                    ·
                      rfl

theorem cell23_3264569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_3264569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264569 prefixEnd_3264569 := by exact prefixLift 3264569
  have htrace : WordTrace (prefixWord ++ tailWord_3264569) baseStart_3264569 baseEnd_3264569 := by
    simpa [prefixWord, tailWord_3264569, baseEnd_3264569] using wordTrace_append hprefix tailTrace_3264569
  have hstable : (prefixWord ++ tailWord_3264569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264569).length < 2 ^ (prefixWord ++ tailWord_3264569).sum := by decide
  have hdescent : baseEnd_3264569 < baseStart_3264569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264601 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3264601 : Nat := 118140960795 + 3264601 * 2 ^ 59
def prefixEnd_3264601 : Nat := 4983230072969 + 3 ^ 40 * 3264601 * 2
def baseEnd_3264601 : Nat := 1676309458148686967273879

theorem tailTrace_3264601 : CollatzResearch.WordTrace tailWord_3264601 prefixEnd_3264601 1676309458148686967273879 := by
  unfold tailWord_3264601
  simp only [CollatzResearch.WordTrace]
  refine ⟨119069780445915601307129657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79379853630610400871419771 119069780445915601307129657)
  ·
    refine ⟨89302335334436700980347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119069780445915601307129657 89302335334436700980347243)
    ·
      refine ⟨133953503001655051470520865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89302335334436700980347243 133953503001655051470520865)
      ·
        refine ⟨100465127251241288602890649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133953503001655051470520865 100465127251241288602890649)
        ·
          refine ⟨75348845438430966452167987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100465127251241288602890649 75348845438430966452167987)
          ·
            refine ⟨113023268157646449678251981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75348845438430966452167987 113023268157646449678251981)
            ·
              refine ⟨42383725559117418629344493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113023268157646449678251981 42383725559117418629344493)
              ·
                refine ⟨15893897084669031986004185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42383725559117418629344493 15893897084669031986004185)
                ·
                  refine ⟨11920422813501773989503139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15893897084669031986004185 11920422813501773989503139)
                  ·
                    refine ⟨17880634220252660984254709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11920422813501773989503139 17880634220252660984254709)
                    ·
                      refine ⟨1676309458148686967273879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17880634220252660984254709 1676309458148686967273879)
                      ·
                        rfl

theorem cell23_3264601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3264601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264601 prefixEnd_3264601 := by exact prefixLift 3264601
  have htrace : WordTrace (prefixWord ++ tailWord_3264601) baseStart_3264601 baseEnd_3264601 := by
    simpa [prefixWord, tailWord_3264601, baseEnd_3264601] using wordTrace_append hprefix tailTrace_3264601
  have hstable : (prefixWord ++ tailWord_3264601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264601).length < 2 ^ (prefixWord ++ tailWord_3264601).sum := by decide
  have hdescent : baseEnd_3264601 < baseStart_3264601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264602 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_3264602 : Nat := 118140960795 + 3264602 * 2 ^ 59
def prefixEnd_3264602 : Nat := 4983230072969 + 3 ^ 40 * 3264602 * 2
def baseEnd_3264602 : Nat := 1676309971629341463361375

theorem tailTrace_3264602 : CollatzResearch.WordTrace tailWord_3264602 prefixEnd_3264602 1676309971629341463361375 := by
  unfold tailWord_3264602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767454229727994619479015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79379877945941318985277373 29767454229727994619479015)
  ·
    refine ⟨44651181344591991929218523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29767454229727994619479015 44651181344591991929218523)
    ·
      refine ⟨66976772016887987893827785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44651181344591991929218523 66976772016887987893827785)
      ·
        refine ⟨50232579012665990920370839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66976772016887987893827785 50232579012665990920370839)
        ·
          refine ⟨75348868518998986380556259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50232579012665990920370839 75348868518998986380556259)
          ·
            refine ⟨113023302778498479570834389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75348868518998986380556259 113023302778498479570834389)
            ·
              refine ⟨2648983658871058114941431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 113023302778498479570834389 2648983658871058114941431)
              ·
                refine ⟨3973475488306587172412147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648983658871058114941431 3973475488306587172412147)
                ·
                  refine ⟨5960213232459880758618221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973475488306587172412147 5960213232459880758618221)
                  ·
                    refine ⟨2235079962172455284481833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5960213232459880758618221 2235079962172455284481833)
                    ·
                      refine ⟨1676309971629341463361375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235079962172455284481833 1676309971629341463361375)
                      ·
                        rfl

theorem cell23_3264602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_3264602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264602 prefixEnd_3264602 := by exact prefixLift 3264602
  have htrace : WordTrace (prefixWord ++ tailWord_3264602) baseStart_3264602 baseEnd_3264602 := by
    simpa [prefixWord, tailWord_3264602, baseEnd_3264602] using wordTrace_append hprefix tailTrace_3264602
  have hstable : (prefixWord ++ tailWord_3264602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264602).length < 2 ^ (prefixWord ++ tailWord_3264602).sum := by decide
  have hdescent : baseEnd_3264602 < baseStart_3264602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264610 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3264610 : Nat := 118140960795 + 3264610 * 2 ^ 59
def prefixEnd_3264610 : Nat := 4983230072969 + 3 ^ 40 * 3264610 * 2
def baseEnd_3264610 : Nat := 1676314079474577432061339

theorem tailTrace_3264610 : CollatzResearch.WordTrace tailWord_3264610 prefixEnd_3264610 1676314079474577432061339 := by
  unfold tailWord_3264610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767527175720748961051821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79380072468588663896138189 29767527175720748961051821)
  ·
    refine ⟨11162822690895280860394433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29767527175720748961051821 11162822690895280860394433)
    ·
      refine ⟨8372117018171460645295825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11162822690895280860394433 8372117018171460645295825)
      ·
        refine ⟨6279087763628595483971869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8372117018171460645295825 6279087763628595483971869)
        ·
          refine ⟨2354657911360723306489451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6279087763628595483971869 2354657911360723306489451)
          ·
            refine ⟨3531986867041084959734177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354657911360723306489451 3531986867041084959734177)
            ·
              refine ⟨2648990150280813719800633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531986867041084959734177 2648990150280813719800633)
              ·
                refine ⟨1986742612710610289850475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648990150280813719800633 1986742612710610289850475)
                ·
                  refine ⟨2980113919065915434775713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986742612710610289850475 2980113919065915434775713)
                  ·
                    refine ⟨2235085439299436576081785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980113919065915434775713 2235085439299436576081785)
                    ·
                      refine ⟨1676314079474577432061339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235085439299436576081785 1676314079474577432061339)
                      ·
                        rfl

theorem cell23_3264610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3264610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264610 prefixEnd_3264610 := by exact prefixLift 3264610
  have htrace : WordTrace (prefixWord ++ tailWord_3264610) baseStart_3264610 baseEnd_3264610 := by
    simpa [prefixWord, tailWord_3264610, baseEnd_3264610] using wordTrace_append hprefix tailTrace_3264610
  have hstable : (prefixWord ++ tailWord_3264610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264610).length < 2 ^ (prefixWord ++ tailWord_3264610).sum := by decide
  have hdescent : baseEnd_3264610 < baseStart_3264610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264666 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3264666 : Nat := 118140960795 + 3264666 * 2 ^ 59
def prefixEnd_3264666 : Nat := 4983230072969 + 3 ^ 40 * 3264666 * 2
def baseEnd_3264666 : Nat := 1676342834391229212961081

theorem tailTrace_3264666 : CollatzResearch.WordTrace tailWord_3264666 prefixEnd_3264666 1676342834391229212961081 := by
  unfold tailWord_3264666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768037797670029352061463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79381434127120078272163901 29768037797670029352061463)
  ·
    refine ⟨44652056696505044028092195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29768037797670029352061463 44652056696505044028092195)
    ·
      refine ⟨66978085044757566042138293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44652056696505044028092195 66978085044757566042138293)
      ·
        refine ⟨6279195472946021816450465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66978085044757566042138293 6279195472946021816450465)
        ·
          refine ⟨4709396604709516362337849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6279195472946021816450465 4709396604709516362337849)
          ·
            refine ⟨3532047453532137271753387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709396604709516362337849 3532047453532137271753387)
            ·
              refine ⟨5298071180298205907630081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532047453532137271753387 5298071180298205907630081)
              ·
                refine ⟨3973553385223654430722561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298071180298205907630081 3973553385223654430722561)
                ·
                  refine ⟨2980165038917740823041921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3973553385223654430722561 2980165038917740823041921)
                  ·
                    refine ⟨2235123779188305617281441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980165038917740823041921 2235123779188305617281441)
                    ·
                      refine ⟨1676342834391229212961081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235123779188305617281441 1676342834391229212961081)
                      ·
                        rfl

theorem cell23_3264666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3264666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264666 prefixEnd_3264666 := by exact prefixLift 3264666
  have htrace : WordTrace (prefixWord ++ tailWord_3264666) baseStart_3264666 baseEnd_3264666 := by
    simpa [prefixWord, tailWord_3264666, baseEnd_3264666] using wordTrace_append hprefix tailTrace_3264666
  have hstable : (prefixWord ++ tailWord_3264666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264666).length < 2 ^ (prefixWord ++ tailWord_3264666).sum := by decide
  have hdescent : baseEnd_3264666 < baseStart_3264666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264668 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3264668 : Nat := 118140960795 + 3264668 * 2 ^ 59
def prefixEnd_3264668 : Nat := 4983230072969 + 3 ^ 40 * 3264668 * 2
def baseEnd_3264668 : Nat := 558781287117512735045357

theorem tailTrace_3264668 : CollatzResearch.WordTrace tailWord_3264668 prefixEnd_3264668 558781287117512735045357 := by
  unfold tailWord_3264668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59536112068336435874909329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79381482757781914499879105 59536112068336435874909329)
  ·
    refine ⟨44652084051252326906181997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59536112068336435874909329 44652084051252326906181997)
    ·
      refine ⟨16744531519219622589818249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44652084051252326906181997 16744531519219622589818249)
      ·
        refine ⟨12558398639414716942363687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16744531519219622589818249 12558398639414716942363687)
        ·
          refine ⟨18837597959122075413545531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12558398639414716942363687 18837597959122075413545531)
          ·
            refine ⟨28256396938683113120318297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18837597959122075413545531 28256396938683113120318297)
            ·
              refine ⟨21192297704012334840238723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28256396938683113120318297 21192297704012334840238723)
              ·
                refine ⟨31788446556018502260358085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21192297704012334840238723 31788446556018502260358085)
                ·
                  refine ⟨5960333729253469173817141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31788446556018502260358085 5960333729253469173817141)
                  ·
                    refine ⟨558781287117512735045357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5960333729253469173817141 558781287117512735045357)
                    ·
                      rfl

theorem cell23_3264668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3264668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264668 prefixEnd_3264668 := by exact prefixLift 3264668
  have htrace : WordTrace (prefixWord ++ tailWord_3264668) baseStart_3264668 baseEnd_3264668 := by
    simpa [prefixWord, tailWord_3264668, baseEnd_3264668] using wordTrace_append hprefix tailTrace_3264668
  have hstable : (prefixWord ++ tailWord_3264668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264668).length < 2 ^ (prefixWord ++ tailWord_3264668).sum := by decide
  have hdescent : baseEnd_3264668 < baseStart_3264668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264706 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3264706 : Nat := 118140960795 + 3264706 * 2 ^ 59
def prefixEnd_3264706 : Nat := 4983230072969 + 3 ^ 40 * 3264706 * 2
def baseEnd_3264706 : Nat := 186262597068601006273433

theorem tailTrace_3264706 : CollatzResearch.WordTrace tailWord_3264706 prefixEnd_3264706 186262597068601006273433 := by
  unfold tailWord_3264706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768402527633801059925493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79382406740356802826467981 29768402527633801059925493)
  ·
    refine ⟨2790787736965668849368015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29768402527633801059925493 2790787736965668849368015)
    ·
      refine ⟨4186181605448503274052023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790787736965668849368015 4186181605448503274052023)
      ·
        refine ⟨6279272408172754911078035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186181605448503274052023 6279272408172754911078035)
        ·
          refine ⟨9418908612259132366617053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279272408172754911078035 9418908612259132366617053)
          ·
            refine ⟨3532090729597174637481395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9418908612259132366617053 3532090729597174637481395)
            ·
              refine ⟨5298136094395761956222093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532090729597174637481395 5298136094395761956222093)
              ·
                refine ⟨1986801035398410733583285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5298136094395761956222093 1986801035398410733583285)
                ·
                  refine ⟨186262597068601006273433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1986801035398410733583285 186262597068601006273433)
                  ·
                    rfl

theorem cell23_3264706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3264706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264706 prefixEnd_3264706 := by exact prefixLift 3264706
  have htrace : WordTrace (prefixWord ++ tailWord_3264706) baseStart_3264706 baseEnd_3264706 := by
    simpa [prefixWord, tailWord_3264706, baseEnd_3264706] using wordTrace_append hprefix tailTrace_3264706
  have hstable : (prefixWord ++ tailWord_3264706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264706).length < 2 ^ (prefixWord ++ tailWord_3264706).sum := by decide
  have hdescent : baseEnd_3264706 < baseStart_3264706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264728 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 8]
def baseStart_3264728 : Nat := 118140960795 + 3264728 * 2 ^ 59
def prefixEnd_3264728 : Nat := 4983230072969 + 3 ^ 40 * 3264728 * 2
def baseEnd_3264728 : Nat := 186263852243534218931755

theorem tailTrace_3264728 : CollatzResearch.WordTrace tailWord_3264728 prefixEnd_3264728 186263852243534218931755 := by
  unfold tailWord_3264728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59537206258227750998501419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79382941677637001331335225 59537206258227750998501419)
  ·
    refine ⟨89305809387341626497752129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59537206258227750998501419 89305809387341626497752129)
    ·
      refine ⟨66979357040506219873314097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89305809387341626497752129 66979357040506219873314097)
      ·
        refine ⟨50234517780379664904985573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66979357040506219873314097 50234517780379664904985573)
        ·
          refine ⟨9418972083821187169684795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50234517780379664904985573 9418972083821187169684795)
          ·
            refine ⟨14128458125731780754527193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418972083821187169684795 14128458125731780754527193)
            ·
              refine ⟨10596343594298835565895395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14128458125731780754527193 10596343594298835565895395)
              ·
                refine ⟨15894515391448253348843093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596343594298835565895395 15894515391448253348843093)
                ·
                  refine ⟨186263852243534218931755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15894515391448253348843093 186263852243534218931755)
                  ·
                    rfl

theorem cell23_3264728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_3264728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264728 prefixEnd_3264728 := by exact prefixLift 3264728
  have htrace : WordTrace (prefixWord ++ tailWord_3264728) baseStart_3264728 baseEnd_3264728 := by
    simpa [prefixWord, tailWord_3264728, baseEnd_3264728] using wordTrace_append hprefix tailTrace_3264728
  have hstable : (prefixWord ++ tailWord_3264728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264728).length < 2 ^ (prefixWord ++ tailWord_3264728).sum := by decide
  have hdescent : baseEnd_3264728 < baseStart_3264728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264755 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 3]
def baseStart_3264755 : Nat := 118140960795 + 3264755 * 2 ^ 59
def prefixEnd_3264755 : Nat := 4983230072969 + 3 ^ 40 * 3264755 * 2
def baseEnd_3264755 : Nat := 1676388534169479364748171

theorem tailTrace_3264755 : CollatzResearch.WordTrace tailWord_3264755 prefixEnd_3264755 1676388534169479364748171 := by
  unfold tailWord_3264755
  simp only [CollatzResearch.WordTrace]
  refine ⟨119075397287357685608235719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79383598191571790405490479 119075397287357685608235719)
  ·
    refine ⟨178613095931036528412353579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119075397287357685608235719 178613095931036528412353579)
    ·
      refine ⟨267919643896554792618530369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178613095931036528412353579 267919643896554792618530369)
      ·
        refine ⟨200939732922416094463897777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267919643896554792618530369 200939732922416094463897777)
        ·
          refine ⟨150704799691812070847923333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200939732922416094463897777 150704799691812070847923333)
          ·
            refine ⟨28257149942214763283985625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150704799691812070847923333 28257149942214763283985625)
            ·
              refine ⟨21192862456661072462989219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28257149942214763283985625 21192862456661072462989219)
              ·
                refine ⟨31789293684991608694483829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21192862456661072462989219 31789293684991608694483829)
                ·
                  refine ⟨2980246282967963315107859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31789293684991608694483829 2980246282967963315107859)
                  ·
                    refine ⟨4470369424451944972661789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2980246282967963315107859 4470369424451944972661789)
                    ·
                      refine ⟨1676388534169479364748171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470369424451944972661789 1676388534169479364748171)
                      ·
                        rfl

theorem cell23_3264755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_3264755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264755 prefixEnd_3264755 := by exact prefixLift 3264755
  have htrace : WordTrace (prefixWord ++ tailWord_3264755) baseStart_3264755 baseEnd_3264755 := by
    simpa [prefixWord, tailWord_3264755, baseEnd_3264755] using wordTrace_append hprefix tailTrace_3264755
  have hstable : (prefixWord ++ tailWord_3264755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264755).length < 2 ^ (prefixWord ++ tailWord_3264755).sum := by decide
  have hdescent : baseEnd_3264755 < baseStart_3264755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264765 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_3264765 : Nat := 118140960795 + 3264765 * 2 ^ 59
def prefixEnd_3264765 : Nat := 4983230072969 + 3 ^ 40 * 3264765 * 2
def baseEnd_3264765 : Nat := 1676393668976024325623125

theorem tailTrace_3264765 : CollatzResearch.WordTrace tailWord_3264765 prefixEnd_3264765 1676393668976024325623125 := by
  unfold tailWord_3264765
  simp only [CollatzResearch.WordTrace]
  refine ⟨119075762017321457316099749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79383841344880971544066499 119075762017321457316099749)
  ·
    refine ⟨22326705378247773246768703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119075762017321457316099749 22326705378247773246768703)
    ·
      refine ⟨33490058067371659870153055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22326705378247773246768703 33490058067371659870153055)
      ·
        refine ⟨50235087101057489805229583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33490058067371659870153055 50235087101057489805229583)
        ·
          refine ⟨75352630651586234707844375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50235087101057489805229583 75352630651586234707844375)
          ·
            refine ⟨113028945977379352061766563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75352630651586234707844375 113028945977379352061766563)
            ·
              refine ⟨169543418966069028092649845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113028945977379352061766563 169543418966069028092649845)
              ·
                refine ⟨15894695528068971383685923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169543418966069028092649845 15894695528068971383685923)
                ·
                  refine ⟨23842043292103457075528885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15894695528068971383685923 23842043292103457075528885)
                  ·
                    refine ⟨2235191558634699100830833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23842043292103457075528885 2235191558634699100830833)
                    ·
                      refine ⟨1676393668976024325623125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235191558634699100830833 1676393668976024325623125)
                      ·
                        rfl

theorem cell23_3264765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_3264765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264765 prefixEnd_3264765 := by exact prefixLift 3264765
  have htrace : WordTrace (prefixWord ++ tailWord_3264765) baseStart_3264765 baseEnd_3264765 := by
    simpa [prefixWord, tailWord_3264765, baseEnd_3264765] using wordTrace_append hprefix tailTrace_3264765
  have hstable : (prefixWord ++ tailWord_3264765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264765).length < 2 ^ (prefixWord ++ tailWord_3264765).sum := by decide
  have hdescent : baseEnd_3264765 < baseStart_3264765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264782 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3264782 : Nat := 118140960795 + 3264782 * 2 ^ 59
def prefixEnd_3264782 : Nat := 4983230072969 + 3 ^ 40 * 3264782 * 2
def baseEnd_3264782 : Nat := 1676402398147150759110547

theorem tailTrace_3264782 : CollatzResearch.WordTrace tailWord_3264782 prefixEnd_3264782 1676402398147150759110547 := by
  unfold tailWord_3264782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884547757282483652433575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79384254705506579479645733 14884547757282483652433575)
  ·
    refine ⟨22326821635923725478650363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14884547757282483652433575 22326821635923725478650363)
    ·
      refine ⟨33490232453885588217975545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22326821635923725478650363 33490232453885588217975545)
      ·
        refine ⟨25117674340414191163481659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33490232453885588217975545 25117674340414191163481659)
        ·
          refine ⟨37676511510621286745222489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25117674340414191163481659 37676511510621286745222489)
          ·
            refine ⟨28257383632965965058916867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37676511510621286745222489 28257383632965965058916867)
            ·
              refine ⟨42386075449448947588375301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28257383632965965058916867 42386075449448947588375301)
              ·
                refine ⟨7947389146771677672820369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42386075449448947588375301 7947389146771677672820369)
                ·
                  refine ⟨5960541860078758254615277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7947389146771677672820369 5960541860078758254615277)
                  ·
                    refine ⟨2235203197529534345480729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5960541860078758254615277 2235203197529534345480729)
                    ·
                      refine ⟨1676402398147150759110547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235203197529534345480729 1676402398147150759110547)
                      ·
                        rfl

theorem cell23_3264782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3264782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264782 prefixEnd_3264782 := by exact prefixLift 3264782
  have htrace : WordTrace (prefixWord ++ tailWord_3264782) baseStart_3264782 baseEnd_3264782 := by
    simpa [prefixWord, tailWord_3264782, baseEnd_3264782] using wordTrace_append hprefix tailTrace_3264782
  have hstable : (prefixWord ++ tailWord_3264782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264782).length < 2 ^ (prefixWord ++ tailWord_3264782).sum := by decide
  have hdescent : baseEnd_3264782 < baseStart_3264782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264812 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_3264812 : Nat := 118140960795 + 3264812 * 2 ^ 59
def prefixEnd_3264812 : Nat := 4983230072969 + 3 ^ 40 * 3264812 * 2
def baseEnd_3264812 : Nat := 1676417802566785641735409

theorem tailTrace_3264812 : CollatzResearch.WordTrace tailWord_3264812 prefixEnd_3264812 1676417802566785641735409 := by
  unfold tailWord_3264812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59538738124075592171530345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79384984165434122895373793 59538738124075592171530345)
  ·
    refine ⟨44654053593056694128647759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59538738124075592171530345 44654053593056694128647759)
    ·
      refine ⟨66981080389585041192971639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44654053593056694128647759 66981080389585041192971639)
      ·
        refine ⟨100471620584377561789457459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66981080389585041192971639 100471620584377561789457459)
        ·
          refine ⟨150707430876566342684186189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100471620584377561789457459 150707430876566342684186189)
          ·
            refine ⟨56515286578712378506569821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150707430876566342684186189 56515286578712378506569821)
            ·
              refine ⟨21193232467017141939963683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56515286578712378506569821 21193232467017141939963683)
              ·
                refine ⟨31789848700525712909945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21193232467017141939963683 31789848700525712909945525)
                ·
                  refine ⟨2980298315674285585307393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31789848700525712909945525 2980298315674285585307393)
                  ·
                    refine ⟨2235223736755714188980545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980298315674285585307393 2235223736755714188980545)
                    ·
                      refine ⟨1676417802566785641735409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235223736755714188980545 1676417802566785641735409)
                      ·
                        rfl

theorem cell23_3264812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_3264812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264812 prefixEnd_3264812 := by exact prefixLift 3264812
  have htrace : WordTrace (prefixWord ++ tailWord_3264812) baseStart_3264812 baseEnd_3264812 := by
    simpa [prefixWord, tailWord_3264812, baseEnd_3264812] using wordTrace_append hprefix tailTrace_3264812
  have hstable : (prefixWord ++ tailWord_3264812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264812).length < 2 ^ (prefixWord ++ tailWord_3264812).sum := by decide
  have hdescent : baseEnd_3264812 < baseStart_3264812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264815 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_3264815 : Nat := 118140960795 + 3264815 * 2 ^ 59
def prefixEnd_3264815 : Nat := 4983230072969 + 3 ^ 40 * 3264815 * 2
def baseEnd_3264815 : Nat := 1676419343008749129997895

theorem tailTrace_3264815 : CollatzResearch.WordTrace tailWord_3264815 prefixEnd_3264815 1676419343008749129997895 := by
  unfold tailWord_3264815
  simp only [CollatzResearch.WordTrace]
  refine ⟨119077585667140315855419899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79385057111426877236946599 119077585667140315855419899)
  ·
    refine ⟨178616378500710473783129849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119077585667140315855419899 178616378500710473783129849)
    ·
      refine ⟨133962283875532855337347387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178616378500710473783129849 133962283875532855337347387)
      ·
        refine ⟨200943425813299283006021081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133962283875532855337347387 200943425813299283006021081)
        ·
          refine ⟨150707569359974462254515811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200943425813299283006021081 150707569359974462254515811)
          ·
            refine ⟨226061354039961693381773717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150707569359974462254515811 226061354039961693381773717)
            ·
              refine ⟨10596625970623204377270643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226061354039961693381773717 10596625970623204377270643)
              ·
                refine ⟨15894938955934806565905965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596625970623204377270643 15894938955934806565905965)
                ·
                  refine ⟨5960602108475552462214737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15894938955934806565905965 5960602108475552462214737)
                  ·
                    refine ⟨4470451581356664346661053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5960602108475552462214737 4470451581356664346661053)
                    ·
                      refine ⟨1676419343008749129997895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470451581356664346661053 1676419343008749129997895)
                      ·
                        rfl

theorem cell23_3264815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_3264815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264815 prefixEnd_3264815 := by exact prefixLift 3264815
  have htrace : WordTrace (prefixWord ++ tailWord_3264815) baseStart_3264815 baseEnd_3264815 := by
    simpa [prefixWord, tailWord_3264815, baseEnd_3264815] using wordTrace_append hprefix tailTrace_3264815
  have hstable : (prefixWord ++ tailWord_3264815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264815).length < 2 ^ (prefixWord ++ tailWord_3264815).sum := by decide
  have hdescent : baseEnd_3264815 < baseStart_3264815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264936 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3264936 : Nat := 118140960795 + 3264936 * 2 ^ 59
def prefixEnd_3264936 : Nat := 4983230072969 + 3 ^ 40 * 3264936 * 2
def baseEnd_3264936 : Nat := 1676481474167943156584839

theorem tailTrace_3264936 : CollatzResearch.WordTrace tailWord_3264936 prefixEnd_3264936 1676481474167943156584839 := by
  unfold tailWord_3264936
  simp only [CollatzResearch.WordTrace]
  refine ⟨59540999449850976760287331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79387999266467969013716441 59540999449850976760287331)
  ·
    refine ⟨89311499174776465140430997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59540999449850976760287331 89311499174776465140430997)
    ·
      refine ⟨4186476523817646803457703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89311499174776465140430997 4186476523817646803457703)
      ·
        refine ⟨6279714785726470205186555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186476523817646803457703 6279714785726470205186555)
        ·
          refine ⟨9419572178589705307779833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279714785726470205186555 9419572178589705307779833)
          ·
            refine ⟨7064679133942278980834875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9419572178589705307779833 7064679133942278980834875)
            ·
              refine ⟨10597018700913418471252313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064679133942278980834875 10597018700913418471252313)
              ·
                refine ⟨7947764025685063853439235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10597018700913418471252313 7947764025685063853439235)
                ·
                  refine ⟨11921646038527595780158853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947764025685063853439235 11921646038527595780158853)
                  ·
                    refine ⟨2235308632223924208779785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11921646038527595780158853 2235308632223924208779785)
                    ·
                      refine ⟨1676481474167943156584839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235308632223924208779785 1676481474167943156584839)
                      ·
                        rfl

theorem cell23_3264936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3264936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264936 prefixEnd_3264936 := by exact prefixLift 3264936
  have htrace : WordTrace (prefixWord ++ tailWord_3264936) baseStart_3264936 baseEnd_3264936 := by
    simpa [prefixWord, tailWord_3264936, baseEnd_3264936] using wordTrace_append hprefix tailTrace_3264936
  have hstable : (prefixWord ++ tailWord_3264936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264936).length < 2 ^ (prefixWord ++ tailWord_3264936).sum := by decide
  have hdescent : baseEnd_3264936 < baseStart_3264936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264975 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_3264975 : Nat := 118140960795 + 3264975 * 2 ^ 59
def prefixEnd_3264975 : Nat := 4983230072969 + 3 ^ 40 * 3264975 * 2
def baseEnd_3264975 : Nat := 1676501499913468503997159

theorem tailTrace_3264975 : CollatzResearch.WordTrace tailWord_3264975 prefixEnd_3264975 1676501499913468503997159 := by
  unfold tailWord_3264975
  simp only [CollatzResearch.WordTrace]
  refine ⟨119083421346560663181244379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79388947564373775454162919 119083421346560663181244379)
  ·
    refine ⟨178625132019840994771866569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119083421346560663181244379 178625132019840994771866569)
    ·
      refine ⟨133968849014880746078899927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178625132019840994771866569 133968849014880746078899927)
      ·
        refine ⟨200953273522321119118349891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133968849014880746078899927 200953273522321119118349891)
        ·
          refine ⟨301429910283481678677524837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200953273522321119118349891 301429910283481678677524837)
          ·
            refine ⟨56518108178152814752035907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301429910283481678677524837 56518108178152814752035907)
            ·
              refine ⟨84777162267229222128053861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56518108178152814752035907 84777162267229222128053861)
              ·
                refine ⟨15895717925105479149010099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84777162267229222128053861 15895717925105479149010099)
                ·
                  refine ⟨23843576887658218723515149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15895717925105479149010099 23843576887658218723515149)
                  ·
                    refine ⟨8941341332871832021318181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23843576887658218723515149 8941341332871832021318181)
                    ·
                      refine ⟨1676501499913468503997159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8941341332871832021318181 1676501499913468503997159)
                      ·
                        rfl

theorem cell23_3264975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_3264975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264975 prefixEnd_3264975 := by exact prefixLift 3264975
  have htrace : WordTrace (prefixWord ++ tailWord_3264975) baseStart_3264975 baseEnd_3264975 := by
    simpa [prefixWord, tailWord_3264975, baseEnd_3264975] using wordTrace_append hprefix tailTrace_3264975
  have hstable : (prefixWord ++ tailWord_3264975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264975).length < 2 ^ (prefixWord ++ tailWord_3264975).sum := by decide
  have hdescent : baseEnd_3264975 < baseStart_3264975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264992 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2]
def baseStart_3264992 : Nat := 118140960795 + 3264992 * 2 ^ 59
def prefixEnd_3264992 : Nat := 4983230072969 + 3 ^ 40 * 3264992 * 2
def baseEnd_3264992 : Nat := 1676510229084594937484581

theorem tailTrace_3264992 : CollatzResearch.WordTrace tailWord_3264992 prefixEnd_3264992 1676510229084594937484581 := by
  unfold tailWord_3264992
  simp only [CollatzResearch.WordTrace]
  refine ⟨59542020693749537542306615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79389360924999383389742153 59542020693749537542306615)
  ·
    refine ⟨89313031040624306313459923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59542020693749537542306615 89313031040624306313459923)
    ·
      refine ⟨133969546560936459470189885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89313031040624306313459923 133969546560936459470189885)
      ·
        refine ⟨50238579960351172301321207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133969546560936459470189885 50238579960351172301321207)
        ·
          refine ⟨75357869940526758451981811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50238579960351172301321207 75357869940526758451981811)
          ·
            refine ⟨113036804910790137677972717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75357869940526758451981811 113036804910790137677972717)
            ·
              refine ⟨42388801841546301629239769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113036804910790137677972717 42388801841546301629239769)
              ·
                refine ⟨31791601381159726221929827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42388801841546301629239769 31791601381159726221929827)
                ·
                  refine ⟨47687402071739589332894741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31791601381159726221929827 47687402071739589332894741)
                  ·
                    refine ⟨2235346972112793249979441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47687402071739589332894741 2235346972112793249979441)
                    ·
                      refine ⟨1676510229084594937484581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235346972112793249979441 1676510229084594937484581)
                      ·
                        rfl

theorem cell23_3264992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_3264992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3264992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3264992 prefixEnd_3264992 := by exact prefixLift 3264992
  have htrace : WordTrace (prefixWord ++ tailWord_3264992) baseStart_3264992 baseEnd_3264992 := by
    simpa [prefixWord, tailWord_3264992, baseEnd_3264992] using wordTrace_append hprefix tailTrace_3264992
  have hstable : (prefixWord ++ tailWord_3264992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264992).length < 2 ^ (prefixWord ++ tailWord_3264992).sum := by decide
  have hdescent : baseEnd_3264992 < baseStart_3264992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265053 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_3265053 : Nat := 118140960795 + 3265053 * 2 ^ 59
def prefixEnd_3265053 : Nat := 4983230072969 + 3 ^ 40 * 3265053 * 2
def baseEnd_3265053 : Nat := 558847183801506399607267

theorem tailTrace_3265053 : CollatzResearch.WordTrace tailWord_3265053 prefixEnd_3265053 558847183801506399607267 := by
  unfold tailWord_3265053
  simp only [CollatzResearch.WordTrace]
  refine ⟨119086266240278082502583813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79390844160185388335055875 119086266240278082502583813)
  ·
    refine ⟨22328674920052140469234465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119086266240278082502583813 22328674920052140469234465)
    ·
      refine ⟨16746506190039105351925849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22328674920052140469234465 16746506190039105351925849)
      ·
        refine ⟨12559879642529329013944387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16746506190039105351925849 12559879642529329013944387)
        ·
          refine ⟨18839819463793993520916581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12559879642529329013944387 18839819463793993520916581)
          ·
            refine ⟨3532466149461373785171859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18839819463793993520916581 3532466149461373785171859)
            ·
              refine ⟨5298699224192060677757789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532466149461373785171859 5298699224192060677757789)
              ·
                refine ⟨1987012209072022754159171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5298699224192060677757789 1987012209072022754159171)
                ·
                  refine ⟨2980518313608034131238757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987012209072022754159171 2980518313608034131238757)
                  ·
                    refine ⟨558847183801506399607267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980518313608034131238757 558847183801506399607267)
                    ·
                      rfl

theorem cell23_3265053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_3265053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265053 prefixEnd_3265053 := by exact prefixLift 3265053
  have htrace : WordTrace (prefixWord ++ tailWord_3265053) baseStart_3265053 baseEnd_3265053 := by
    simpa [prefixWord, tailWord_3265053, baseEnd_3265053] using wordTrace_append hprefix tailTrace_3265053
  have hstable : (prefixWord ++ tailWord_3265053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265053).length < 2 ^ (prefixWord ++ tailWord_3265053).sum := by decide
  have hdescent : baseEnd_3265053 < baseStart_3265053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265063 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3265063 : Nat := 118140960795 + 3265063 * 2 ^ 59
def prefixEnd_3265063 : Nat := 4983230072969 + 3 ^ 40 * 3265063 * 2
def baseEnd_3265063 : Nat := 1676546686211064159696755

theorem tailTrace_3265063 : CollatzResearch.WordTrace tailWord_3265063 prefixEnd_3265063 1676546686211064159696755 := by
  unfold tailWord_3265063
  simp only [CollatzResearch.WordTrace]
  refine ⟨119086630970241854210447843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79391087313494569473631895 119086630970241854210447843)
  ·
    refine ⟨178629946455362781315671765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119086630970241854210447843 178629946455362781315671765)
    ·
      refine ⟨4186639370047565187086057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 178629946455362781315671765 4186639370047565187086057)
      ·
        refine ⟨3139979527535673890314543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186639370047565187086057 3139979527535673890314543)
        ·
          refine ⟨4709969291303510835471815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139979527535673890314543 4709969291303510835471815)
          ·
            refine ⟨7064953936955266253207723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709969291303510835471815 7064953936955266253207723)
            ·
              refine ⟨10597430905432899379811585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064953936955266253207723 10597430905432899379811585)
              ·
                refine ⟨7948073179074674534858689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10597430905432899379811585 7948073179074674534858689)
                ·
                  refine ⟨5961054884306005901144017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7948073179074674534858689 5961054884306005901144017)
                  ·
                    refine ⟨4470791163229504425858013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961054884306005901144017 4470791163229504425858013)
                    ·
                      refine ⟨1676546686211064159696755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470791163229504425858013 1676546686211064159696755)
                      ·
                        rfl

theorem cell23_3265063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3265063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265063 prefixEnd_3265063 := by exact prefixLift 3265063
  have htrace : WordTrace (prefixWord ++ tailWord_3265063) baseStart_3265063 baseEnd_3265063 := by
    simpa [prefixWord, tailWord_3265063, baseEnd_3265063] using wordTrace_append hprefix tailTrace_3265063
  have hstable : (prefixWord ++ tailWord_3265063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265063).length < 2 ^ (prefixWord ++ tailWord_3265063).sum := by decide
  have hdescent : baseEnd_3265063 < baseStart_3265063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265070 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3265070 : Nat := 118140960795 + 3265070 * 2 ^ 59
def prefixEnd_3265070 : Nat := 4983230072969 + 3 ^ 40 * 3265070 * 2
def baseEnd_3265070 : Nat := 558850093525215210769741

theorem tailTrace_3265070 : CollatzResearch.WordTrace tailWord_3265070 prefixEnd_3265070 558850093525215210769741 := by
  unfold tailWord_3265070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885860785152061800744083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79391257520810996270635109 14885860785152061800744083)
  ·
    refine ⟨22328791177728092701116125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14885860785152061800744083 22328791177728092701116125)
    ·
      refine ⟨8373296691648034762918547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22328791177728092701116125 8373296691648034762918547)
      ·
        refine ⟨12559945037472052144377821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373296691648034762918547 12559945037472052144377821)
        ·
          refine ⟨4709979389052019554141683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12559945037472052144377821 4709979389052019554141683)
          ·
            refine ⟨7064969083578029331212525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709979389052019554141683 7064969083578029331212525)
            ·
              refine ⟨2649363406341760999204697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7064969083578029331212525 2649363406341760999204697)
              ·
                refine ⟨1987022554756320749403523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649363406341760999204697 1987022554756320749403523)
                ·
                  refine ⟨2980533832134481124105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987022554756320749403523 2980533832134481124105285)
                  ·
                    refine ⟨558850093525215210769741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980533832134481124105285 558850093525215210769741)
                    ·
                      rfl

theorem cell23_3265070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3265070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265070 prefixEnd_3265070 := by exact prefixLift 3265070
  have htrace : WordTrace (prefixWord ++ tailWord_3265070) baseStart_3265070 baseEnd_3265070 := by
    simpa [prefixWord, tailWord_3265070, baseEnd_3265070] using wordTrace_append hprefix tailTrace_3265070
  have hstable : (prefixWord ++ tailWord_3265070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265070).length < 2 ^ (prefixWord ++ tailWord_3265070).sum := by decide
  have hdescent : baseEnd_3265070 < baseStart_3265070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265099 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 4]
def baseStart_3265099 : Nat := 118140960795 + 3265099 * 2 ^ 59
def prefixEnd_3265099 : Nat := 4983230072969 + 3 ^ 40 * 3265099 * 2
def baseEnd_3265099 : Nat := 1676565171514626018846589

theorem tailTrace_3265099 : CollatzResearch.WordTrace tailWord_3265099 prefixEnd_3265099 1676565171514626018846589 := by
  unfold tailWord_3265099
  simp only [CollatzResearch.WordTrace]
  refine ⟨119087943998111432358758351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79391962665407621572505567 119087943998111432358758351)
  ·
    refine ⟨178631915997167148538137527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119087943998111432358758351 178631915997167148538137527)
    ·
      refine ⟨267947873995750722807206291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178631915997167148538137527 267947873995750722807206291)
      ·
        refine ⟨401921810993626084210809437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267947873995750722807206291 401921810993626084210809437)
        ·
          refine ⟨150720679122609781579053539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401921810993626084210809437 150720679122609781579053539)
          ·
            refine ⟨226081018683914672368580309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150720679122609781579053539 226081018683914672368580309)
            ·
              refine ⟨5298773875404250133638601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 226081018683914672368580309 5298773875404250133638601)
              ·
                refine ⟨3974080406553187600228951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298773875404250133638601 3974080406553187600228951)
                ·
                  refine ⟨5961120609829781400343427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974080406553187600228951 5961120609829781400343427)
                  ·
                    refine ⟨8941680914744672100515141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5961120609829781400343427 8941680914744672100515141)
                    ·
                      refine ⟨1676565171514626018846589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8941680914744672100515141 1676565171514626018846589)
                      ·
                        rfl

theorem cell23_3265099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 4].length) (baseStart_3265099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265099 prefixEnd_3265099 := by exact prefixLift 3265099
  have htrace : WordTrace (prefixWord ++ tailWord_3265099) baseStart_3265099 baseEnd_3265099 := by
    simpa [prefixWord, tailWord_3265099, baseEnd_3265099] using wordTrace_append hprefix tailTrace_3265099
  have hstable : (prefixWord ++ tailWord_3265099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265099).length < 2 ^ (prefixWord ++ tailWord_3265099).sum := by decide
  have hdescent : baseEnd_3265099 < baseStart_3265099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265102 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3265102 : Nat := 118140960795 + 3265102 * 2 ^ 59
def prefixEnd_3265102 : Nat := 4983230072969 + 3 ^ 40 * 3265102 * 2
def baseEnd_3265102 : Nat := 1676566711956589507109075

theorem tailTrace_3265102 : CollatzResearch.WordTrace tailWord_3265102 prefixEnd_3265102 1676566711956589507109075 := by
  unfold tailWord_3265102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886006677137570483889695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79392035611400375914078373 14886006677137570483889695)
  ·
    refine ⟨22329010015706355725834543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14886006677137570483889695 22329010015706355725834543)
    ·
      refine ⟨33493515023559533588751815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22329010015706355725834543 33493515023559533588751815)
      ·
        refine ⟨50240272535339300383127723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33493515023559533588751815 50240272535339300383127723)
        ·
          refine ⟨75360408803008950574691585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50240272535339300383127723 75360408803008950574691585)
          ·
            refine ⟨56520306602256712931018689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75360408803008950574691585 56520306602256712931018689)
            ·
              refine ⟨42390229951692534698264017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56520306602256712931018689 42390229951692534698264017)
              ·
                refine ⟨31792672463769401023698013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42390229951692534698264017 31792672463769401023698013)
                ·
                  refine ⟨11922252173913525383886755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31792672463769401023698013 11922252173913525383886755)
                  ·
                    refine ⟨17883378260870288075830133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11922252173913525383886755 17883378260870288075830133)
                    ·
                      refine ⟨1676566711956589507109075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17883378260870288075830133 1676566711956589507109075)
                      ·
                        rfl

theorem cell23_3265102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3265102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265102 prefixEnd_3265102 := by exact prefixLift 3265102
  have htrace : WordTrace (prefixWord ++ tailWord_3265102) baseStart_3265102 baseEnd_3265102 := by
    simpa [prefixWord, tailWord_3265102, baseEnd_3265102] using wordTrace_append hprefix tailTrace_3265102
  have hstable : (prefixWord ++ tailWord_3265102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265102).length < 2 ^ (prefixWord ++ tailWord_3265102).sum := by decide
  have hdescent : baseEnd_3265102 < baseStart_3265102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265112 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3265112 : Nat := 118140960795 + 3265112 * 2 ^ 59
def prefixEnd_3265112 : Nat := 4983230072969 + 3 ^ 40 * 3265112 * 2
def baseEnd_3265112 : Nat := 1676571846763134467984029

theorem tailTrace_3265112 : CollatzResearch.WordTrace tailWord_3265112 prefixEnd_3265112 1676571846763134467984029 := by
  unfold tailWord_3265112
  simp only [CollatzResearch.WordTrace]
  refine ⟨59544209073532167789490795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79392278764709557052654393 59544209073532167789490795)
  ·
    refine ⟨89316313610298251684236193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59544209073532167789490795 89316313610298251684236193)
    ·
      refine ⟨66987235207723688763177145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89316313610298251684236193 66987235207723688763177145)
      ·
        refine ⟨50240426405792766572382859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66987235207723688763177145 50240426405792766572382859)
        ·
          refine ⟨75360639608689149858574289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50240426405792766572382859 75360639608689149858574289)
          ·
            refine ⟨56520479706516862393930717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75360639608689149858574289 56520479706516862393930717)
            ·
              refine ⟨21195179889943823397724019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56520479706516862393930717 21195179889943823397724019)
              ·
                refine ⟨31792769834915735096586029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21195179889943823397724019 31792769834915735096586029)
                ·
                  refine ⟨11922288688093400661219761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31792769834915735096586029 11922288688093400661219761)
                  ·
                    refine ⟨8941716516070050495914821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11922288688093400661219761 8941716516070050495914821)
                    ·
                      refine ⟨1676571846763134467984029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8941716516070050495914821 1676571846763134467984029)
                      ·
                        rfl

theorem cell23_3265112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3265112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265112 prefixEnd_3265112 := by exact prefixLift 3265112
  have htrace : WordTrace (prefixWord ++ tailWord_3265112) baseStart_3265112 baseEnd_3265112 := by
    simpa [prefixWord, tailWord_3265112, baseEnd_3265112] using wordTrace_append hprefix tailTrace_3265112
  have hstable : (prefixWord ++ tailWord_3265112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265112).length < 2 ^ (prefixWord ++ tailWord_3265112).sum := by decide
  have hdescent : baseEnd_3265112 < baseStart_3265112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265119 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_3265119 : Nat := 118140960795 + 3265119 * 2 ^ 59
def prefixEnd_3265119 : Nat := 4983230072969 + 3 ^ 40 * 3265119 * 2
def baseEnd_3265119 : Nat := 1676575441127715940596497

theorem tailTrace_3265119 : CollatzResearch.WordTrace tailWord_3265119 prefixEnd_3265119 1676575441127715940596497 := by
  unfold tailWord_3265119
  simp only [CollatzResearch.WordTrace]
  refine ⟨119088673458038975774486411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79392448972025983849657607 119088673458038975774486411)
  ·
    refine ⟨178633010187058463661729617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119088673458038975774486411 178633010187058463661729617)
    ·
      refine ⟨133974757640293847746297213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178633010187058463661729617 133974757640293847746297213)
      ·
        refine ⟨50240534115110192904861455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133974757640293847746297213 50240534115110192904861455)
        ·
          refine ⟨75360801172665289357292183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50240534115110192904861455 75360801172665289357292183)
          ·
            refine ⟨113041201758997934035938275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75360801172665289357292183 113041201758997934035938275)
            ·
              refine ⟨169561802638496901053907413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113041201758997934035938275 169561802638496901053907413)
              ·
                refine ⟨3974104749339771118450955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 169561802638496901053907413 3974104749339771118450955)
                ·
                  refine ⟨5961157124009656677676433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974104749339771118450955 5961157124009656677676433)
                  ·
                    refine ⟨4470867843007242508257325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961157124009656677676433 4470867843007242508257325)
                    ·
                      refine ⟨1676575441127715940596497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470867843007242508257325 1676575441127715940596497)
                      ·
                        rfl

theorem cell23_3265119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_3265119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265119 prefixEnd_3265119 := by exact prefixLift 3265119
  have htrace : WordTrace (prefixWord ++ tailWord_3265119) baseStart_3265119 baseEnd_3265119 := by
    simpa [prefixWord, tailWord_3265119, baseEnd_3265119] using wordTrace_append hprefix tailTrace_3265119
  have hstable : (prefixWord ++ tailWord_3265119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265119).length < 2 ^ (prefixWord ++ tailWord_3265119).sum := by decide
  have hdescent : baseEnd_3265119 < baseStart_3265119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265154 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3265154 : Nat := 118140960795 + 3265154 * 2 ^ 59
def prefixEnd_3265154 : Nat := 4983230072969 + 3 ^ 40 * 3265154 * 2
def baseEnd_3265154 : Nat := 1676593412950623303658837

theorem tailTrace_3265154 : CollatzResearch.WordTrace tailWord_3265154 prefixEnd_3265154 1676593412950623303658837 := by
  unfold tailWord_3265154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29772487503228044188002629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79393300008608117834673677 29772487503228044188002629)
  ·
    refine ⟨5582341406855258285250493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29772487503228044188002629 5582341406855258285250493)
    ·
      refine ⟨2093378027570721856968935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5582341406855258285250493 2093378027570721856968935)
      ·
        refine ⟨3140067041356082785453403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093378027570721856968935 3140067041356082785453403)
        ·
          refine ⟨4710100562034124178180105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140067041356082785453403 4710100562034124178180105)
          ·
            refine ⟨3532575421525593133635079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4710100562034124178180105 3532575421525593133635079)
            ·
              refine ⟨5298863132288389700452619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532575421525593133635079 5298863132288389700452619)
              ·
                refine ⟨7948294698432584550678929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298863132288389700452619 7948294698432584550678929)
                ·
                  refine ⟨5961221023824438413009197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7948294698432584550678929 5961221023824438413009197)
                  ·
                    refine ⟨2235457883934164404878449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5961221023824438413009197 2235457883934164404878449)
                    ·
                      refine ⟨1676593412950623303658837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235457883934164404878449 1676593412950623303658837)
                      ·
                        rfl

theorem cell23_3265154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3265154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265154 prefixEnd_3265154 := by exact prefixLift 3265154
  have htrace : WordTrace (prefixWord ++ tailWord_3265154) baseStart_3265154 baseEnd_3265154 := by
    simpa [prefixWord, tailWord_3265154, baseEnd_3265154] using wordTrace_append hprefix tailTrace_3265154
  have hstable : (prefixWord ++ tailWord_3265154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265154).length < 2 ^ (prefixWord ++ tailWord_3265154).sum := by decide
  have hdescent : baseEnd_3265154 < baseStart_3265154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265166 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3265166 : Nat := 118140960795 + 3265166 * 2 ^ 59
def prefixEnd_3265166 : Nat := 4983230072969 + 3 ^ 40 * 3265166 * 2
def baseEnd_3265166 : Nat := 1676599574718477256708781

theorem tailTrace_3265166 : CollatzResearch.WordTrace tailWord_3265166 prefixEnd_3265166 1676599574718477256708781 := by
  unfold tailWord_3265166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886298461108587850180919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79393591792579135200964901 14886298461108587850180919)
  ·
    refine ⟨22329447691662881775271379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14886298461108587850180919 22329447691662881775271379)
    ·
      refine ⟨33494171537494322662907069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22329447691662881775271379 33494171537494322662907069)
      ·
        refine ⟨12560314326560370998590151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33494171537494322662907069 12560314326560370998590151)
        ·
          refine ⟨18840471489840556497885227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12560314326560370998590151 18840471489840556497885227)
          ·
            refine ⟨28260707234760834746827841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18840471489840556497885227 28260707234760834746827841)
            ·
              refine ⟨21195530426070626060120881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28260707234760834746827841 21195530426070626060120881)
              ·
                refine ⟨15896647819552969545090661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21195530426070626060120881 15896647819552969545090661)
                ·
                  refine ⟨2980621466166181789704499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15896647819552969545090661 2980621466166181789704499)
                  ·
                    refine ⟨4470932199249272684556749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2980621466166181789704499 4470932199249272684556749)
                    ·
                      refine ⟨1676599574718477256708781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470932199249272684556749 1676599574718477256708781)
                      ·
                        rfl

theorem cell23_3265166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3265166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265166 prefixEnd_3265166 := by exact prefixLift 3265166
  have htrace : WordTrace (prefixWord ++ tailWord_3265166) baseStart_3265166 baseEnd_3265166 := by
    simpa [prefixWord, tailWord_3265166, baseEnd_3265166] using wordTrace_append hprefix tailTrace_3265166
  have hstable : (prefixWord ++ tailWord_3265166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265166).length < 2 ^ (prefixWord ++ tailWord_3265166).sum := by decide
  have hdescent : baseEnd_3265166 < baseStart_3265166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265170 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_3265170 : Nat := 118140960795 + 3265170 * 2 ^ 59
def prefixEnd_3265170 : Nat := 4983230072969 + 3 ^ 40 * 3265170 * 2
def baseEnd_3265170 : Nat := 1676601628641095241058763

theorem tailTrace_3265170 : CollatzResearch.WordTrace tailWord_3265170 prefixEnd_3265170 1676601628641095241058763 := by
  unfold tailWord_3265170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29772633395213552871148241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79393689053902807656395309 29772633395213552871148241)
  ·
    refine ⟨22329475046410164653361181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29772633395213552871148241 22329475046410164653361181)
    ·
      refine ⟨8373553142403811745010443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22329475046410164653361181 8373553142403811745010443)
      ·
        refine ⟨12560329713605717617515665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373553142403811745010443 12560329713605717617515665)
        ·
          refine ⟨9420247285204288213136749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12560329713605717617515665 9420247285204288213136749)
          ·
            refine ⟨3532592731951608079926281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9420247285204288213136749 3532592731951608079926281)
            ·
              refine ⟨2649444548963706059944711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532592731951608079926281 2649444548963706059944711)
              ·
                refine ⟨3974166823445559089917067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649444548963706059944711 3974166823445559089917067)
                ·
                  refine ⟨5961250235168338634875601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974166823445559089917067 5961250235168338634875601)
                  ·
                    refine ⟨4470937676376253976156701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961250235168338634875601 4470937676376253976156701)
                    ·
                      refine ⟨1676601628641095241058763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4470937676376253976156701 1676601628641095241058763)
                      ·
                        rfl

theorem cell23_3265170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_3265170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265170 prefixEnd_3265170 := by exact prefixLift 3265170
  have htrace : WordTrace (prefixWord ++ tailWord_3265170) baseStart_3265170 baseEnd_3265170 := by
    simpa [prefixWord, tailWord_3265170, baseEnd_3265170] using wordTrace_append hprefix tailTrace_3265170
  have hstable : (prefixWord ++ tailWord_3265170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265170).length < 2 ^ (prefixWord ++ tailWord_3265170).sum := by decide
  have hdescent : baseEnd_3265170 < baseStart_3265170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265276 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_3265276 : Nat := 118140960795 + 3265276 * 2 ^ 59
def prefixEnd_3265276 : Nat := 4983230072969 + 3 ^ 40 * 3265276 * 2
def baseEnd_3265276 : Nat := 558885352530157275444425

theorem tailTrace_3265276 : CollatzResearch.WordTrace tailWord_3265276 prefixEnd_3265276 558885352530157275444425 := by
  unfold tailWord_3265276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59547199859235095793975841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79396266478980127725301121 59547199859235095793975841)
  ·
    refine ⟨44660399894426321845481881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59547199859235095793975841 44660399894426321845481881)
    ·
      refine ⟨33495299920819741384111411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44660399894426321845481881 33495299920819741384111411)
      ·
        refine ⟨50242949881229612076167117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33495299920819741384111411 50242949881229612076167117)
        ·
          refine ⟨18841106205461104528562669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50242949881229612076167117 18841106205461104528562669)
          ·
            refine ⟨7065414827047914198211001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18841106205461104528562669 7065414827047914198211001)
            ·
              refine ⟨5299061120285935648658251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7065414827047914198211001 5299061120285935648658251)
              ·
                refine ⟨7948591680428903472987377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299061120285935648658251 7948591680428903472987377)
                ·
                  refine ⟨5961443760321677604740533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7948591680428903472987377 5961443760321677604740533)
                  ·
                    refine ⟨558885352530157275444425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5961443760321677604740533 558885352530157275444425)
                    ·
                      rfl

theorem cell23_3265276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_3265276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265276 prefixEnd_3265276 := by exact prefixLift 3265276
  have htrace : WordTrace (prefixWord ++ tailWord_3265276) baseStart_3265276 baseEnd_3265276 := by
    simpa [prefixWord, tailWord_3265276, baseEnd_3265276] using wordTrace_append hprefix tailTrace_3265276
  have hstable : (prefixWord ++ tailWord_3265276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265276).length < 2 ^ (prefixWord ++ tailWord_3265276).sum := by decide
  have hdescent : baseEnd_3265276 < baseStart_3265276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265306 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_3265306 : Nat := 118140960795 + 3265306 * 2 ^ 59
def prefixEnd_3265306 : Nat := 4983230072969 + 3 ^ 40 * 3265306 * 2
def baseEnd_3265306 : Nat := 558890487336702236319379

theorem tailTrace_3265306 : CollatzResearch.WordTrace tailWord_3265306 prefixEnd_3265306 558890487336702236319379 := by
  unfold tailWord_3265306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29773873477090376677885943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79396995938907671141029181 29773873477090376677885943)
  ·
    refine ⟨44660810215635565016828915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29773873477090376677885943 44660810215635565016828915)
    ·
      refine ⟨66991215323453347525243373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44660810215635565016828915 66991215323453347525243373)
      ·
        refine ⟨25121705746295005321966265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66991215323453347525243373 25121705746295005321966265)
        ·
          refine ⟨18841279309721253991474699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25121705746295005321966265 18841279309721253991474699)
          ·
            refine ⟨28261918964581880987212049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18841279309721253991474699 28261918964581880987212049)
            ·
              refine ⟨21196439223436410740409037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28261918964581880987212049 21196439223436410740409037)
              ·
                refine ⟨7948664708788654027653389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21196439223436410740409037 7948664708788654027653389)
                ·
                  refine ⟨2980749265795745260370021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7948664708788654027653389 2980749265795745260370021)
                  ·
                    refine ⟨558890487336702236319379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980749265795745260370021 558890487336702236319379)
                    ·
                      rfl

theorem cell23_3265306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_3265306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265306 prefixEnd_3265306 := by exact prefixLift 3265306
  have htrace : WordTrace (prefixWord ++ tailWord_3265306) baseStart_3265306 baseEnd_3265306 := by
    simpa [prefixWord, tailWord_3265306, baseEnd_3265306] using wordTrace_append hprefix tailTrace_3265306
  have hstable : (prefixWord ++ tailWord_3265306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265306).length < 2 ^ (prefixWord ++ tailWord_3265306).sum := by decide
  have hdescent : baseEnd_3265306 < baseStart_3265306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265333 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3265333 : Nat := 118140960795 + 3265333 * 2 ^ 59
def prefixEnd_3265333 : Nat := 4983230072969 + 3 ^ 40 * 3265333 * 2
def baseEnd_3265333 : Nat := 1676685325987778103320513

theorem tailTrace_3265333 : CollatzResearch.WordTrace tailWord_3265333 prefixEnd_3265333 1676685325987778103320513 := by
  unfold tailWord_3265333
  simp only [CollatzResearch.WordTrace]
  refine ⟨119096478679263690322776653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79397652452842460215184435 119096478679263690322776653)
  ·
    refine ⟨44661179504723883871041245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119096478679263690322776653 44661179504723883871041245)
    ·
      refine ⟨16747942314271456451640467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44661179504723883871041245 16747942314271456451640467)
      ·
        refine ⟨25121913471407184677460701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16747942314271456451640467 25121913471407184677460701)
        ·
          refine ⟨9420717551777694254047763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25121913471407184677460701 9420717551777694254047763)
          ·
            refine ⟨14131076327666541381071645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420717551777694254047763 14131076327666541381071645)
            ·
              refine ⟨5299153622874953017901867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14131076327666541381071645 5299153622874953017901867)
              ·
                refine ⟨7948730434312429526852801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299153622874953017901867 7948730434312429526852801)
                ·
                  refine ⟨5961547825734322145139601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7948730434312429526852801 5961547825734322145139601)
                  ·
                    refine ⟨4471160869300741608854701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961547825734322145139601 4471160869300741608854701)
                    ·
                      refine ⟨1676685325987778103320513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471160869300741608854701 1676685325987778103320513)
                      ·
                        rfl

theorem cell23_3265333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3265333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265333 prefixEnd_3265333 := by exact prefixLift 3265333
  have htrace : WordTrace (prefixWord ++ tailWord_3265333) baseStart_3265333 baseEnd_3265333 := by
    simpa [prefixWord, tailWord_3265333, baseEnd_3265333] using wordTrace_append hprefix tailTrace_3265333
  have hstable : (prefixWord ++ tailWord_3265333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265333).length < 2 ^ (prefixWord ++ tailWord_3265333).sum := by decide
  have hdescent : baseEnd_3265333 < baseStart_3265333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265349 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_3265349 : Nat := 118140960795 + 3265349 * 2 ^ 59
def prefixEnd_3265349 : Nat := 4983230072969 + 3 ^ 40 * 3265349 * 2
def baseEnd_3265349 : Nat := 558897847226083346906813

theorem tailTrace_3265349 : CollatzResearch.WordTrace tailWord_3265349 prefixEnd_3265349 558897847226083346906813 := by
  unfold tailWord_3265349
  simp only [CollatzResearch.WordTrace]
  refine ⟨119097062247205725055359101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79398041498137150036906067 119097062247205725055359101)
  ·
    refine ⟨44661398342702146895759663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119097062247205725055359101 44661398342702146895759663)
    ·
      refine ⟨66992097514053220343639495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44661398342702146895759663 66992097514053220343639495)
      ·
        refine ⟨100488146271079830515459243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66992097514053220343639495 100488146271079830515459243)
        ·
          refine ⟨150732219406619745773188865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100488146271079830515459243 150732219406619745773188865)
          ·
            refine ⟨113049164554964809329891649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150732219406619745773188865 113049164554964809329891649)
            ·
              refine ⟨84786873416223606997418737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113049164554964809329891649 84786873416223606997418737)
              ·
                refine ⟨63590155062167705248064053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84786873416223606997418737 63590155062167705248064053)
                ·
                  refine ⟨5961577037078222367006005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63590155062167705248064053 5961577037078222367006005)
                  ·
                    refine ⟨558897847226083346906813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5961577037078222367006005 558897847226083346906813)
                    ·
                      rfl

theorem cell23_3265349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_3265349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265349 prefixEnd_3265349 := by exact prefixLift 3265349
  have htrace : WordTrace (prefixWord ++ tailWord_3265349) baseStart_3265349 baseEnd_3265349 := by
    simpa [prefixWord, tailWord_3265349, baseEnd_3265349] using wordTrace_append hprefix tailTrace_3265349
  have hstable : (prefixWord ++ tailWord_3265349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265349).length < 2 ^ (prefixWord ++ tailWord_3265349).sum := by decide
  have hdescent : baseEnd_3265349 < baseStart_3265349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265383 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3265383 : Nat := 118140960795 + 3265383 * 2 ^ 59
def prefixEnd_3265383 : Nat := 4983230072969 + 3 ^ 40 * 3265383 * 2
def baseEnd_3265383 : Nat := 558903666673500969231761

theorem tailTrace_3265383 : CollatzResearch.WordTrace tailWord_3265383 prefixEnd_3265383 558903666673500969231761 := by
  unfold tailWord_3265383
  simp only [CollatzResearch.WordTrace]
  refine ⟨119098302329082548862096803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79398868219388365908064535 119098302329082548862096803)
  ·
    refine ⟨178647453493623823293145205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119098302329082548862096803 178647453493623823293145205)
    ·
      refine ⟨16748198765027233433732363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178647453493623823293145205 16748198765027233433732363)
      ·
        refine ⟨25122298147540850150598545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16748198765027233433732363 25122298147540850150598545)
        ·
          refine ⟨18841723610655637612948909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25122298147540850150598545 18841723610655637612948909)
          ·
            refine ⟨7065646353995864104855841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18841723610655637612948909 7065646353995864104855841)
            ·
              refine ⟨5299234765496898078641881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7065646353995864104855841 5299234765496898078641881)
              ·
                refine ⟨3974426074122673558981411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299234765496898078641881 3974426074122673558981411)
                ·
                  refine ⟨5961639111184010338472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974426074122673558981411 5961639111184010338472117)
                  ·
                    refine ⟨558903666673500969231761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5961639111184010338472117 558903666673500969231761)
                    ·
                      rfl

theorem cell23_3265383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3265383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265383 prefixEnd_3265383 := by exact prefixLift 3265383
  have htrace : WordTrace (prefixWord ++ tailWord_3265383) baseStart_3265383 baseEnd_3265383 := by
    simpa [prefixWord, tailWord_3265383, baseEnd_3265383] using wordTrace_append hprefix tailTrace_3265383
  have hstable : (prefixWord ++ tailWord_3265383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265383).length < 2 ^ (prefixWord ++ tailWord_3265383).sum := by decide
  have hdescent : baseEnd_3265383 < baseStart_3265383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265397 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3265397 : Nat := 118140960795 + 3265397 * 2 ^ 59
def prefixEnd_3265397 : Nat := 4983230072969 + 3 ^ 40 * 3265397 * 2
def baseEnd_3265397 : Nat := 1676718188749665852920219

theorem tailTrace_3265397 : CollatzResearch.WordTrace tailWord_3265397 prefixEnd_3265397 1676718188749665852920219 := by
  unfold tailWord_3265397
  simp only [CollatzResearch.WordTrace]
  refine ⟨119098812951031829253106445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79399208634021219502070963 119098812951031829253106445)
  ·
    refine ⟨44662054856636935969914917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119098812951031829253106445 44662054856636935969914917)
    ·
      refine ⟨8374135285619425494359047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44662054856636935969914917 8374135285619425494359047)
      ·
        refine ⟨12561202928429138241538571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374135285619425494359047 12561202928429138241538571)
        ·
          refine ⟨18841804392643707362307857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12561202928429138241538571 18841804392643707362307857)
          ·
            refine ⟨14131353294482780521730893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18841804392643707362307857 14131353294482780521730893)
            ·
              refine ⟨5299257485431042695649085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14131353294482780521730893 5299257485431042695649085)
              ·
                refine ⟨1987221557036641010868407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5299257485431042695649085 1987221557036641010868407)
                ·
                  refine ⟨2980832335554961516302611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987221557036641010868407 2980832335554961516302611)
                  ·
                    refine ⟨4471248503332442274453917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2980832335554961516302611 4471248503332442274453917)
                    ·
                      refine ⟨1676718188749665852920219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471248503332442274453917 1676718188749665852920219)
                      ·
                        rfl

theorem cell23_3265397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3265397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265397 prefixEnd_3265397 := by exact prefixLift 3265397
  have htrace : WordTrace (prefixWord ++ tailWord_3265397) baseStart_3265397 baseEnd_3265397 := by
    simpa [prefixWord, tailWord_3265397, baseEnd_3265397] using wordTrace_append hprefix tailTrace_3265397
  have hstable : (prefixWord ++ tailWord_3265397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265397).length < 2 ^ (prefixWord ++ tailWord_3265397).sum := by decide
  have hdescent : baseEnd_3265397 < baseStart_3265397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265403 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 5, 2, 2]
def baseStart_3265403 : Nat := 118140960795 + 3265403 * 2 ^ 59
def prefixEnd_3265403 : Nat := 4983230072969 + 3 ^ 40 * 3265403 * 2
def baseEnd_3265403 : Nat := 1676721269633592829445191

theorem tailTrace_3265403 : CollatzResearch.WordTrace tailWord_3265403 prefixEnd_3265403 1676721269633592829445191 := by
  unfold tailWord_3265403
  simp only [CollatzResearch.WordTrace]
  refine ⟨119099031789010092277824863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79399354526006728185216575 119099031789010092277824863)
  ·
    refine ⟨178648547683515138416737295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119099031789010092277824863 178648547683515138416737295)
    ·
      refine ⟨267972821525272707625105943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178648547683515138416737295 267972821525272707625105943)
      ·
        refine ⟨401959232287909061437658915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267972821525272707625105943 401959232287909061437658915)
        ·
          refine ⟨602938848431863592156488373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401959232287909061437658915 602938848431863592156488373)
          ·
            refine ⟨56525517040487211764670785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 602938848431863592156488373 56525517040487211764670785)
            ·
              refine ⟨42394137780365408823503089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56525517040487211764670785 42394137780365408823503089)
              ·
                refine ⟨31795603335274056617627317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42394137780365408823503089 31795603335274056617627317)
                ·
                  refine ⟨2980837812681942807902561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31795603335274056617627317 2980837812681942807902561)
                  ·
                    refine ⟨2235628359511457105926921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980837812681942807902561 2235628359511457105926921)
                    ·
                      refine ⟨1676721269633592829445191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235628359511457105926921 1676721269633592829445191)
                      ·
                        rfl

theorem cell23_3265403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2, 2].length) (baseStart_3265403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265403 prefixEnd_3265403 := by exact prefixLift 3265403
  have htrace : WordTrace (prefixWord ++ tailWord_3265403) baseStart_3265403 baseEnd_3265403 := by
    simpa [prefixWord, tailWord_3265403, baseEnd_3265403] using wordTrace_append hprefix tailTrace_3265403
  have hstable : (prefixWord ++ tailWord_3265403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265403).length < 2 ^ (prefixWord ++ tailWord_3265403).sum := by decide
  have hdescent : baseEnd_3265403 < baseStart_3265403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265416 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3265416 : Nat := 118140960795 + 3265416 * 2 ^ 59
def prefixEnd_3265416 : Nat := 4983230072969 + 3 ^ 40 * 3265416 * 2
def baseEnd_3265416 : Nat := 1676727944882101278582631

theorem tailTrace_3265416 : CollatzResearch.WordTrace tailWord_3265416 prefixEnd_3265416 1676727944882101278582631 := by
  unfold tailWord_3265416
  simp only [CollatzResearch.WordTrace]
  refine ⟨59549752968981497749024051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79399670625308663665365401 59549752968981497749024051)
  ·
    refine ⟨89324629453472246623536077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59549752968981497749024051 89324629453472246623536077)
    ·
      refine ⟨33496736045052092483826029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89324629453472246623536077 33496736045052092483826029)
      ·
        refine ⟨12561276016894534681434761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33496736045052092483826029 12561276016894534681434761)
        ·
          refine ⟨9420957012670901011076071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12561276016894534681434761 9420957012670901011076071)
          ·
            refine ⟨14131435519006351516614107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420957012670901011076071 14131435519006351516614107)
            ·
              refine ⟨21197153278509527274921161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131435519006351516614107 21197153278509527274921161)
              ·
                refine ⟨15897864958882145456190871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21197153278509527274921161 15897864958882145456190871)
                ·
                  refine ⟨23846797438323218184286307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15897864958882145456190871 23846797438323218184286307)
                  ·
                    refine ⟨35770196157484827276429461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23846797438323218184286307 35770196157484827276429461)
                    ·
                      refine ⟨1676727944882101278582631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35770196157484827276429461 1676727944882101278582631)
                      ·
                        rfl

theorem cell23_3265416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3265416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265416 prefixEnd_3265416 := by exact prefixLift 3265416
  have htrace : WordTrace (prefixWord ++ tailWord_3265416) baseStart_3265416 baseEnd_3265416 := by
    simpa [prefixWord, tailWord_3265416, baseEnd_3265416] using wordTrace_append hprefix tailTrace_3265416
  have hstable : (prefixWord ++ tailWord_3265416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265416).length < 2 ^ (prefixWord ++ tailWord_3265416).sum := by decide
  have hdescent : baseEnd_3265416 < baseStart_3265416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265420 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_3265420 : Nat := 118140960795 + 3265420 * 2 ^ 59
def prefixEnd_3265420 : Nat := 4983230072969 + 3 ^ 40 * 3265420 * 2
def baseEnd_3265420 : Nat := 1676729998804719262932613

theorem tailTrace_3265420 : CollatzResearch.WordTrace tailWord_3265420 prefixEnd_3265420 1676729998804719262932613 := by
  unfold tailWord_3265420
  simp only [CollatzResearch.WordTrace]
  refine ⟨59549825914974252090596857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79399767886632336120795809 59549825914974252090596857)
  ·
    refine ⟨44662369436230689067947643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59549825914974252090596857 44662369436230689067947643)
    ·
      refine ⟨66993554154346033601921465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44662369436230689067947643 66993554154346033601921465)
      ·
        refine ⟨50245165615759525201441099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66993554154346033601921465 50245165615759525201441099)
        ·
          refine ⟨75367748423639287802161649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50245165615759525201441099 75367748423639287802161649)
          ·
            refine ⟨56525811317729465851621237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75367748423639287802161649 56525811317729465851621237)
            ·
              refine ⟨5299294811037137423589491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56525811317729465851621237 5299294811037137423589491)
              ·
                refine ⟨7948942216555706135384237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299294811037137423589491 7948942216555706135384237)
                ·
                  refine ⟨2980853331208389800769089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7948942216555706135384237 2980853331208389800769089)
                  ·
                    refine ⟨2235639998406292350576817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980853331208389800769089 2235639998406292350576817)
                    ·
                      refine ⟨1676729998804719262932613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235639998406292350576817 1676729998804719262932613)
                      ·
                        rfl

theorem cell23_3265420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_3265420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265420 prefixEnd_3265420 := by exact prefixLift 3265420
  have htrace : WordTrace (prefixWord ++ tailWord_3265420) baseStart_3265420 baseEnd_3265420 := by
    simpa [prefixWord, tailWord_3265420, baseEnd_3265420] using wordTrace_append hprefix tailTrace_3265420
  have hstable : (prefixWord ++ tailWord_3265420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265420).length < 2 ^ (prefixWord ++ tailWord_3265420).sum := by decide
  have hdescent : baseEnd_3265420 < baseStart_3265420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265457 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_3265457 : Nat := 118140960795 + 3265457 * 2 ^ 59
def prefixEnd_3265457 : Nat := 4983230072969 + 3 ^ 40 * 3265457 * 2
def baseEnd_3265457 : Nat := 1676748997588935618169943

theorem tailTrace_3265457 : CollatzResearch.WordTrace tailWord_3265457 prefixEnd_3265457 1676748997588935618169943 := by
  unfold tailWord_3265457
  simp only [CollatzResearch.WordTrace]
  refine ⟨119101001330814459500290625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79400667553876306333527083 119101001330814459500290625)
  ·
    refine ⟨89325750998110844625217969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119101001330814459500290625 89325750998110844625217969)
    ·
      refine ⟨66994313248583133468913477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89325750998110844625217969 66994313248583133468913477)
      ·
        refine ⟨12561433734109337525421277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66994313248583133468913477 12561433734109337525421277)
        ·
          refine ⟨4710537650291001572032979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12561433734109337525421277 4710537650291001572032979)
          ·
            refine ⟨7065806475436502358049469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710537650291001572032979 7065806475436502358049469)
            ·
              refine ⟨2649677428288688384268551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065806475436502358049469 2649677428288688384268551)
              ·
                refine ⟨3974516142433032576402827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649677428288688384268551 3974516142433032576402827)
                ·
                  refine ⟨5961774213649548864604241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974516142433032576402827 5961774213649548864604241)
                  ·
                    refine ⟨4471330660237161648453181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961774213649548864604241 4471330660237161648453181)
                    ·
                      refine ⟨1676748997588935618169943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471330660237161648453181 1676748997588935618169943)
                      ·
                        rfl

theorem cell23_3265457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_3265457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265457 prefixEnd_3265457 := by exact prefixLift 3265457
  have htrace : WordTrace (prefixWord ++ tailWord_3265457) baseStart_3265457 baseEnd_3265457 := by
    simpa [prefixWord, tailWord_3265457, baseEnd_3265457] using wordTrace_append hprefix tailTrace_3265457
  have hstable : (prefixWord ++ tailWord_3265457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265457).length < 2 ^ (prefixWord ++ tailWord_3265457).sum := by decide
  have hdescent : baseEnd_3265457 < baseStart_3265457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265486 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3265486 : Nat := 118140960795 + 3265486 * 2 ^ 59
def prefixEnd_3265486 : Nat := 4983230072969 + 3 ^ 40 * 3265486 * 2
def baseEnd_3265486 : Nat := 558921296175972001569103

theorem tailTrace_3265486 : CollatzResearch.WordTrace tailWord_3265486 prefixEnd_3265486 558921296175972001569103 := by
  unfold tailWord_3265486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14887757380963674681637039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79401372698472931635397541 14887757380963674681637039)
  ·
    refine ⟨22331636071445512022455559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14887757380963674681637039 22331636071445512022455559)
    ·
      refine ⟨33497454107168268033683339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22331636071445512022455559 33497454107168268033683339)
      ·
        refine ⟨50246181160752402050525009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33497454107168268033683339 50246181160752402050525009)
        ·
          refine ⟨37684635870564301537893757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50246181160752402050525009 37684635870564301537893757)
          ·
            refine ⟨14131738451461613076710159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37684635870564301537893757 14131738451461613076710159)
            ·
              refine ⟨21197607677192419615065239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131738451461613076710159 21197607677192419615065239)
              ·
                refine ⟨31796411515788629422597859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21197607677192419615065239 31796411515788629422597859)
                ·
                  refine ⟨47694617273682944133896789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31796411515788629422597859 47694617273682944133896789)
                  ·
                    refine ⟨558921296175972001569103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47694617273682944133896789 558921296175972001569103)
                    ·
                      rfl

theorem cell23_3265486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3265486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265486 prefixEnd_3265486 := by exact prefixLift 3265486
  have htrace : WordTrace (prefixWord ++ tailWord_3265486) baseStart_3265486 baseEnd_3265486 := by
    simpa [prefixWord, tailWord_3265486, baseEnd_3265486] using wordTrace_append hprefix tailTrace_3265486
  have hstable : (prefixWord ++ tailWord_3265486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265486).length < 2 ^ (prefixWord ++ tailWord_3265486).sum := by decide
  have hdescent : baseEnd_3265486 < baseStart_3265486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265514 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_3265514 : Nat := 118140960795 + 3265514 * 2 ^ 59
def prefixEnd_3265514 : Nat := 4983230072969 + 3 ^ 40 * 3265514 * 2
def baseEnd_3265514 : Nat := 1676778265986241895157181

theorem tailTrace_3265514 : CollatzResearch.WordTrace tailWord_3265514 prefixEnd_3265514 1676778265986241895157181 := by
  unfold tailWord_3265514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775770072901989558778899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79402053527738638823410397 29775770072901989558778899)
  ·
    refine ⟨44663655109352984338168349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775770072901989558778899 44663655109352984338168349)
    ·
      refine ⟨16748870666007369126813131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44663655109352984338168349 16748870666007369126813131)
      ·
        refine ⟨25123305999011053690219697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16748870666007369126813131 25123305999011053690219697)
        ·
          refine ⟨18842479499258290267664773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25123305999011053690219697 18842479499258290267664773)
          ·
            refine ⟨3532964906110929425187145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18842479499258290267664773 3532964906110929425187145)
            ·
              refine ⟨2649723679583197068890359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532964906110929425187145 2649723679583197068890359)
              ·
                refine ⟨3974585519374795603335539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649723679583197068890359 3974585519374795603335539)
                ·
                  refine ⟨5961878279062193405003309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974585519374795603335539 5961878279062193405003309)
                  ·
                    refine ⟨2235704354648322526876241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5961878279062193405003309 2235704354648322526876241)
                    ·
                      refine ⟨1676778265986241895157181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235704354648322526876241 1676778265986241895157181)
                      ·
                        rfl

theorem cell23_3265514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_3265514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265514 prefixEnd_3265514 := by exact prefixLift 3265514
  have htrace : WordTrace (prefixWord ++ tailWord_3265514) baseStart_3265514 baseEnd_3265514 := by
    simpa [prefixWord, tailWord_3265514, baseEnd_3265514] using wordTrace_append hprefix tailTrace_3265514
  have hstable : (prefixWord ++ tailWord_3265514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265514).length < 2 ^ (prefixWord ++ tailWord_3265514).sum := by decide
  have hdescent : baseEnd_3265514 < baseStart_3265514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265543 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3265543 : Nat := 118140960795 + 3265543 * 2 ^ 59
def prefixEnd_3265543 : Nat := 4983230072969 + 3 ^ 40 * 3265543 * 2
def baseEnd_3265543 : Nat := 1676793156925222281694547

theorem tailTrace_3265543 : CollatzResearch.WordTrace tailWord_3265543 prefixEnd_3265543 1676793156925222281694547 := by
  unfold tailWord_3265543
  simp only [CollatzResearch.WordTrace]
  refine ⟨119104138008502896187921283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79402758672335264125280855 119104138008502896187921283)
  ·
    refine ⟨178656207012754344281881925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119104138008502896187921283 178656207012754344281881925)
    ·
      refine ⟨33498038814891439552852861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178656207012754344281881925 33498038814891439552852861)
      ·
        refine ⟨12561764555584289832319823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33498038814891439552852861 12561764555584289832319823)
        ·
          refine ⟨18842646833376434748479735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12561764555584289832319823 18842646833376434748479735)
          ·
            refine ⟨28263970250064652122719603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18842646833376434748479735 28263970250064652122719603)
            ·
              refine ⟨42395955375096978184079405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28263970250064652122719603 42395955375096978184079405)
              ·
                refine ⟨15898483265661366819029777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42395955375096978184079405 15898483265661366819029777)
                ·
                  refine ⟨11923862449246025114272333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15898483265661366819029777 11923862449246025114272333)
                  ·
                    refine ⟨4471448418467259417852125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11923862449246025114272333 4471448418467259417852125)
                    ·
                      refine ⟨1676793156925222281694547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471448418467259417852125 1676793156925222281694547)
                      ·
                        rfl

theorem cell23_3265543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3265543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265543 prefixEnd_3265543 := by exact prefixLift 3265543
  have htrace : WordTrace (prefixWord ++ tailWord_3265543) baseStart_3265543 baseEnd_3265543 := by
    simpa [prefixWord, tailWord_3265543, baseEnd_3265543] using wordTrace_append hprefix tailTrace_3265543
  have hstable : (prefixWord ++ tailWord_3265543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265543).length < 2 ^ (prefixWord ++ tailWord_3265543).sum := by decide
  have hdescent : baseEnd_3265543 < baseStart_3265543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265544 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_3265544 : Nat := 118140960795 + 3265544 * 2 ^ 59
def prefixEnd_3265544 : Nat := 4983230072969 + 3 ^ 40 * 3265544 * 2
def baseEnd_3265544 : Nat := 1676793670405876777782043

theorem tailTrace_3265544 : CollatzResearch.WordTrace tailWord_3265544 prefixEnd_3265544 1676793670405876777782043 := by
  unfold tailWord_3265544
  simp only [CollatzResearch.WordTrace]
  refine ⟨59552087240749636679353843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79402782987666182239138457 59552087240749636679353843)
  ·
    refine ⟨89328130861124455019030765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59552087240749636679353843 89328130861124455019030765)
    ·
      refine ⟨33498049072921670632136537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89328130861124455019030765 33498049072921670632136537)
      ·
        refine ⟨25123536804691252974102403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33498049072921670632136537 25123536804691252974102403)
        ·
          refine ⟨37685305207036879461153605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25123536804691252974102403 37685305207036879461153605)
          ·
            refine ⟨7065994726319414898966301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37685305207036879461153605 7065994726319414898966301)
            ·
              refine ⟨2649748022369780587112363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065994726319414898966301 2649748022369780587112363)
              ·
                refine ⟨3974622033554670880668545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649748022369780587112363 3974622033554670880668545)
                ·
                  refine ⟨2980966525166003160501409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3974622033554670880668545 2980966525166003160501409)
                  ·
                    refine ⟨2235724893874502370376057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2980966525166003160501409 2235724893874502370376057)
                    ·
                      refine ⟨1676793670405876777782043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235724893874502370376057 1676793670405876777782043)
                      ·
                        rfl

theorem cell23_3265544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_3265544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265544 prefixEnd_3265544 := by exact prefixLift 3265544
  have htrace : WordTrace (prefixWord ++ tailWord_3265544) baseStart_3265544 baseEnd_3265544 := by
    simpa [prefixWord, tailWord_3265544, baseEnd_3265544] using wordTrace_append hprefix tailTrace_3265544
  have hstable : (prefixWord ++ tailWord_3265544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265544).length < 2 ^ (prefixWord ++ tailWord_3265544).sum := by decide
  have hdescent : baseEnd_3265544 < baseStart_3265544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265553 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_3265553 : Nat := 118140960795 + 3265553 * 2 ^ 59
def prefixEnd_3265553 : Nat := 4983230072969 + 3 ^ 40 * 3265553 * 2
def baseEnd_3265553 : Nat := 1676798291731767242569501

theorem tailTrace_3265553 : CollatzResearch.WordTrace tailWord_3265553 prefixEnd_3265553 1676798291731767242569501 := by
  unfold tailWord_3265553
  simp only [CollatzResearch.WordTrace]
  refine ⟨119104502738466667895785313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79403001825644445263856875 119104502738466667895785313)
  ·
    refine ⟨89328377053850000921838985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119104502738466667895785313 89328377053850000921838985)
    ·
      refine ⟨66996282790387500691379239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89328377053850000921838985 66996282790387500691379239)
      ·
        refine ⟨100494424185581251037068859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66996282790387500691379239 100494424185581251037068859)
        ·
          refine ⟨150741636278371876555603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100494424185581251037068859 150741636278371876555603289)
          ·
            refine ⟨113056227208778907416702467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150741636278371876555603289 113056227208778907416702467)
            ·
              refine ⟨169584340813168361125053701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113056227208778907416702467 169584340813168361125053701)
              ·
                refine ⟨31797063902469067710947569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169584340813168361125053701 31797063902469067710947569)
                ·
                  refine ⟨23847797926851800783210677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31797063902469067710947569 23847797926851800783210677)
                  ·
                    refine ⟨2235731055642356323426001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23847797926851800783210677 2235731055642356323426001)
                    ·
                      refine ⟨1676798291731767242569501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235731055642356323426001 1676798291731767242569501)
                      ·
                        rfl

theorem cell23_3265553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_3265553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265553 prefixEnd_3265553 := by exact prefixLift 3265553
  have htrace : WordTrace (prefixWord ++ tailWord_3265553) baseStart_3265553 baseEnd_3265553 := by
    simpa [prefixWord, tailWord_3265553, baseEnd_3265553] using wordTrace_append hprefix tailTrace_3265553
  have hstable : (prefixWord ++ tailWord_3265553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265553).length < 2 ^ (prefixWord ++ tailWord_3265553).sum := by decide
  have hdescent : baseEnd_3265553 < baseStart_3265553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265590 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3265590 : Nat := 118140960795 + 3265590 * 2 ^ 59
def prefixEnd_3265590 : Nat := 4983230072969 + 3 ^ 40 * 3265590 * 2
def baseEnd_3265590 : Nat := 1676817290515983597806831

theorem tailTrace_3265590 : CollatzResearch.WordTrace tailWord_3265590 prefixEnd_3265590 1676817290515983597806831 := by
  unfold tailWord_3265590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444115764958288950930139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79403901492888415476588149 7444115764958288950930139)
  ·
    refine ⟨11166173647437433426395209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7444115764958288950930139 11166173647437433426395209)
    ·
      refine ⟨8374630235578075069796407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11166173647437433426395209 8374630235578075069796407)
      ·
        refine ⟨12561945353367112604694611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374630235578075069796407 12561945353367112604694611)
        ·
          refine ⟨18842918030050668907041917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12561945353367112604694611 18842918030050668907041917)
          ·
            refine ⟨7066094261269000840140719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18842918030050668907041917 7066094261269000840140719)
            ·
              refine ⟨10599141391903501260211079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066094261269000840140719 10599141391903501260211079)
              ·
                refine ⟨15898712087855251890316619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10599141391903501260211079 15898712087855251890316619)
                ·
                  refine ⟨23848068131782877835474929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15898712087855251890316619 23848068131782877835474929)
                  ·
                    refine ⟨17886051098837158376606197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23848068131782877835474929 17886051098837158376606197)
                    ·
                      refine ⟨1676817290515983597806831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17886051098837158376606197 1676817290515983597806831)
                      ·
                        rfl

theorem cell23_3265590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3265590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265590 prefixEnd_3265590 := by exact prefixLift 3265590
  have htrace : WordTrace (prefixWord ++ tailWord_3265590) baseStart_3265590 baseEnd_3265590 := by
    simpa [prefixWord, tailWord_3265590, baseEnd_3265590] using wordTrace_append hprefix tailTrace_3265590
  have hstable : (prefixWord ++ tailWord_3265590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265590).length < 2 ^ (prefixWord ++ tailWord_3265590).sum := by decide
  have hdescent : baseEnd_3265590 < baseStart_3265590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265603 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3]
def baseStart_3265603 : Nat := 118140960795 + 3265603 * 2 ^ 59
def prefixEnd_3265603 : Nat := 4983230072969 + 3 ^ 40 * 3265603 * 2
def baseEnd_3265603 : Nat := 1676823965764492046944271

theorem tailTrace_3265603 : CollatzResearch.WordTrace tailWord_3265603 prefixEnd_3265603 1676823965764492046944271 := by
  unfold tailWord_3265603
  simp only [CollatzResearch.WordTrace]
  refine ⟨119106326388285526435105463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79404217592190350956736975 119106326388285526435105463)
  ·
    refine ⟨178659489582428289652658195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119106326388285526435105463 178659489582428289652658195)
    ·
      refine ⟨267989234373642434478987293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178659489582428289652658195 267989234373642434478987293)
      ·
        refine ⟨100495962890115912929620235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267989234373642434478987293 100495962890115912929620235)
        ·
          refine ⟨150743944335173869394430353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100495962890115912929620235 150743944335173869394430353)
          ·
            refine ⟨113057958251380402045822765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150743944335173869394430353 113057958251380402045822765)
            ·
              refine ⟨42396734344267650767183537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113057958251380402045822765 42396734344267650767183537)
              ·
                refine ⟨31797550758200738075387653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42396734344267650767183537 31797550758200738075387653)
                ·
                  refine ⟨5962040767162638389135185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31797550758200738075387653 5962040767162638389135185)
                  ·
                    refine ⟨4471530575371978791851389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5962040767162638389135185 4471530575371978791851389)
                    ·
                      refine ⟨1676823965764492046944271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471530575371978791851389 1676823965764492046944271)
                      ·
                        rfl

theorem cell23_3265603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_3265603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265603 prefixEnd_3265603 := by exact prefixLift 3265603
  have htrace : WordTrace (prefixWord ++ tailWord_3265603) baseStart_3265603 baseEnd_3265603 := by
    simpa [prefixWord, tailWord_3265603, baseEnd_3265603] using wordTrace_append hprefix tailTrace_3265603
  have hstable : (prefixWord ++ tailWord_3265603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265603).length < 2 ^ (prefixWord ++ tailWord_3265603).sum := by decide
  have hdescent : baseEnd_3265603 < baseStart_3265603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265620 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_3265620 : Nat := 118140960795 + 3265620 * 2 ^ 59
def prefixEnd_3265620 : Nat := 4983230072969 + 3 ^ 40 * 3265620 * 2
def baseEnd_3265620 : Nat := 1676832694935618480431693

theorem tailTrace_3265620 : CollatzResearch.WordTrace tailWord_3265620 prefixEnd_3265620 1676832694935618480431693 := by
  unfold tailWord_3265620
  simp only [CollatzResearch.WordTrace]
  refine ⟨59553473214611969169237157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79404630952815958892316209 59553473214611969169237157)
  ·
    refine ⟨11166276227739744219231967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59553473214611969169237157 11166276227739744219231967)
    ·
      refine ⟨16749414341609616328847951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11166276227739744219231967 16749414341609616328847951)
      ·
        refine ⟨25124121512414424493271927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16749414341609616328847951 25124121512414424493271927)
        ·
          refine ⟨37686182268621636739907891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25124121512414424493271927 37686182268621636739907891)
          ·
            refine ⟨56529273402932455109861837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37686182268621636739907891 56529273402932455109861837)
            ·
              refine ⟨21198477526099670666198189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56529273402932455109861837 21198477526099670666198189)
              ·
                refine ⟨7949429072287376499824321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21198477526099670666198189 7949429072287376499824321)
                ·
                  refine ⟨5962071804215532374868241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949429072287376499824321 5962071804215532374868241)
                  ·
                    refine ⟨4471553853161649281151181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5962071804215532374868241 4471553853161649281151181)
                    ·
                      refine ⟨1676832694935618480431693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471553853161649281151181 1676832694935618480431693)
                      ·
                        rfl

theorem cell23_3265620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_3265620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265620 prefixEnd_3265620 := by exact prefixLift 3265620
  have htrace : WordTrace (prefixWord ++ tailWord_3265620) baseStart_3265620 baseEnd_3265620 := by
    simpa [prefixWord, tailWord_3265620, baseEnd_3265620] using wordTrace_append hprefix tailTrace_3265620
  have hstable : (prefixWord ++ tailWord_3265620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265620).length < 2 ^ (prefixWord ++ tailWord_3265620).sum := by decide
  have hdescent : baseEnd_3265620 < baseStart_3265620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265660 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_3265660 : Nat := 118140960795 + 3265660 * 2 ^ 59
def prefixEnd_3265660 : Nat := 4983230072969 + 3 ^ 40 * 3265660 * 2
def baseEnd_3265660 : Nat := 1676853234161798323931509

theorem tailTrace_3265660 : CollatzResearch.WordTrace tailWord_3265660 prefixEnd_3265660 1676853234161798323931509 := by
  unfold tailWord_3265660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59554202674539512584965217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79405603566052683446620289 59554202674539512584965217)
  ·
    refine ⟨44665652005904634438723913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59554202674539512584965217 44665652005904634438723913)
    ·
      refine ⟨33499239004428475829042935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44665652005904634438723913 33499239004428475829042935)
      ·
        refine ⟨50248858506642713743564403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33499239004428475829042935 50248858506642713743564403)
        ·
          refine ⟨75373287759964070615346605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50248858506642713743564403 75373287759964070615346605)
          ·
            refine ⟨28264982909986526480754977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75373287759964070615346605 28264982909986526480754977)
            ·
              refine ⟨21198737182489894860566233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28264982909986526480754977 21198737182489894860566233)
              ·
                refine ⟨15899052886867421145424675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21198737182489894860566233 15899052886867421145424675)
                ·
                  refine ⟨23848579330301131718137013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15899052886867421145424675 23848579330301131718137013)
                  ·
                    refine ⟨2235804312215731098575345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23848579330301131718137013 2235804312215731098575345)
                    ·
                      refine ⟨1676853234161798323931509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235804312215731098575345 1676853234161798323931509)
                      ·
                        rfl

theorem cell23_3265660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_3265660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265660 prefixEnd_3265660 := by exact prefixLift 3265660
  have htrace : WordTrace (prefixWord ++ tailWord_3265660) baseStart_3265660 baseEnd_3265660 := by
    simpa [prefixWord, tailWord_3265660, baseEnd_3265660] using wordTrace_append hprefix tailTrace_3265660
  have hstable : (prefixWord ++ tailWord_3265660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265660).length < 2 ^ (prefixWord ++ tailWord_3265660).sum := by decide
  have hdescent : baseEnd_3265660 < baseStart_3265660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265683 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 1, 6]
def baseStart_3265683 : Nat := 118140960795 + 3265683 * 2 ^ 59
def prefixEnd_3265683 : Nat := 4983230072969 + 3 ^ 40 * 3265683 * 2
def baseEnd_3265683 : Nat := 558955014738950577981301

theorem tailTrace_3265683 : CollatzResearch.WordTrace tailWord_3265683 prefixEnd_3265683 558955014738950577981301 := by
  unfold tailWord_3265683
  simp only [CollatzResearch.WordTrace]
  refine ⟨119109244227995700098017703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79406162818663800065345135 119109244227995700098017703)
  ·
    refine ⟨178663866341993550147026555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119109244227995700098017703 178663866341993550147026555)
    ·
      refine ⟨267995799512990325220539833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178663866341993550147026555 267995799512990325220539833)
      ·
        refine ⟨200996849634742743915404875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267995799512990325220539833 200996849634742743915404875)
        ·
          refine ⟨301495274452114115873107313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200996849634742743915404875 301495274452114115873107313)
          ·
            refine ⟨226121455839085586904830485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301495274452114115873107313 226121455839085586904830485)
            ·
              refine ⟨10599443242457136886163929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226121455839085586904830485 10599443242457136886163929)
              ·
                refine ⟨7949582431842852664622947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599443242457136886163929 7949582431842852664622947)
                ·
                  refine ⟨11924373647764278996934421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949582431842852664622947 11924373647764278996934421)
                  ·
                    refine ⟨558955014738950577981301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11924373647764278996934421 558955014738950577981301)
                    ·
                      rfl

theorem cell23_3265683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 6].length) (baseStart_3265683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265683 prefixEnd_3265683 := by exact prefixLift 3265683
  have htrace : WordTrace (prefixWord ++ tailWord_3265683) baseStart_3265683 baseEnd_3265683 := by
    simpa [prefixWord, tailWord_3265683, baseEnd_3265683] using wordTrace_append hprefix tailTrace_3265683
  have hstable : (prefixWord ++ tailWord_3265683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265683).length < 2 ^ (prefixWord ++ tailWord_3265683).sum := by decide
  have hdescent : baseEnd_3265683 < baseStart_3265683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265687 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 1, 5]
def baseStart_3265687 : Nat := 118140960795 + 3265687 * 2 ^ 59
def prefixEnd_3265687 : Nat := 4983230072969 + 3 ^ 40 * 3265687 * 2
def baseEnd_3265687 : Nat := 558955699379823239431295

theorem tailTrace_3265687 : CollatzResearch.WordTrace tailWord_3265687 prefixEnd_3265687 558955699379823239431295 := by
  unfold tailWord_3265687
  simp only [CollatzResearch.WordTrace]
  refine ⟨119109390119981208781163315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79406260079987472520775543 119109390119981208781163315)
  ·
    refine ⟨178664085179971813171744973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119109390119981208781163315 178664085179971813171744973)
    ·
      refine ⟨66999031942489429939404365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178664085179971813171744973 66999031942489429939404365)
      ·
        refine ⟨25124636978433536227276637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66999031942489429939404365 25124636978433536227276637)
        ·
          refine ⟨9421738866912576085228739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25124636978433536227276637 9421738866912576085228739)
          ·
            refine ⟨14132608300368864127843109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421738866912576085228739 14132608300368864127843109)
            ·
              refine ⟨2649864056319162023970583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14132608300368864127843109 2649864056319162023970583)
              ·
                refine ⟨3974796084478743035955875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649864056319162023970583 3974796084478743035955875)
                ·
                  refine ⟨5962194126718114553933813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974796084478743035955875 5962194126718114553933813)
                  ·
                    refine ⟨558955699379823239431295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5962194126718114553933813 558955699379823239431295)
                    ·
                      rfl

theorem cell23_3265687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_3265687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265687 prefixEnd_3265687 := by exact prefixLift 3265687
  have htrace : WordTrace (prefixWord ++ tailWord_3265687) baseStart_3265687 baseEnd_3265687 := by
    simpa [prefixWord, tailWord_3265687, baseEnd_3265687] using wordTrace_append hprefix tailTrace_3265687
  have hstable : (prefixWord ++ tailWord_3265687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265687).length < 2 ^ (prefixWord ++ tailWord_3265687).sum := by decide
  have hdescent : baseEnd_3265687 < baseStart_3265687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265724 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_3265724 : Nat := 118140960795 + 3265724 * 2 ^ 59
def prefixEnd_3265724 : Nat := 4983230072969 + 3 ^ 40 * 3265724 * 2
def baseEnd_3265724 : Nat := 1676886096923686073531215

theorem tailTrace_3265724 : CollatzResearch.WordTrace tailWord_3265724 prefixEnd_3265724 1676886096923686073531215 := by
  unfold tailWord_3265724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59555369810423582050130113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79407159747231442733506817 59555369810423582050130113)
  ·
    refine ⟨44666527357817686537597585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59555369810423582050130113 44666527357817686537597585)
    ·
      refine ⟨33499895518363264903198189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44666527357817686537597585 33499895518363264903198189)
      ·
        refine ⟨12562460819386224338699321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33499895518363264903198189 12562460819386224338699321)
        ·
          refine ⟨9421845614539668254024491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12562460819386224338699321 9421845614539668254024491)
          ·
            refine ⟨14132768421809502381036737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421845614539668254024491 14132768421809502381036737)
            ·
              refine ⟨10599576316357126785777553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14132768421809502381036737 10599576316357126785777553)
              ·
                refine ⟨7949682237267845089333165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599576316357126785777553 7949682237267845089333165)
                ·
                  refine ⟨2981130838975441908499937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7949682237267845089333165 2981130838975441908499937)
                  ·
                    refine ⟨2235848129231581431374953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2981130838975441908499937 2235848129231581431374953)
                    ·
                      refine ⟨1676886096923686073531215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235848129231581431374953 1676886096923686073531215)
                      ·
                        rfl

theorem cell23_3265724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_3265724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265724 prefixEnd_3265724 := by exact prefixLift 3265724
  have htrace : WordTrace (prefixWord ++ tailWord_3265724) baseStart_3265724 baseEnd_3265724 := by
    simpa [prefixWord, tailWord_3265724, baseEnd_3265724] using wordTrace_append hprefix tailTrace_3265724
  have hstable : (prefixWord ++ tailWord_3265724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265724).length < 2 ^ (prefixWord ++ tailWord_3265724).sum := by decide
  have hdescent : baseEnd_3265724 < baseStart_3265724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265753 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3265753 : Nat := 118140960795 + 3265753 * 2 ^ 59
def prefixEnd_3265753 : Nat := 4983230072969 + 3 ^ 40 * 3265753 * 2
def baseEnd_3265753 : Nat := 1676900987862666460068581

theorem tailTrace_3265753 : CollatzResearch.WordTrace tailWord_3265753 prefixEnd_3265753 1676900987862666460068581 := by
  unfold tailWord_3265753
  simp only [CollatzResearch.WordTrace]
  refine ⟨119111797337742102053065913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79407864891828068035377275 119111797337742102053065913)
  ·
    refine ⟨89333848003306576539799435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119111797337742102053065913 89333848003306576539799435)
    ·
      refine ⟨134000772004959864809699153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89333848003306576539799435 134000772004959864809699153)
      ·
        refine ⟨100500579003719898607274365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134000772004959864809699153 100500579003719898607274365)
        ·
          refine ⟨37687717126394961977727887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100500579003719898607274365 37687717126394961977727887)
          ·
            refine ⟨56531575689592442966591831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37687717126394961977727887 56531575689592442966591831)
            ·
              refine ⟨84797363534388664449887747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56531575689592442966591831 84797363534388664449887747)
              ·
                refine ⟨127196045301582996674831621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84797363534388664449887747 127196045301582996674831621)
                ·
                  refine ⟨23849258494046811876530929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127196045301582996674831621 23849258494046811876530929)
                  ·
                    refine ⟨17886943870535108907398197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23849258494046811876530929 17886943870535108907398197)
                    ·
                      refine ⟨1676900987862666460068581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17886943870535108907398197 1676900987862666460068581)
                      ·
                        rfl

theorem cell23_3265753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3265753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265753 prefixEnd_3265753 := by exact prefixLift 3265753
  have htrace : WordTrace (prefixWord ++ tailWord_3265753) baseStart_3265753 baseEnd_3265753 := by
    simpa [prefixWord, tailWord_3265753, baseEnd_3265753] using wordTrace_append hprefix tailTrace_3265753
  have hstable : (prefixWord ++ tailWord_3265753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265753).length < 2 ^ (prefixWord ++ tailWord_3265753).sum := by decide
  have hdescent : baseEnd_3265753 < baseStart_3265753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265783 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3265783 : Nat := 118140960795 + 3265783 * 2 ^ 59
def prefixEnd_3265783 : Nat := 4983230072969 + 3 ^ 40 * 3265783 * 2
def baseEnd_3265783 : Nat := 1676916392282301342693443

theorem tailTrace_3265783 : CollatzResearch.WordTrace tailWord_3265783 prefixEnd_3265783 1676916392282301342693443 := by
  unfold tailWord_3265783
  simp only [CollatzResearch.WordTrace]
  refine ⟨119112891527633417176658003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79408594351755611451105335 119112891527633417176658003)
  ·
    refine ⟨178669337291450125764987005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119112891527633417176658003 178669337291450125764987005)
    ·
      refine ⟨67001001484293797161870127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178669337291450125764987005 67001001484293797161870127)
      ·
        refine ⟨100501502226440695742805191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67001001484293797161870127 100501502226440695742805191)
        ·
          refine ⟨150752253339661043614207787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100501502226440695742805191 150752253339661043614207787)
          ·
            refine ⟨226128380009491565421311681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150752253339661043614207787 226128380009491565421311681)
            ·
              refine ⟨169596285007118674065983761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226128380009491565421311681 169596285007118674065983761)
              ·
                refine ⟨127197213755339005549487821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169596285007118674065983761 127197213755339005549487821)
                ·
                  refine ⟨47698955158252127081057933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127197213755339005549487821 47698955158252127081057933)
                  ·
                    refine ⟨17887108184344547655396725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47698955158252127081057933 17887108184344547655396725)
                    ·
                      refine ⟨1676916392282301342693443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17887108184344547655396725 1676916392282301342693443)
                      ·
                        rfl

theorem cell23_3265783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3265783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265783 prefixEnd_3265783 := by exact prefixLift 3265783
  have htrace : WordTrace (prefixWord ++ tailWord_3265783) baseStart_3265783 baseEnd_3265783 := by
    simpa [prefixWord, tailWord_3265783, baseEnd_3265783] using wordTrace_append hprefix tailTrace_3265783
  have hstable : (prefixWord ++ tailWord_3265783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265783).length < 2 ^ (prefixWord ++ tailWord_3265783).sum := by decide
  have hdescent : baseEnd_3265783 < baseStart_3265783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265797 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_3265797 : Nat := 118140960795 + 3265797 * 2 ^ 59
def prefixEnd_3265797 : Nat := 4983230072969 + 3 ^ 40 * 3265797 * 2
def baseEnd_3265797 : Nat := 1676923581011464287918379

theorem tailTrace_3265797 : CollatzResearch.WordTrace tailWord_3265797 prefixEnd_3265797 1676923581011464287918379 := by
  unfold tailWord_3265797
  simp only [CollatzResearch.WordTrace]
  refine ⟨119113402149582697567667645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79408934766388465045111763 119113402149582697567667645)
  ·
    refine ⟨44667525806093511587875367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119113402149582697567667645 44667525806093511587875367)
    ·
      refine ⟨67001288709140267381813051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44667525806093511587875367 67001288709140267381813051)
      ·
        refine ⟨100501933063710401072719577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67001288709140267381813051 100501933063710401072719577)
        ·
          refine ⟨75376449797782800804539683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100501933063710401072719577 75376449797782800804539683)
          ·
            refine ⟨113064674696674201206809525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75376449797782800804539683 113064674696674201206809525)
            ·
              refine ⟨10599813252813206363138393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113064674696674201206809525 10599813252813206363138393)
              ·
                refine ⟨7949859939609904772353795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599813252813206363138393 7949859939609904772353795)
                ·
                  refine ⟨11924789909414857158530693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949859939609904772353795 11924789909414857158530693)
                  ·
                    refine ⟨2235898108015285717224505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11924789909414857158530693 2235898108015285717224505)
                    ·
                      refine ⟨1676923581011464287918379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2235898108015285717224505 1676923581011464287918379)
                      ·
                        rfl

theorem cell23_3265797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_3265797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265797 prefixEnd_3265797 := by exact prefixLift 3265797
  have htrace : WordTrace (prefixWord ++ tailWord_3265797) baseStart_3265797 baseEnd_3265797 := by
    simpa [prefixWord, tailWord_3265797, baseEnd_3265797] using wordTrace_append hprefix tailTrace_3265797
  have hstable : (prefixWord ++ tailWord_3265797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265797).length < 2 ^ (prefixWord ++ tailWord_3265797).sum := by decide
  have hdescent : baseEnd_3265797 < baseStart_3265797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_3265833 : Nat := 118140960795 + 3265833 * 2 ^ 59
def prefixEnd_3265833 : Nat := 4983230072969 + 3 ^ 40 * 3265833 * 2
def baseEnd_3265833 : Nat := 558980688771675382356071

theorem tailTrace_3265833 : CollatzResearch.WordTrace tailWord_3265833 prefixEnd_3265833 558980688771675382356071 := by
  unfold tailWord_3265833
  simp only [CollatzResearch.WordTrace]
  refine ⟨119114715177452275715978153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79409810118301517143985435 119114715177452275715978153)
  ·
    refine ⟨89336036383089206786983615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119114715177452275715978153 89336036383089206786983615)
    ·
      refine ⟨134004054574633810180475423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89336036383089206786983615 134004054574633810180475423)
      ·
        refine ⟨201006081861950715270713135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134004054574633810180475423 201006081861950715270713135)
        ·
          refine ⟨301509122792926072906069703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201006081861950715270713135 301509122792926072906069703)
          ·
            refine ⟨452263684189389109359104555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301509122792926072906069703 452263684189389109359104555)
            ·
              refine ⟨678395526284083664038656833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452263684189389109359104555 678395526284083664038656833)
              ·
                refine ⟨508796644713062748028992625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678395526284083664038656833 508796644713062748028992625)
                ·
                  refine ⟨381597483534797061021744469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508796644713062748028992625 381597483534797061021744469)
                  ·
                    refine ⟨558980688771675382356071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 381597483534797061021744469 558980688771675382356071)
                    ·
                      rfl

theorem cell23_3265833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_3265833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265833 prefixEnd_3265833 := by exact prefixLift 3265833
  have htrace : WordTrace (prefixWord ++ tailWord_3265833) baseStart_3265833 baseEnd_3265833 := by
    simpa [prefixWord, tailWord_3265833, baseEnd_3265833] using wordTrace_append hprefix tailTrace_3265833
  have hstable : (prefixWord ++ tailWord_3265833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265833).length < 2 ^ (prefixWord ++ tailWord_3265833).sum := by decide
  have hdescent : baseEnd_3265833 < baseStart_3265833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265837 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 9]
def baseStart_3265837 : Nat := 118140960795 + 3265837 * 2 ^ 59
def prefixEnd_3265837 : Nat := 4983230072969 + 3 ^ 40 * 3265837 * 2
def baseEnd_3265837 : Nat := 186327124470849347935355

theorem tailTrace_3265837 : CollatzResearch.WordTrace tailWord_3265837 prefixEnd_3265837 186327124470849347935355 := by
  unfold tailWord_3265837
  simp only [CollatzResearch.WordTrace]
  refine ⟨119114861069437784399123765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79409907379625189599415843 119114861069437784399123765)
  ·
    refine ⟨11167018225259792287417853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119114861069437784399123765 11167018225259792287417853)
    ·
      refine ⟨4187631834472422107781695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11167018225259792287417853 4187631834472422107781695)
      ·
        refine ⟨6281447751708633161672543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187631834472422107781695 6281447751708633161672543)
        ·
          refine ⟨9422171627562949742508815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281447751708633161672543 9422171627562949742508815)
          ·
            refine ⟨14133257441344424613763223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422171627562949742508815 14133257441344424613763223)
            ·
              refine ⟨21199886162016636920644835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133257441344424613763223 21199886162016636920644835)
              ·
                refine ⟨31799829243024955380967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21199886162016636920644835 31799829243024955380967253)
                ·
                  refine ⟨186327124470849347935355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31799829243024955380967253 186327124470849347935355)
                  ·
                    rfl

theorem cell23_3265837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_3265837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265837 prefixEnd_3265837 := by exact prefixLift 3265837
  have htrace : WordTrace (prefixWord ++ tailWord_3265837) baseStart_3265837 baseEnd_3265837 := by
    simpa [prefixWord, tailWord_3265837, baseEnd_3265837] using wordTrace_append hprefix tailTrace_3265837
  have hstable : (prefixWord ++ tailWord_3265837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265837).length < 2 ^ (prefixWord ++ tailWord_3265837).sum := by decide
  have hdescent : baseEnd_3265837 < baseStart_3265837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265850 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_3265850 : Nat := 118140960795 + 3265850 * 2 ^ 59
def prefixEnd_3265850 : Nat := 4983230072969 + 3 ^ 40 * 3265850 * 2
def baseEnd_3265850 : Nat := 558983598495384193518545

theorem tailTrace_3265850 : CollatzResearch.WordTrace tailWord_3265850 prefixEnd_3265850 558983598495384193518545 := by
  unfold tailWord_3265850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778833804597671904836751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79410223478927125079564669 29778833804597671904836751)
  ·
    refine ⟨44668250706896507857255127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29778833804597671904836751 44668250706896507857255127)
    ·
      refine ⟨67002376060344761785882691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44668250706896507857255127 67002376060344761785882691)
      ·
        refine ⟨100503564090517142678824037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67002376060344761785882691 100503564090517142678824037)
        ·
          refine ⟨18844418266971964252279507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100503564090517142678824037 18844418266971964252279507)
          ·
            refine ⟨28266627400457946378419261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18844418266971964252279507 28266627400457946378419261)
            ·
              refine ⟨10599985275171729891907223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28266627400457946378419261 10599985275171729891907223)
              ·
                refine ⟨15899977912757594837860835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10599985275171729891907223 15899977912757594837860835)
                ·
                  refine ⟨23849966869136392256791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15899977912757594837860835 23849966869136392256791253)
                  ·
                    refine ⟨558983598495384193518545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23849966869136392256791253 558983598495384193518545)
                    ·
                      rfl

theorem cell23_3265850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_3265850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265850 prefixEnd_3265850 := by exact prefixLift 3265850
  have htrace : WordTrace (prefixWord ++ tailWord_3265850) baseStart_3265850 baseEnd_3265850 := by
    simpa [prefixWord, tailWord_3265850, baseEnd_3265850] using wordTrace_append hprefix tailTrace_3265850
  have hstable : (prefixWord ++ tailWord_3265850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265850).length < 2 ^ (prefixWord ++ tailWord_3265850).sum := by decide
  have hdescent : baseEnd_3265850 < baseStart_3265850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265854 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3265854 : Nat := 118140960795 + 3265854 * 2 ^ 59
def prefixEnd_3265854 : Nat := 4983230072969 + 3 ^ 40 * 3265854 * 2
def baseEnd_3265854 : Nat := 186328094378752284989513

theorem tailTrace_3265854 : CollatzResearch.WordTrace tailWord_3265854 prefixEnd_3265854 186328094378752284989513 := by
  unfold tailWord_3265854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889435138797024537811577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79410320740250797534995077 14889435138797024537811577)
  ·
    refine ⟨11167076354097768403358683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14889435138797024537811577 11167076354097768403358683)
    ·
      refine ⟨16750614531146652605038025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11167076354097768403358683 16750614531146652605038025)
      ·
        refine ⟨12562960898359989453778519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16750614531146652605038025 12562960898359989453778519)
        ·
          refine ⟨18844441347539984180667779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12562960898359989453778519 18844441347539984180667779)
          ·
            refine ⟨28266662021309976271001669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18844441347539984180667779 28266662021309976271001669)
            ·
              refine ⟨5299999128995620550812813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28266662021309976271001669 5299999128995620550812813)
              ·
                refine ⟨1987499673373357706554805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5299999128995620550812813 1987499673373357706554805)
                ·
                  refine ⟨186328094378752284989513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987499673373357706554805 186328094378752284989513)
                  ·
                    rfl

theorem cell23_3265854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3265854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265854 prefixEnd_3265854 := by exact prefixLift 3265854
  have htrace : WordTrace (prefixWord ++ tailWord_3265854) baseStart_3265854 baseEnd_3265854 := by
    simpa [prefixWord, tailWord_3265854, baseEnd_3265854] using wordTrace_append hprefix tailTrace_3265854
  have hstable : (prefixWord ++ tailWord_3265854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265854).length < 2 ^ (prefixWord ++ tailWord_3265854).sum := by decide
  have hdescent : baseEnd_3265854 < baseStart_3265854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265924 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3265924 : Nat := 118140960795 + 3265924 * 2 ^ 59
def prefixEnd_3265924 : Nat := 4983230072969 + 3 ^ 40 * 3265924 * 2
def baseEnd_3265924 : Nat := 1676988793054585291030295

theorem tailTrace_3265924 : CollatzResearch.WordTrace tailWord_3265924 prefixEnd_3265924 1676988793054585291030295 := by
  unfold tailWord_3265924
  simp only [CollatzResearch.WordTrace]
  refine ⟨59559017110061299128770413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79412022813415065505027217 59559017110061299128770413)
  ·
    refine ⟨22334631416272987173288905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59559017110061299128770413 22334631416272987173288905)
    ·
      refine ⟨16750973562204740379966679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22334631416272987173288905 16750973562204740379966679)
      ·
        refine ⟨25126460343307110569950019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16750973562204740379966679 25126460343307110569950019)
        ·
          refine ⟨37689690514960665854925029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25126460343307110569950019 37689690514960665854925029)
          ·
            refine ⟨7066816971555124847798443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37689690514960665854925029 7066816971555124847798443)
            ·
              refine ⟨10600225457332687271697665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066816971555124847798443 10600225457332687271697665)
              ·
                refine ⟨7950169092999515453773249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10600225457332687271697665 7950169092999515453773249)
                ·
                  refine ⟨5962626819749636590329937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950169092999515453773249 5962626819749636590329937)
                  ·
                    refine ⟨4471970114812227442747453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5962626819749636590329937 4471970114812227442747453)
                    ·
                      refine ⟨1676988793054585291030295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4471970114812227442747453 1676988793054585291030295)
                      ·
                        rfl

theorem cell23_3265924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3265924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265924 prefixEnd_3265924 := by exact prefixLift 3265924
  have htrace : WordTrace (prefixWord ++ tailWord_3265924) baseStart_3265924 baseEnd_3265924 := by
    simpa [prefixWord, tailWord_3265924, baseEnd_3265924] using wordTrace_append hprefix tailTrace_3265924
  have hstable : (prefixWord ++ tailWord_3265924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265924).length < 2 ^ (prefixWord ++ tailWord_3265924).sum := by decide
  have hdescent : baseEnd_3265924 < baseStart_3265924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265931 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 1, 4]
def baseStart_3265931 : Nat := 118140960795 + 3265931 * 2 ^ 59
def prefixEnd_3265931 : Nat := 4983230072969 + 3 ^ 40 * 3265931 * 2
def baseEnd_3265931 : Nat := 558997462473055587880921

theorem tailTrace_3265931 : CollatzResearch.WordTrace tailWord_3265931 prefixEnd_3265931 558997462473055587880921 := by
  unfold tailWord_3265931
  simp only [CollatzResearch.WordTrace]
  refine ⟨119118289531097238453045647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79412193020731492302030431 119118289531097238453045647)
  ·
    refine ⟨178677434296645857679568471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119118289531097238453045647 178677434296645857679568471)
    ·
      refine ⟨268016151444968786519352707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178677434296645857679568471 268016151444968786519352707)
      ·
        refine ⟨402024227167453179779029061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268016151444968786519352707 402024227167453179779029061)
        ·
          refine ⟨75379542593897471208567949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402024227167453179779029061 75379542593897471208567949)
          ·
            refine ⟨28267328472711551703212981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75379542593897471208567949 28267328472711551703212981)
            ·
              refine ⟨2650062044316707972176217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28267328472711551703212981 2650062044316707972176217)
              ·
                refine ⟨1987546533237530979132163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2650062044316707972176217 1987546533237530979132163)
                ·
                  refine ⟨2981319799856296468698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987546533237530979132163 2981319799856296468698245)
                  ·
                    refine ⟨558997462473055587880921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981319799856296468698245 558997462473055587880921)
                    ·
                      rfl

theorem cell23_3265931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 4].length) (baseStart_3265931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265931 prefixEnd_3265931 := by exact prefixLift 3265931
  have htrace : WordTrace (prefixWord ++ tailWord_3265931) baseStart_3265931 baseEnd_3265931 := by
    simpa [prefixWord, tailWord_3265931, baseEnd_3265931] using wordTrace_append hprefix tailTrace_3265931
  have hstable : (prefixWord ++ tailWord_3265931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265931).length < 2 ^ (prefixWord ++ tailWord_3265931).sum := by decide
  have hdescent : baseEnd_3265931 < baseStart_3265931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265944 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 6]
def baseStart_3265944 : Nat := 118140960795 + 3265944 * 2 ^ 59
def prefixEnd_3265944 : Nat := 4983230072969 + 3 ^ 40 * 3265944 * 2
def baseEnd_3265944 : Nat := 186333229185297245864467

theorem tailTrace_3265944 : CollatzResearch.WordTrace tailWord_3265944 prefixEnd_3265944 186333229185297245864467 := by
  unfold tailWord_3265944
  simp only [CollatzResearch.WordTrace]
  refine ⟨59559381840025070836634443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79412509120033427782179257 59559381840025070836634443)
  ·
    refine ⟨89339072760037606254951665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59559381840025070836634443 89339072760037606254951665)
    ·
      refine ⟨67004304570028204691213749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89339072760037606254951665 67004304570028204691213749)
      ·
        refine ⟨6281653553440144189801289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67004304570028204691213749 6281653553440144189801289)
        ·
          refine ⟨4711240165080108142350967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6281653553440144189801289 4711240165080108142350967)
          ·
            refine ⟨7066860247620162213526451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711240165080108142350967 7066860247620162213526451)
            ·
              refine ⟨10600290371430243320289677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066860247620162213526451 10600290371430243320289677)
              ·
                refine ⟨3975108889286341245108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10600290371430243320289677 3975108889286341245108629)
                ·
                  refine ⟨186333229185297245864467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3975108889286341245108629 186333229185297245864467)
                  ·
                    rfl

theorem cell23_3265944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_3265944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265944 prefixEnd_3265944 := by exact prefixLift 3265944
  have htrace : WordTrace (prefixWord ++ tailWord_3265944) baseStart_3265944 baseEnd_3265944 := by
    simpa [prefixWord, tailWord_3265944, baseEnd_3265944] using wordTrace_append hprefix tailTrace_3265944
  have hstable : (prefixWord ++ tailWord_3265944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265944).length < 2 ^ (prefixWord ++ tailWord_3265944).sum := by decide
  have hdescent : baseEnd_3265944 < baseStart_3265944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265957 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_3265957 : Nat := 118140960795 + 3265957 * 2 ^ 59
def prefixEnd_3265957 : Nat := 4983230072969 + 3 ^ 40 * 3265957 * 2
def baseEnd_3265957 : Nat := 559001912638727887305881

theorem tailTrace_3265957 : CollatzResearch.WordTrace tailWord_3265957 prefixEnd_3265957 559001912638727887305881 := by
  unfold tailWord_3265957
  simp only [CollatzResearch.WordTrace]
  refine ⟨119119237829003044893492125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79412825219335363262328083 119119237829003044893492125)
  ·
    refine ⟨44669714185876141835059547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119119237829003044893492125 44669714185876141835059547)
    ·
      refine ⟨67004571278814212752589321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44669714185876141835059547 67004571278814212752589321)
      ·
        refine ⟨50253428459110659564441991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67004571278814212752589321 50253428459110659564441991)
        ·
          refine ⟨75380142688665989346662987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50253428459110659564441991 75380142688665989346662987)
          ·
            refine ⟨113070214032998984019994481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75380142688665989346662987 113070214032998984019994481)
            ·
              refine ⟨84802660524749238014995861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113070214032998984019994481 84802660524749238014995861)
              ·
                refine ⟨3975124712097620531952931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84802660524749238014995861 3975124712097620531952931)
                ·
                  refine ⟨5962687068146430797929397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975124712097620531952931 5962687068146430797929397)
                  ·
                    refine ⟨559001912638727887305881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5962687068146430797929397 559001912638727887305881)
                    ·
                      rfl

theorem cell23_3265957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_3265957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265957 prefixEnd_3265957 := by exact prefixLift 3265957
  have htrace : WordTrace (prefixWord ++ tailWord_3265957) baseStart_3265957 baseEnd_3265957 := by
    simpa [prefixWord, tailWord_3265957, baseEnd_3265957] using wordTrace_append hprefix tailTrace_3265957
  have hstable : (prefixWord ++ tailWord_3265957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265957).length < 2 ^ (prefixWord ++ tailWord_3265957).sum := by decide
  have hdescent : baseEnd_3265957 < baseStart_3265957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265964 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_3265964 : Nat := 118140960795 + 3265964 * 2 ^ 59
def prefixEnd_3265964 : Nat := 4983230072969 + 3 ^ 40 * 3265964 * 2
def baseEnd_3265964 : Nat := 1677009332280765134530111

theorem tailTrace_3265964 : CollatzResearch.WordTrace tailWord_3265964 prefixEnd_3265964 1677009332280765134530111 := by
  unfold tailWord_3265964
  simp only [CollatzResearch.WordTrace]
  refine ⟨59559746569988842544498473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79412995426651790059331297 59559746569988842544498473)
  ·
    refine ⟨44669809927491631908373855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59559746569988842544498473 44669809927491631908373855)
    ·
      refine ⟨67004714891237447862560783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44669809927491631908373855 67004714891237447862560783)
      ·
        refine ⟨100507072336856171793841175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67004714891237447862560783 100507072336856171793841175)
        ·
          refine ⟨150760608505284257690761763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100507072336856171793841175 150760608505284257690761763)
          ·
            refine ⟨226140912757926386536142645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150760608505284257690761763 226140912757926386536142645)
            ·
              refine ⟨21200710571055598737763373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226140912757926386536142645 21200710571055598737763373)
              ·
                refine ⟨7950266464145849526661265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21200710571055598737763373 7950266464145849526661265)
                ·
                  refine ⟨5962699848109387144995949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950266464145849526661265 5962699848109387144995949)
                  ·
                    refine ⟨2236012443041020179373481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5962699848109387144995949 2236012443041020179373481)
                    ·
                      refine ⟨1677009332280765134530111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236012443041020179373481 1677009332280765134530111)
                      ·
                        rfl

theorem cell23_3265964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_3265964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265964 prefixEnd_3265964 := by exact prefixLift 3265964
  have htrace : WordTrace (prefixWord ++ tailWord_3265964) baseStart_3265964 baseEnd_3265964 := by
    simpa [prefixWord, tailWord_3265964, baseEnd_3265964] using wordTrace_append hprefix tailTrace_3265964
  have hstable : (prefixWord ++ tailWord_3265964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265964).length < 2 ^ (prefixWord ++ tailWord_3265964).sum := by decide
  have hdescent : baseEnd_3265964 < baseStart_3265964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265987 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 4, 4]
def baseStart_3265987 : Nat := 118140960795 + 3265987 * 2 ^ 59
def prefixEnd_3265987 : Nat := 4983230072969 + 3 ^ 40 * 3265987 * 2
def baseEnd_3265987 : Nat := 559007047445272848180835

theorem tailTrace_3265987 : CollatzResearch.WordTrace tailWord_3265987 prefixEnd_3265987 559007047445272848180835 := by
  unfold tailWord_3265987
  simp only [CollatzResearch.WordTrace]
  refine ⟨119120332018894360017084215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79413554679262906678056143 119120332018894360017084215)
  ·
    refine ⟨178680498028341540025626323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119120332018894360017084215 178680498028341540025626323)
    ·
      refine ⟨268020747042512310038439485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178680498028341540025626323 268020747042512310038439485)
      ·
        refine ⟨100507780140942116264414807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268020747042512310038439485 100507780140942116264414807)
        ·
          refine ⟨150761670211413174396622211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100507780140942116264414807 150761670211413174396622211)
          ·
            refine ⟨226142505317119761594933317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150761670211413174396622211 226142505317119761594933317)
            ·
              refine ⟨42401719746959955299049997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226142505317119761594933317 42401719746959955299049997)
              ·
                refine ⟨15900644905109983237143749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42401719746959955299049997 15900644905109983237143749)
                ·
                  refine ⟨2981370919708121856964453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15900644905109983237143749 2981370919708121856964453)
                  ·
                    refine ⟨559007047445272848180835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981370919708121856964453 559007047445272848180835)
                    ·
                      rfl

theorem cell23_3265987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 4].length) (baseStart_3265987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3265987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3265987 prefixEnd_3265987 := by exact prefixLift 3265987
  have htrace : WordTrace (prefixWord ++ tailWord_3265987) baseStart_3265987 baseEnd_3265987 := by
    simpa [prefixWord, tailWord_3265987, baseEnd_3265987] using wordTrace_append hprefix tailTrace_3265987
  have hstable : (prefixWord ++ tailWord_3265987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265987).length < 2 ^ (prefixWord ++ tailWord_3265987).sum := by decide
  have hdescent : baseEnd_3265987 < baseStart_3265987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266027 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3]
def baseStart_3266027 : Nat := 118140960795 + 3266027 * 2 ^ 59
def prefixEnd_3266027 : Nat := 4983230072969 + 3 ^ 40 * 3266027 * 2
def baseEnd_3266027 : Nat := 1677041681561998388042321

theorem tailTrace_3266027 : CollatzResearch.WordTrace tailWord_3266027 prefixEnd_3266027 1677041681561998388042321 := by
  unfold tailWord_3266027
  simp only [CollatzResearch.WordTrace]
  refine ⟨119121790938749446848540335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79414527292499631232360223 119121790938749446848540335)
  ·
    refine ⟨178682686408124170272810503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119121790938749446848540335 178682686408124170272810503)
    ·
      refine ⟨268024029612186255409215755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178682686408124170272810503 268024029612186255409215755)
      ·
        refine ⟨402036044418279383113823633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268024029612186255409215755 402036044418279383113823633)
        ·
          refine ⟨301527033313709537335367725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402036044418279383113823633 301527033313709537335367725)
          ·
            refine ⟨113072637492641076500762897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301527033313709537335367725 113072637492641076500762897)
            ·
              refine ⟨84804478119480807375572173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113072637492641076500762897 84804478119480807375572173)
              ·
                refine ⟨31801679294805302765839565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84804478119480807375572173 31801679294805302765839565)
                ·
                  refine ⟨11925629735551988537189837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31801679294805302765839565 11925629735551988537189837)
                  ·
                    refine ⟨4472111150831995701446189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11925629735551988537189837 4472111150831995701446189)
                    ·
                      refine ⟨1677041681561998388042321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472111150831995701446189 1677041681561998388042321)
                      ·
                        rfl

theorem cell23_3266027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3].length) (baseStart_3266027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266027 prefixEnd_3266027 := by exact prefixLift 3266027
  have htrace : WordTrace (prefixWord ++ tailWord_3266027) baseStart_3266027 baseEnd_3266027 := by
    simpa [prefixWord, tailWord_3266027, baseEnd_3266027] using wordTrace_append hprefix tailTrace_3266027
  have hstable : (prefixWord ++ tailWord_3266027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266027).length < 2 ^ (prefixWord ++ tailWord_3266027).sum := by decide
  have hdescent : baseEnd_3266027 < baseStart_3266027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266031 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 1, 2, 3]
def baseStart_3266031 : Nat := 118140960795 + 3266031 * 2 ^ 59
def prefixEnd_3266031 : Nat := 4983230072969 + 3 ^ 40 * 3266031 * 2
def baseEnd_3266031 : Nat := 1677043735484616372392303

theorem tailTrace_3266031 : CollatzResearch.WordTrace tailWord_3266031 prefixEnd_3266031 1677043735484616372392303 := by
  unfold tailWord_3266031
  simp only [CollatzResearch.WordTrace]
  refine ⟨119121936830734955531685947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79414624553823303687790631 119121936830734955531685947)
  ·
    refine ⟨178682905246102433297528921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119121936830734955531685947 178682905246102433297528921)
    ·
      refine ⟨134012178934576824973146691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178682905246102433297528921 134012178934576824973146691)
      ·
        refine ⟨201018268401865237459720037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134012178934576824973146691 201018268401865237459720037)
        ·
          refine ⟨37690925325349732023697507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201018268401865237459720037 37690925325349732023697507)
          ·
            refine ⟨56536387988024598035546261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37690925325349732023697507 56536387988024598035546261)
            ·
              refine ⟨2650143186938653032916231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56536387988024598035546261 2650143186938653032916231)
              ·
                refine ⟨3975214780407979549374347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650143186938653032916231 3975214780407979549374347)
                ·
                  refine ⟨5962822170611969324061521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975214780407979549374347 5962822170611969324061521)
                  ·
                    refine ⟨4472116627958976993046141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5962822170611969324061521 4472116627958976993046141)
                    ·
                      refine ⟨1677043735484616372392303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472116627958976993046141 1677043735484616372392303)
                      ·
                        rfl

theorem cell23_3266031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 2, 3].length) (baseStart_3266031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266031 prefixEnd_3266031 := by exact prefixLift 3266031
  have htrace : WordTrace (prefixWord ++ tailWord_3266031) baseStart_3266031 baseEnd_3266031 := by
    simpa [prefixWord, tailWord_3266031, baseEnd_3266031] using wordTrace_append hprefix tailTrace_3266031
  have hstable : (prefixWord ++ tailWord_3266031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266031).length < 2 ^ (prefixWord ++ tailWord_3266031).sum := by decide
  have hdescent : baseEnd_3266031 < baseStart_3266031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266038 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3266038 : Nat := 118140960795 + 3266038 * 2 ^ 59
def prefixEnd_3266038 : Nat := 4983230072969 + 3 ^ 40 * 3266038 * 2
def baseEnd_3266038 : Nat := 559015776616399281668257

theorem tailTrace_3266038 : CollatzResearch.WordTrace tailWord_3266038 prefixEnd_3266038 559015776616399281668257 := by
  unfold tailWord_3266038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7445137008856849732949423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79414794761139730484793845 7445137008856849732949423)
  ·
    refine ⟨11167705513285274599424135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7445137008856849732949423 11167705513285274599424135)
    ·
      refine ⟨16751558269927911899136203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11167705513285274599424135 16751558269927911899136203)
      ·
        refine ⟨25127337404891867848704305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16751558269927911899136203 25127337404891867848704305)
        ·
          refine ⟨18845503053668900886528229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25127337404891867848704305 18845503053668900886528229)
          ·
            refine ⟨3533531822562918916224043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18845503053668900886528229 3533531822562918916224043)
            ·
              refine ⟨5300297733844378374336065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533531822562918916224043 5300297733844378374336065)
              ·
                refine ⟨3975223300383283780752049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300297733844378374336065 3975223300383283780752049)
                ·
                  refine ⟨2981417475287462835564037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3975223300383283780752049 2981417475287462835564037)
                  ·
                    refine ⟨559015776616399281668257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981417475287462835564037 559015776616399281668257)
                    ·
                      rfl

theorem cell23_3266038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3266038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266038 prefixEnd_3266038 := by exact prefixLift 3266038
  have htrace : WordTrace (prefixWord ++ tailWord_3266038) baseStart_3266038 baseEnd_3266038 := by
    simpa [prefixWord, tailWord_3266038, baseEnd_3266038] using wordTrace_append hprefix tailTrace_3266038
  have hstable : (prefixWord ++ tailWord_3266038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266038).length < 2 ^ (prefixWord ++ tailWord_3266038).sum := by decide
  have hdescent : baseEnd_3266038 < baseStart_3266038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266068 : List Nat := [2, 4, 3, 1, 2, 2, 2, 7]
def baseStart_3266068 : Nat := 118140960795 + 3266068 * 2 ^ 59
def prefixEnd_3266068 : Nat := 4983230072969 + 3 ^ 40 * 3266068 * 2
def baseEnd_3266068 : Nat := 62113434602549360282579

theorem tailTrace_3266068 : CollatzResearch.WordTrace tailWord_3266068 prefixEnd_3266068 62113434602549360282579 := by
  unfold tailWord_3266068
  simp only [CollatzResearch.WordTrace]
  refine ⟨59561643165800455425391429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79415524221067273900521905 59561643165800455425391429)
  ·
    refine ⟨11167808093587585392260893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59561643165800455425391429 11167808093587585392260893)
    ·
      refine ⟨4187928035095344522097835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11167808093587585392260893 4187928035095344522097835)
      ·
        refine ⟨6281892052643016783146753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187928035095344522097835 6281892052643016783146753)
        ·
          refine ⟨4711419039482262587360065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6281892052643016783146753 4711419039482262587360065)
          ·
            refine ⟨3533564279611696940520049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711419039482262587360065 3533564279611696940520049)
            ·
              refine ⟨2650173209708772705390037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533564279611696940520049 2650173209708772705390037)
              ·
                refine ⟨62113434602549360282579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2650173209708772705390037 62113434602549360282579)
                ·
                  rfl

theorem cell23_3266068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 7].length) (baseStart_3266068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266068 prefixEnd_3266068 := by exact prefixLift 3266068
  have htrace : WordTrace (prefixWord ++ tailWord_3266068) baseStart_3266068 baseEnd_3266068 := by
    simpa [prefixWord, tailWord_3266068, baseEnd_3266068] using wordTrace_append hprefix tailTrace_3266068
  have hstable : (prefixWord ++ tailWord_3266068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266068).length < 2 ^ (prefixWord ++ tailWord_3266068).sum := by decide
  have hdescent : baseEnd_3266068 < baseStart_3266068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266137 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_3266137 : Nat := 118140960795 + 3266137 * 2 ^ 59
def prefixEnd_3266137 : Nat := 4983230072969 + 3 ^ 40 * 3266137 * 2
def baseEnd_3266137 : Nat := 559032721477997652555605

theorem tailTrace_3266137 : CollatzResearch.WordTrace tailWord_3266137 prefixEnd_3266137 559032721477997652555605 := by
  unfold tailWord_3266137
  simp only [CollatzResearch.WordTrace]
  refine ⟨119125802968350935635044665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79417201978900623756696443 119125802968350935635044665)
  ·
    refine ⟨89344352226263201726283499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119125802968350935635044665 89344352226263201726283499)
    ·
      refine ⟨134016528339394802589425249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89344352226263201726283499 134016528339394802589425249)
      ·
        refine ⟨100512396254546101942068937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134016528339394802589425249 100512396254546101942068937)
        ·
          refine ⟨75384297190909576456551703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100512396254546101942068937 75384297190909576456551703)
          ·
            refine ⟨113076445786364364684827555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75384297190909576456551703 113076445786364364684827555)
            ·
              refine ⟨169614668679546547027241333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113076445786364364684827555 169614668679546547027241333)
              ·
                refine ⟨15901375188707488783803875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169614668679546547027241333 15901375188707488783803875)
                ·
                  refine ⟨23852062783061233175705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15901375188707488783803875 23852062783061233175705813)
                  ·
                    refine ⟨559032721477997652555605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23852062783061233175705813 559032721477997652555605)
                    ·
                      rfl

theorem cell23_3266137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_3266137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266137 prefixEnd_3266137 := by exact prefixLift 3266137
  have htrace : WordTrace (prefixWord ++ tailWord_3266137) baseStart_3266137 baseEnd_3266137 := by
    simpa [prefixWord, tailWord_3266137, baseEnd_3266137] using wordTrace_append hprefix tailTrace_3266137
  have hstable : (prefixWord ++ tailWord_3266137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266137).length < 2 ^ (prefixWord ++ tailWord_3266137).sum := by decide
  have hdescent : baseEnd_3266137 < baseStart_3266137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266158 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_3266158 : Nat := 118140960795 + 3266158 * 2 ^ 59
def prefixEnd_3266158 : Nat := 4983230072969 + 3 ^ 40 * 3266158 * 2
def baseEnd_3266158 : Nat := 186345438614193041722691

theorem tailTrace_3266158 : CollatzResearch.WordTrace tailWord_3266158 prefixEnd_3266158 186345438614193041722691 := by
  unfold tailWord_3266158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14890821112659357027694891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79417712600849904147706085 14890821112659357027694891)
  ·
    refine ⟨22336231668989035541542337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14890821112659357027694891 22336231668989035541542337)
    ·
      refine ⟨16752173751741776656156753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22336231668989035541542337 16752173751741776656156753)
      ·
        refine ⟨12564130313806332492117565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16752173751741776656156753 12564130313806332492117565)
        ·
          refine ⟨4711548867677374684544087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12564130313806332492117565 4711548867677374684544087)
          ·
            refine ⟨7067323301516062026816131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711548867677374684544087 7067323301516062026816131)
            ·
              refine ⟨10600984952274093040224197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067323301516062026816131 10600984952274093040224197)
              ·
                refine ⟨1987684678551392445042037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10600984952274093040224197 1987684678551392445042037)
                ·
                  refine ⟨186345438614193041722691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987684678551392445042037 186345438614193041722691)
                  ·
                    rfl

theorem cell23_3266158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_3266158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266158 prefixEnd_3266158 := by exact prefixLift 3266158
  have htrace : WordTrace (prefixWord ++ tailWord_3266158) baseStart_3266158 baseEnd_3266158 := by
    simpa [prefixWord, tailWord_3266158, baseEnd_3266158] using wordTrace_append hprefix tailTrace_3266158
  have hstable : (prefixWord ++ tailWord_3266158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266158).length < 2 ^ (prefixWord ++ tailWord_3266158).sum := by decide
  have hdescent : baseEnd_3266158 < baseStart_3266158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266167 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 8]
def baseStart_3266167 : Nat := 118140960795 + 3266167 * 2 ^ 59
def prefixEnd_3266167 : Nat := 4983230072969 + 3 ^ 40 * 3266167 * 2
def baseEnd_3266167 : Nat := 559037856284542613430559

theorem tailTrace_3266167 : CollatzResearch.WordTrace tailWord_3266167 prefixEnd_3266167 559037856284542613430559 := by
  unfold tailWord_3266167
  simp only [CollatzResearch.WordTrace]
  refine ⟨119126897158242250758636755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79417931438828167172424503 119126897158242250758636755)
  ·
    refine ⟨178690345737363376137955133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119126897158242250758636755 178690345737363376137955133)
    ·
      refine ⟨67008879651511266051733175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178690345737363376137955133 67008879651511266051733175)
      ·
        refine ⟨100513319477266899077599763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67008879651511266051733175 100513319477266899077599763)
        ·
          refine ⟨150769979215900348616399645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100513319477266899077599763 150769979215900348616399645)
          ·
            refine ⟨56538742205962630731149867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150769979215900348616399645 56538742205962630731149867)
            ·
              refine ⟨84808113308943946096724801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56538742205962630731149867 84808113308943946096724801)
              ·
                refine ⟨63606084981707959572543601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84808113308943946096724801 63606084981707959572543601)
                ·
                  refine ⟨47704563736280969679407701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63606084981707959572543601 47704563736280969679407701)
                  ·
                    refine ⟨559037856284542613430559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47704563736280969679407701 559037856284542613430559)
                    ·
                      rfl

theorem cell23_3266167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_3266167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266167 prefixEnd_3266167 := by exact prefixLift 3266167
  have htrace : WordTrace (prefixWord ++ tailWord_3266167) baseStart_3266167 baseEnd_3266167 := by
    simpa [prefixWord, tailWord_3266167, baseEnd_3266167] using wordTrace_append hprefix tailTrace_3266167
  have hstable : (prefixWord ++ tailWord_3266167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266167).length < 2 ^ (prefixWord ++ tailWord_3266167).sum := by decide
  have hdescent : baseEnd_3266167 < baseStart_3266167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266251 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 6, 3, 2]
def baseStart_3266251 : Nat := 118140960795 + 3266251 * 2 ^ 59
def prefixEnd_3266251 : Nat := 4983230072969 + 3 ^ 40 * 3266251 * 2
def baseEnd_3266251 : Nat := 1677156701228605511641291

theorem tailTrace_3266251 : CollatzResearch.WordTrace tailWord_3266251 prefixEnd_3266251 1677156701228605511641291 := by
  unfold tailWord_3266251
  simp only [CollatzResearch.WordTrace]
  refine ⟨119129960889937933104694607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79419973926625288736463071 119129960889937933104694607)
  ·
    refine ⟨178694941334906899657041911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119129960889937933104694607 178694941334906899657041911)
    ·
      refine ⟨268042412002360349485562867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178694941334906899657041911 268042412002360349485562867)
      ·
        refine ⟨402063618003540524228344301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268042412002360349485562867 402063618003540524228344301)
        ·
          refine ⟨150773856751327696585629113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402063618003540524228344301 150773856751327696585629113)
          ·
            refine ⟨113080392563495772439221835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150773856751327696585629113 113080392563495772439221835)
            ·
              refine ⟨169620588845243658658832753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113080392563495772439221835 169620588845243658658832753)
              ·
                refine ⟨127215441633932743994124565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169620588845243658658832753 127215441633932743994124565)
                ·
                  refine ⟨5963223826590597374724589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127215441633932743994124565 5963223826590597374724589)
                  ·
                    refine ⟨2236208934971474015521721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5963223826590597374724589 2236208934971474015521721)
                    ·
                      refine ⟨1677156701228605511641291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236208934971474015521721 1677156701228605511641291)
                      ·
                        rfl

theorem cell23_3266251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3, 2].length) (baseStart_3266251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266251 prefixEnd_3266251 := by exact prefixLift 3266251
  have htrace : WordTrace (prefixWord ++ tailWord_3266251) baseStart_3266251 baseEnd_3266251 := by
    simpa [prefixWord, tailWord_3266251, baseEnd_3266251] using wordTrace_append hprefix tailTrace_3266251
  have hstable : (prefixWord ++ tailWord_3266251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266251).length < 2 ^ (prefixWord ++ tailWord_3266251).sum := by decide
  have hdescent : baseEnd_3266251 < baseStart_3266251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266252 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_3266252 : Nat := 118140960795 + 3266252 * 2 ^ 59
def prefixEnd_3266252 : Nat := 4983230072969 + 3 ^ 40 * 3266252 * 2
def baseEnd_3266252 : Nat := 559052404903086669242929

theorem tailTrace_3266252 : CollatzResearch.WordTrace tailWord_3266252 prefixEnd_3266252 559052404903086669242929 := by
  unfold tailWord_3266252
  simp only [CollatzResearch.WordTrace]
  refine ⟨59564998681467155137740505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79419998241956206850320673 59564998681467155137740505)
  ·
    refine ⟨44673749011100366353305379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59564998681467155137740505 44673749011100366353305379)
    ·
      refine ⟨67010623516650549529958069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44673749011100366353305379 67010623516650549529958069)
      ·
        refine ⟨6282245954685989018433569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67010623516650549529958069 6282245954685989018433569)
        ·
          refine ⟨4711684466014491763825177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6282245954685989018433569 4711684466014491763825177)
          ·
            refine ⟨3533763349510868822868883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711684466014491763825177 3533763349510868822868883)
            ·
              refine ⟨5300645024266303234303325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533763349510868822868883 5300645024266303234303325)
              ·
                refine ⟨1987741884099863712863747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5300645024266303234303325 1987741884099863712863747)
                ·
                  refine ⟨2981612826149795569295621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987741884099863712863747 2981612826149795569295621)
                  ·
                    refine ⟨559052404903086669242929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981612826149795569295621 559052404903086669242929)
                    ·
                      rfl

theorem cell23_3266252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_3266252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266252 prefixEnd_3266252 := by exact prefixLift 3266252
  have htrace : WordTrace (prefixWord ++ tailWord_3266252) baseStart_3266252 baseEnd_3266252 := by
    simpa [prefixWord, tailWord_3266252, baseEnd_3266252] using wordTrace_append hprefix tailTrace_3266252
  have hstable : (prefixWord ++ tailWord_3266252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266252).length < 2 ^ (prefixWord ++ tailWord_3266252).sum := by decide
  have hdescent : baseEnd_3266252 < baseStart_3266252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266262 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3266262 : Nat := 118140960795 + 3266262 * 2 ^ 59
def prefixEnd_3266262 : Nat := 4983230072969 + 3 ^ 40 * 3266262 * 2
def baseEnd_3266262 : Nat := 1677162349515804968603741

theorem tailTrace_3266262 : CollatzResearch.WordTrace tailWord_3266262 prefixEnd_3266262 1677162349515804968603741 := by
  unfold tailWord_3266262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7445647630806130123959065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79420241395265387988896693 7445647630806130123959065)
  ·
    refine ⟨5584235723104597592969299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7445647630806130123959065 5584235723104597592969299)
    ·
      refine ⟨8376353584656896389453949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584235723104597592969299 8376353584656896389453949)
      ·
        refine ⟨3141132594246336146045231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8376353584656896389453949 3141132594246336146045231)
        ·
          refine ⟨4711698891369504219067847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141132594246336146045231 4711698891369504219067847)
          ·
            refine ⟨7067548337054256328601771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711698891369504219067847 7067548337054256328601771)
            ·
              refine ⟨10601322505581384492902657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067548337054256328601771 10601322505581384492902657)
              ·
                refine ⟨7950991879186038369676993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10601322505581384492902657 7950991879186038369676993)
                ·
                  refine ⟨5963243909389528777257745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950991879186038369676993 5963243909389528777257745)
                  ·
                    refine ⟨4472432932042146582943309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5963243909389528777257745 4472432932042146582943309)
                    ·
                      refine ⟨1677162349515804968603741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472432932042146582943309 1677162349515804968603741)
                      ·
                        rfl

theorem cell23_3266262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3266262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266262 prefixEnd_3266262 := by exact prefixLift 3266262
  have htrace : WordTrace (prefixWord ++ tailWord_3266262) baseStart_3266262 baseEnd_3266262 := by
    simpa [prefixWord, tailWord_3266262, baseEnd_3266262] using wordTrace_append hprefix tailTrace_3266262
  have hstable : (prefixWord ++ tailWord_3266262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266262).length < 2 ^ (prefixWord ++ tailWord_3266262).sum := by decide
  have hdescent : baseEnd_3266262 < baseStart_3266262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266269 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_3266269 : Nat := 118140960795 + 3266269 * 2 ^ 59
def prefixEnd_3266269 : Nat := 4983230072969 + 3 ^ 40 * 3266269 * 2
def baseEnd_3266269 : Nat := 559055314626795480405403

theorem tailTrace_3266269 : CollatzResearch.WordTrace tailWord_3266269 prefixEnd_3266269 559055314626795480405403 := by
  unfold tailWord_3266269
  simp only [CollatzResearch.WordTrace]
  refine ⟨119130617403872722178849861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79420411602581814785899907 119130617403872722178849861)
  ·
    refine ⟨22336990763226135408534349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119130617403872722178849861 22336990763226135408534349)
    ·
      refine ⟨8376371536209800778200381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22336990763226135408534349 8376371536209800778200381)
      ·
        refine ⟨3141139326078675291825143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8376371536209800778200381 3141139326078675291825143)
        ·
          refine ⟨4711708989118012937737715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141139326078675291825143 4711708989118012937737715)
          ·
            refine ⟨7067563483677019406606573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711708989118012937737715 7067563483677019406606573)
            ·
              refine ⟨2650336306378882277477465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7067563483677019406606573 2650336306378882277477465)
              ·
                refine ⟨1987752229784161708108099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2650336306378882277477465 1987752229784161708108099)
                ·
                  refine ⟨2981628344676242562162149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987752229784161708108099 2981628344676242562162149)
                  ·
                    refine ⟨559055314626795480405403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981628344676242562162149 559055314626795480405403)
                    ·
                      rfl

theorem cell23_3266269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_3266269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266269 prefixEnd_3266269 := by exact prefixLift 3266269
  have htrace : WordTrace (prefixWord ++ tailWord_3266269) baseStart_3266269 baseEnd_3266269 := by
    simpa [prefixWord, tailWord_3266269, baseEnd_3266269] using wordTrace_append hprefix tailTrace_3266269
  have hstable : (prefixWord ++ tailWord_3266269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266269).length < 2 ^ (prefixWord ++ tailWord_3266269).sum := by decide
  have hdescent : baseEnd_3266269 < baseStart_3266269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266298 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_3266298 : Nat := 118140960795 + 3266298 * 2 ^ 59
def prefixEnd_3266298 : Nat := 4983230072969 + 3 ^ 40 * 3266298 * 2
def baseEnd_3266298 : Nat := 1677180834819366827753575

theorem tailTrace_3266298 : CollatzResearch.WordTrace tailWord_3266298 prefixEnd_3266298 1677180834819366827753575 := by
  unfold tailWord_3266298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782918780191915032913887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79421116747178440087770365 29782918780191915032913887)
  ·
    refine ⟨44674378170287872549370831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29782918780191915032913887 44674378170287872549370831)
    ·
      refine ⟨67011567255431808824056247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44674378170287872549370831 67011567255431808824056247)
      ·
        refine ⟨100517350883147713236084371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67011567255431808824056247 100517350883147713236084371)
        ·
          refine ⟨150776026324721569854126557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100517350883147713236084371 150776026324721569854126557)
          ·
            refine ⟨56541009871770588695297459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150776026324721569854126557 56541009871770588695297459)
            ·
              refine ⟨84811514807655883042946189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56541009871770588695297459 84811514807655883042946189)
              ·
                refine ⟨31804318052870956141104821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84811514807655883042946189 31804318052870956141104821)
                ·
                  refine ⟨2981654817456652138228577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31804318052870956141104821 2981654817456652138228577)
                  ·
                    refine ⟨2236241113092489103671433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2981654817456652138228577 2236241113092489103671433)
                    ·
                      refine ⟨1677180834819366827753575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236241113092489103671433 1677180834819366827753575)
                      ·
                        rfl

theorem cell23_3266298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_3266298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266298 prefixEnd_3266298 := by exact prefixLift 3266298
  have htrace : WordTrace (prefixWord ++ tailWord_3266298) baseStart_3266298 baseEnd_3266298 := by
    simpa [prefixWord, tailWord_3266298, baseEnd_3266298] using wordTrace_append hprefix tailTrace_3266298
  have hstable : (prefixWord ++ tailWord_3266298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266298).length < 2 ^ (prefixWord ++ tailWord_3266298).sum := by decide
  have hdescent : baseEnd_3266298 < baseStart_3266298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266302 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_3266302 : Nat := 118140960795 + 3266302 * 2 ^ 59
def prefixEnd_3266302 : Nat := 4983230072969 + 3 ^ 40 * 3266302 * 2
def baseEnd_3266302 : Nat := 1677182888741984812103557

theorem tailTrace_3266302 : CollatzResearch.WordTrace tailWord_3266302 prefixEnd_3266302 1677182888741984812103557 := by
  unfold tailWord_3266302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891477626594146101850145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79421214008502112543200773 14891477626594146101850145)
  ·
    refine ⟨11168608219945609576387609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14891477626594146101850145 11168608219945609576387609)
    ·
      refine ⟨8376456164959207182290707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11168608219945609576387609 8376456164959207182290707)
      ·
        refine ⟨12564684247438810773436061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8376456164959207182290707 12564684247438810773436061)
        ·
          refine ⟨4711756592789554040038523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12564684247438810773436061 4711756592789554040038523)
          ·
            refine ⟨7067634889184331060057785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711756592789554040038523 7067634889184331060057785)
            ·
              refine ⟨5300726166888248295043339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7067634889184331060057785 5300726166888248295043339)
              ·
                refine ⟨7951089250332372442565009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300726166888248295043339 7951089250332372442565009)
                ·
                  refine ⟨5963316937749279331923757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7951089250332372442565009 5963316937749279331923757)
                  ·
                    refine ⟨2236243851655979749471409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5963316937749279331923757 2236243851655979749471409)
                    ·
                      refine ⟨1677182888741984812103557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236243851655979749471409 1677182888741984812103557)
                      ·
                        rfl

theorem cell23_3266302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_3266302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266302 prefixEnd_3266302 := by exact prefixLift 3266302
  have htrace : WordTrace (prefixWord ++ tailWord_3266302) baseStart_3266302 baseEnd_3266302 := by
    simpa [prefixWord, tailWord_3266302, baseEnd_3266302] using wordTrace_append hprefix tailTrace_3266302
  have hstable : (prefixWord ++ tailWord_3266302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266302).length < 2 ^ (prefixWord ++ tailWord_3266302).sum := by decide
  have hdescent : baseEnd_3266302 < baseStart_3266302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266318 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3266318 : Nat := 118140960795 + 3266318 * 2 ^ 59
def prefixEnd_3266318 : Nat := 4983230072969 + 3 ^ 40 * 3266318 * 2
def baseEnd_3266318 : Nat := 1677191104432456749503483

theorem tailTrace_3266318 : CollatzResearch.WordTrace tailWord_3266318 prefixEnd_3266318 1677191104432456749503483 := by
  unfold tailWord_3266318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891550572586900443422951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79421603053796802364922405 14891550572586900443422951)
  ·
    refine ⟨22337325858880350665134427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14891550572586900443422951 22337325858880350665134427)
    ·
      refine ⟨33505988788320525997701641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22337325858880350665134427 33505988788320525997701641)
      ·
        refine ⟨25129491591240394498276231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33505988788320525997701641 25129491591240394498276231)
        ·
          refine ⟨37694237386860591747414347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25129491591240394498276231 37694237386860591747414347)
          ·
            refine ⟨56541356080290887621121521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37694237386860591747414347 56541356080290887621121521)
            ·
              refine ⟨42406017060218165715841141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56541356080290887621121521 42406017060218165715841141)
              ·
                refine ⟨3975564099395453035860107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42406017060218165715841141 3975564099395453035860107)
                ·
                  refine ⟨5963346149093179553790161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975564099395453035860107 5963346149093179553790161)
                  ·
                    refine ⟨4472509611819884665342621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5963346149093179553790161 4472509611819884665342621)
                    ·
                      refine ⟨1677191104432456749503483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472509611819884665342621 1677191104432456749503483)
                      ·
                        rfl

theorem cell23_3266318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3266318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266318 prefixEnd_3266318 := by exact prefixLift 3266318
  have htrace : WordTrace (prefixWord ++ tailWord_3266318) baseStart_3266318 baseEnd_3266318 := by
    simpa [prefixWord, tailWord_3266318, baseEnd_3266318] using wordTrace_append hprefix tailTrace_3266318
  have hstable : (prefixWord ++ tailWord_3266318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266318).length < 2 ^ (prefixWord ++ tailWord_3266318).sum := by decide
  have hdescent : baseEnd_3266318 < baseStart_3266318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266332 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3266332 : Nat := 118140960795 + 3266332 * 2 ^ 59
def prefixEnd_3266332 : Nat := 4983230072969 + 3 ^ 40 * 3266332 * 2
def baseEnd_3266332 : Nat := 1677198293161619694728419

theorem tailTrace_3266332 : CollatzResearch.WordTrace tailWord_3266332 prefixEnd_3266332 1677198293161619694728419 := by
  unfold tailWord_3266332
  simp only [CollatzResearch.WordTrace]
  refine ⟨59566457601322241969196625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79421943468429655958928833 59566457601322241969196625)
  ·
    refine ⟨44674843200991681476897469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59566457601322241969196625 44674843200991681476897469)
    ·
      refine ⟨16753066200371880553836551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44674843200991681476897469 16753066200371880553836551)
      ·
        refine ⟨25129599300557820830754827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16753066200371880553836551 25129599300557820830754827)
        ·
          refine ⟨37694398950836731246132241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25129599300557820830754827 37694398950836731246132241)
          ·
            refine ⟨28270799213127548434599181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37694398950836731246132241 28270799213127548434599181)
            ·
              refine ⟨10601549704922830662974693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28270799213127548434599181 10601549704922830662974693)
              ·
                refine ⟨1987790569673030749307755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10601549704922830662974693 1987790569673030749307755)
                ·
                  refine ⟨2981685854509546123961633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987790569673030749307755 2981685854509546123961633)
                  ·
                    refine ⟨2236264390882159592971225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2981685854509546123961633 2236264390882159592971225)
                    ·
                      refine ⟨1677198293161619694728419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236264390882159592971225 1677198293161619694728419)
                      ·
                        rfl

theorem cell23_3266332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3266332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266332 prefixEnd_3266332 := by exact prefixLift 3266332
  have htrace : WordTrace (prefixWord ++ tailWord_3266332) baseStart_3266332 baseEnd_3266332 := by
    simpa [prefixWord, tailWord_3266332, baseEnd_3266332] using wordTrace_append hprefix tailTrace_3266332
  have hstable : (prefixWord ++ tailWord_3266332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266332).length < 2 ^ (prefixWord ++ tailWord_3266332).sum := by decide
  have hdescent : baseEnd_3266332 < baseStart_3266332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266348 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_3266348 : Nat := 118140960795 + 3266348 * 2 ^ 59
def prefixEnd_3266348 : Nat := 4983230072969 + 3 ^ 40 * 3266348 * 2
def baseEnd_3266348 : Nat := 1677206508852091632128345

theorem tailTrace_3266348 : CollatzResearch.WordTrace tailWord_3266348 prefixEnd_3266348 1677206508852091632128345 := by
  unfold tailWord_3266348
  simp only [CollatzResearch.WordTrace]
  refine ⟨59566749385293259335487849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79422332513724345780650465 59566749385293259335487849)
  ·
    refine ⟨44675062038969944501615887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59566749385293259335487849 44675062038969944501615887)
    ·
      refine ⟨67012593058454916752423831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44675062038969944501615887 67012593058454916752423831)
      ·
        refine ⟨100518889587682375128635747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67012593058454916752423831 100518889587682375128635747)
        ·
          refine ⟨150778334381523562692953621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100518889587682375128635747 150778334381523562692953621)
          ·
            refine ⟨7067734424133917001232201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150778334381523562692953621 7067734424133917001232201)
            ·
              refine ⟨5300800818100437750924151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7067734424133917001232201 5300800818100437750924151)
              ·
                refine ⟨7951201227150656626386227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300800818100437750924151 7951201227150656626386227)
                ·
                  refine ⟨11926801840725984939579341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951201227150656626386227 11926801840725984939579341)
                  ·
                    refine ⟨4472550690272244352342253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11926801840725984939579341 4472550690272244352342253)
                    ·
                      refine ⟨1677206508852091632128345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472550690272244352342253 1677206508852091632128345)
                      ·
                        rfl

theorem cell23_3266348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_3266348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266348 prefixEnd_3266348 := by exact prefixLift 3266348
  have htrace : WordTrace (prefixWord ++ tailWord_3266348) baseStart_3266348 baseEnd_3266348 := by
    simpa [prefixWord, tailWord_3266348, baseEnd_3266348] using wordTrace_append hprefix tailTrace_3266348
  have hstable : (prefixWord ++ tailWord_3266348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266348).length < 2 ^ (prefixWord ++ tailWord_3266348).sum := by decide
  have hdescent : baseEnd_3266348 < baseStart_3266348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266401 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_3266401 : Nat := 118140960795 + 3266401 * 2 ^ 59
def prefixEnd_3266401 : Nat := 4983230072969 + 3 ^ 40 * 3266401 * 2
def baseEnd_3266401 : Nat := 1677233723326779924765601

theorem tailTrace_3266401 : CollatzResearch.WordTrace tailWord_3266401 prefixEnd_3266401 1677233723326779924765601 := by
  unfold tailWord_3266401
  simp only [CollatzResearch.WordTrace]
  refine ⟨119135431839394508722655057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79423621226263005815103371 119135431839394508722655057)
  ·
    refine ⟨89351573879545881541991293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119135431839394508722655057 89351573879545881541991293)
    ·
      refine ⟨33506840204829705578246735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89351573879545881541991293 33506840204829705578246735)
      ·
        refine ⟨50260260307244558367370103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33506840204829705578246735 50260260307244558367370103)
        ·
          refine ⟨75390390460866837551055155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50260260307244558367370103 75390390460866837551055155)
          ·
            refine ⟨113085585691300256326582733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75390390460866837551055155 113085585691300256326582733)
            ·
              refine ⟨42407094634237596122468525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113085585691300256326582733 42407094634237596122468525)
              ·
                refine ⟨15902660487839098545925697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42407094634237596122468525 15902660487839098545925697)
                ·
                  refine ⟨11926995365879323909444273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15902660487839098545925697 11926995365879323909444273)
                  ·
                    refine ⟨8945246524409492932083205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11926995365879323909444273 8945246524409492932083205)
                    ·
                      refine ⟨1677233723326779924765601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8945246524409492932083205 1677233723326779924765601)
                      ·
                        rfl

theorem cell23_3266401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_3266401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266401 prefixEnd_3266401 := by exact prefixLift 3266401
  have htrace : WordTrace (prefixWord ++ tailWord_3266401) baseStart_3266401 baseEnd_3266401 := by
    simpa [prefixWord, tailWord_3266401, baseEnd_3266401] using wordTrace_append hprefix tailTrace_3266401
  have hstable : (prefixWord ++ tailWord_3266401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266401).length < 2 ^ (prefixWord ++ tailWord_3266401).sum := by decide
  have hdescent : baseEnd_3266401 < baseStart_3266401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266505 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 1, 4]
def baseStart_3266505 : Nat := 118140960795 + 3266505 * 2 ^ 59
def prefixEnd_3266505 : Nat := 4983230072969 + 3 ^ 40 * 3266505 * 2
def baseEnd_3266505 : Nat := 559095708438282505955041

theorem tailTrace_3266505 : CollatzResearch.WordTrace tailWord_3266505 prefixEnd_3266505 559095708438282505955041 := by
  unfold tailWord_3266505
  simp only [CollatzResearch.WordTrace]
  refine ⟨119139225031017734484440969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79426150020678489656293979 119139225031017734484440969)
  ·
    refine ⟨89354418773263300863330727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119139225031017734484440969 89354418773263300863330727)
    ·
      refine ⟨134031628159894951294996091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89354418773263300863330727 134031628159894951294996091)
      ·
        refine ⟨201047442239842426942494137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134031628159894951294996091 201047442239842426942494137)
        ·
          refine ⟨150785581679881820206870603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201047442239842426942494137 150785581679881820206870603)
          ·
            refine ⟨226178372519822730310305905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150785581679881820206870603 226178372519822730310305905)
            ·
              refine ⟨169633779389867047732729429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226178372519822730310305905 169633779389867047732729429)
              ·
                refine ⟨1987895852225004465617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 169633779389867047732729429 1987895852225004465617923)
                ·
                  refine ⟨2981843778337506698426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987895852225004465617923 2981843778337506698426885)
                  ·
                    refine ⟨559095708438282505955041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981843778337506698426885 559095708438282505955041)
                    ·
                      rfl

theorem cell23_3266505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 4].length) (baseStart_3266505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266505 prefixEnd_3266505 := by exact prefixLift 3266505
  have htrace : WordTrace (prefixWord ++ tailWord_3266505) baseStart_3266505 baseEnd_3266505 := by
    simpa [prefixWord, tailWord_3266505, baseEnd_3266505] using wordTrace_append hprefix tailTrace_3266505
  have hstable : (prefixWord ++ tailWord_3266505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266505).length < 2 ^ (prefixWord ++ tailWord_3266505).sum := by decide
  have hdescent : baseEnd_3266505 < baseStart_3266505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266555 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 2, 3, 2]
def baseStart_3266555 : Nat := 118140960795 + 3266555 * 2 ^ 59
def prefixEnd_3266555 : Nat := 4983230072969 + 3 ^ 40 * 3266555 * 2
def baseEnd_3266555 : Nat := 1677312799347572322239893

theorem tailTrace_3266555 : CollatzResearch.WordTrace tailWord_3266555 prefixEnd_3266555 1677312799347572322239893 := by
  unfold tailWord_3266555
  simp only [CollatzResearch.WordTrace]
  refine ⟨119141048680836593023761119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79427365787224395349174079 119141048680836593023761119)
  ·
    refine ⟨178711573021254889535641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119141048680836593023761119 178711573021254889535641679)
    ·
      refine ⟨268067359531882334303462519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178711573021254889535641679 268067359531882334303462519)
      ·
        refine ⟨402101039297823501455193779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268067359531882334303462519 402101039297823501455193779)
        ·
          refine ⟨603151558946735252182790669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402101039297823501455193779 603151558946735252182790669)
          ·
            refine ⟨226181834605025719568546501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603151558946735252182790669 226181834605025719568546501)
            ·
              refine ⟨42409093988442322419102469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226181834605025719568546501 42409093988442322419102469)
              ·
                refine ⟨7951705122832935453581713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42409093988442322419102469 7951705122832935453581713)
                ·
                  refine ⟨5963778842124701590186285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7951705122832935453581713 5963778842124701590186285)
                  ·
                    refine ⟨2236417065796763096319857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5963778842124701590186285 2236417065796763096319857)
                    ·
                      refine ⟨1677312799347572322239893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236417065796763096319857 1677312799347572322239893)
                      ·
                        rfl

theorem cell23_3266555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3, 2].length) (baseStart_3266555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266555 prefixEnd_3266555 := by exact prefixLift 3266555
  have htrace : WordTrace (prefixWord ++ tailWord_3266555) baseStart_3266555 baseEnd_3266555 := by
    simpa [prefixWord, tailWord_3266555, baseEnd_3266555] using wordTrace_append hprefix tailTrace_3266555
  have hstable : (prefixWord ++ tailWord_3266555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266555).length < 2 ^ (prefixWord ++ tailWord_3266555).sum := by decide
  have hdescent : baseEnd_3266555 < baseStart_3266555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266602 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3266602 : Nat := 118140960795 + 3266602 * 2 ^ 59
def prefixEnd_3266602 : Nat := 4983230072969 + 3 ^ 40 * 3266602 * 2
def baseEnd_3266602 : Nat := 1677336932938333638352177

theorem tailTrace_3266602 : CollatzResearch.WordTrace tailWord_3266602 prefixEnd_3266602 1677336932938333638352177 := by
  unfold tailWord_3266602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785690727916580012680515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79428508607777546700481373 29785690727916580012680515)
  ·
    refine ⟨44678536091874870019020773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29785690727916580012680515 44678536091874870019020773)
    ·
      refine ⟨8377225517226538128566395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44678536091874870019020773 8377225517226538128566395)
      ·
        refine ⟨12565838275839807192849593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377225517226538128566395 12565838275839807192849593)
        ·
          refine ⟨9424378706879855394637195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12565838275839807192849593 9424378706879855394637195)
          ·
            refine ⟨14136568060319783091955793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424378706879855394637195 14136568060319783091955793)
            ·
              refine ⟨10602426045239837318966845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14136568060319783091955793 10602426045239837318966845)
              ·
                refine ⟨3975909766964938994612567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10602426045239837318966845 3975909766964938994612567)
                ·
                  refine ⟨5963864650447408491918851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975909766964938994612567 5963864650447408491918851)
                  ·
                    refine ⟨8945796975671112737878277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963864650447408491918851 8945796975671112737878277)
                    ·
                      refine ⟨1677336932938333638352177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8945796975671112737878277 1677336932938333638352177)
                      ·
                        rfl

theorem cell23_3266602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3266602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266602 prefixEnd_3266602 := by exact prefixLift 3266602
  have htrace : WordTrace (prefixWord ++ tailWord_3266602) baseStart_3266602 baseEnd_3266602 := by
    simpa [prefixWord, tailWord_3266602, baseEnd_3266602] using wordTrace_append hprefix tailTrace_3266602
  have hstable : (prefixWord ++ tailWord_3266602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266602).length < 2 ^ (prefixWord ++ tailWord_3266602).sum := by decide
  have hdescent : baseEnd_3266602 < baseStart_3266602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266608 : List Nat := [2, 1, 1, 1, 2, 7, 9]
def baseStart_3266608 : Nat := 118140960795 + 3266608 * 2 ^ 59
def prefixEnd_3266608 : Nat := 4983230072969 + 3 ^ 40 * 3266608 * 2
def baseEnd_3266608 : Nat := 20707901405213094010829

theorem tailTrace_3266608 : CollatzResearch.WordTrace tailWord_3266608 prefixEnd_3266608 20707901405213094010829 := by
  unfold tailWord_3266608
  simp only [CollatzResearch.WordTrace]
  refine ⟨59571490874822291537720239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79428654499763055383626985 59571490874822291537720239)
  ·
    refine ⟨89357236312233437306580359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59571490874822291537720239 89357236312233437306580359)
    ·
      refine ⟨134035854468350155959870539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89357236312233437306580359 134035854468350155959870539)
      ·
        refine ⟨201053781702525233939805809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134035854468350155959870539 201053781702525233939805809)
        ·
          refine ⟨150790336276893925454854357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201053781702525233939805809 150790336276893925454854357)
          ·
            refine ⟨3534148506489701377848149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150790336276893925454854357 3534148506489701377848149)
            ·
              refine ⟨20707901405213094010829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3534148506489701377848149 20707901405213094010829)
              ·
                rfl

theorem cell23_3266608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 9].length) (baseStart_3266608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266608 prefixEnd_3266608 := by exact prefixLift 3266608
  have htrace : WordTrace (prefixWord ++ tailWord_3266608) baseStart_3266608 baseEnd_3266608 := by
    simpa [prefixWord, tailWord_3266608, baseEnd_3266608] using wordTrace_append hprefix tailTrace_3266608
  have hstable : (prefixWord ++ tailWord_3266608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266608).length < 2 ^ (prefixWord ++ tailWord_3266608).sum := by decide
  have hdescent : baseEnd_3266608 < baseStart_3266608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266625 : List Nat := [1, 2, 5, 1, 2, 2, 2, 8]
def baseStart_3266625 : Nat := 118140960795 + 3266625 * 2 ^ 59
def prefixEnd_3266625 : Nat := 4983230072969 + 3 ^ 40 * 3266625 * 2
def baseEnd_3266625 : Nat := 62124027518273594383873

theorem tailTrace_3266625 : CollatzResearch.WordTrace tailWord_3266625 prefixEnd_3266625 62124027518273594383873 := by
  unfold tailWord_3266625
  simp only [CollatzResearch.WordTrace]
  refine ⟨119143601790582994978809329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79429067860388663319206219 119143601790582994978809329)
  ·
    refine ⟨89357701342937246234106997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119143601790582994978809329 89357701342937246234106997)
    ·
      refine ⟨8377284500900366834447531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89357701342937246234106997 8377284500900366834447531)
      ·
        refine ⟨12565926751350550251671297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377284500900366834447531 12565926751350550251671297)
        ·
          refine ⟨9424445063512912688753473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12565926751350550251671297 9424445063512912688753473)
          ·
            refine ⟨7068333797634684516565105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9424445063512912688753473 7068333797634684516565105)
            ·
              refine ⟨5301250348226013387423829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068333797634684516565105 5301250348226013387423829)
              ·
                refine ⟨62124027518273594383873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5301250348226013387423829 62124027518273594383873)
                ·
                  rfl

theorem cell23_3266625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 8].length) (baseStart_3266625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266625 prefixEnd_3266625 := by exact prefixLift 3266625
  have htrace : WordTrace (prefixWord ++ tailWord_3266625) baseStart_3266625 baseEnd_3266625 := by
    simpa [prefixWord, tailWord_3266625, baseEnd_3266625] using wordTrace_append hprefix tailTrace_3266625
  have hstable : (prefixWord ++ tailWord_3266625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266625).length < 2 ^ (prefixWord ++ tailWord_3266625).sum := by decide
  have hdescent : baseEnd_3266625 < baseStart_3266625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266652 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3266652 : Nat := 118140960795 + 3266652 * 2 ^ 59
def prefixEnd_3266652 : Nat := 4983230072969 + 3 ^ 40 * 3266652 * 2
def baseEnd_3266652 : Nat := 1677362606971058442726947

theorem tailTrace_3266652 : CollatzResearch.WordTrace tailWord_3266652 prefixEnd_3266652 1677362606971058442726947 := by
  unfold tailWord_3266652
  simp only [CollatzResearch.WordTrace]
  refine ⟨59572293280742589295021105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79429724374323452393361473 59572293280742589295021105)
  ·
    refine ⟨44679219960556941971265829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59572293280742589295021105 44679219960556941971265829)
    ·
      refine ⟨8377353742604426619612343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44679219960556941971265829 8377353742604426619612343)
      ·
        refine ⟨12566030613906639929418515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377353742604426619612343 12566030613906639929418515)
        ·
          refine ⟨18849045920859959894127773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12566030613906639929418515 18849045920859959894127773)
          ·
            refine ⟨7068392220322484960297915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18849045920859959894127773 7068392220322484960297915)
            ·
              refine ⟨10602588330483727440446873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068392220322484960297915 10602588330483727440446873)
              ·
                refine ⟨7951941247862795580335155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10602588330483727440446873 7951941247862795580335155)
                ·
                  refine ⟨11927911871794193370502733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951941247862795580335155 11927911871794193370502733)
                  ·
                    refine ⟨4472966951922822513938525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11927911871794193370502733 4472966951922822513938525)
                    ·
                      refine ⟨1677362606971058442726947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472966951922822513938525 1677362606971058442726947)
                      ·
                        rfl

theorem cell23_3266652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3266652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266652 prefixEnd_3266652 := by exact prefixLift 3266652
  have htrace : WordTrace (prefixWord ++ tailWord_3266652) baseStart_3266652 baseEnd_3266652 := by
    simpa [prefixWord, tailWord_3266652, baseEnd_3266652] using wordTrace_append hprefix tailTrace_3266652
  have hstable : (prefixWord ++ tailWord_3266652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266652).length < 2 ^ (prefixWord ++ tailWord_3266652).sum := by decide
  have hdescent : baseEnd_3266652 < baseStart_3266652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266669 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3266669 : Nat := 118140960795 + 3266669 * 2 ^ 59
def prefixEnd_3266669 : Nat := 4983230072969 + 3 ^ 40 * 3266669 * 2
def baseEnd_3266669 : Nat := 1677371336142184876214369

theorem tailTrace_3266669 : CollatzResearch.WordTrace tailWord_3266669 prefixEnd_3266669 1677371336142184876214369 := by
  unfold tailWord_3266669
  simp only [CollatzResearch.WordTrace]
  refine ⟨119145206602423590493411061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79430137734949060328940707 119145206602423590493411061)
  ·
    refine ⟨11169863118977211608757287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119145206602423590493411061 11169863118977211608757287)
    ·
      refine ⟨16754794678465817413135931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11169863118977211608757287 16754794678465817413135931)
      ·
        refine ⟨25132192017698726119703897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16754794678465817413135931 25132192017698726119703897)
        ·
          refine ⟨18849144013274044589777923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25132192017698726119703897 18849144013274044589777923)
          ·
            refine ⟨28273716019911066884666885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18849144013274044589777923 28273716019911066884666885)
            ·
              refine ⟨5301321753733325040875041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28273716019911066884666885 5301321753733325040875041)
              ·
                refine ⟨3975991315299993780656281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5301321753733325040875041 3975991315299993780656281)
                ·
                  refine ⟨2981993486474995335492211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3975991315299993780656281 2981993486474995335492211)
                  ·
                    refine ⟨4472990229712493003238317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2981993486474995335492211 4472990229712493003238317)
                    ·
                      refine ⟨1677371336142184876214369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4472990229712493003238317 1677371336142184876214369)
                      ·
                        rfl

theorem cell23_3266669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3266669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266669 prefixEnd_3266669 := by exact prefixLift 3266669
  have htrace : WordTrace (prefixWord ++ tailWord_3266669) baseStart_3266669 baseEnd_3266669 := by
    simpa [prefixWord, tailWord_3266669, baseEnd_3266669] using wordTrace_append hprefix tailTrace_3266669
  have hstable : (prefixWord ++ tailWord_3266669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266669).length < 2 ^ (prefixWord ++ tailWord_3266669).sum := by decide
  have hdescent : baseEnd_3266669 < baseStart_3266669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266685 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_3266685 : Nat := 118140960795 + 3266685 * 2 ^ 59
def prefixEnd_3266685 : Nat := 4983230072969 + 3 ^ 40 * 3266685 * 2
def baseEnd_3266685 : Nat := 559126517277552271204765

theorem tailTrace_3266685 : CollatzResearch.WordTrace tailWord_3266685 prefixEnd_3266685 559126517277552271204765 := by
  unfold tailWord_3266685
  simp only [CollatzResearch.WordTrace]
  refine ⟨119145790170365625225993509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79430526780243750150662339 119145790170365625225993509)
  ·
    refine ⟨22339835656943554729873783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119145790170365625225993509 22339835656943554729873783)
    ·
      refine ⟨33509753485415332094810675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22339835656943554729873783 33509753485415332094810675)
      ·
        refine ⟨50264630228122998142216013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33509753485415332094810675 50264630228122998142216013)
        ·
          refine ⟨18849236335546124303331005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50264630228122998142216013 18849236335546124303331005)
          ·
            refine ⟨7068463625829796613749127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18849236335546124303331005 7068463625829796613749127)
            ·
              refine ⟨10602695438744694920623691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068463625829796613749127 10602695438744694920623691)
              ·
                refine ⟨15904043158117042380935537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10602695438744694920623691 15904043158117042380935537)
                ·
                  refine ⟨11928032368587781785701653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904043158117042380935537 11928032368587781785701653)
                  ·
                    refine ⟨559126517277552271204765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11928032368587781785701653 559126517277552271204765)
                    ·
                      rfl

theorem cell23_3266685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_3266685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266685 prefixEnd_3266685 := by exact prefixLift 3266685
  have htrace : WordTrace (prefixWord ++ tailWord_3266685) baseStart_3266685 baseEnd_3266685 := by
    simpa [prefixWord, tailWord_3266685, baseEnd_3266685] using wordTrace_append hprefix tailTrace_3266685
  have hstable : (prefixWord ++ tailWord_3266685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266685).length < 2 ^ (prefixWord ++ tailWord_3266685).sum := by decide
  have hdescent : baseEnd_3266685 < baseStart_3266685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266722 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3266722 : Nat := 118140960795 + 3266722 * 2 ^ 59
def prefixEnd_3266722 : Nat := 4983230072969 + 3 ^ 40 * 3266722 * 2
def baseEnd_3266722 : Nat := 1677398550616873168851625

theorem tailTrace_3266722 : CollatzResearch.WordTrace tailWord_3266722 prefixEnd_3266722 1677398550616873168851625 := by
  unfold tailWord_3266722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29786784917807895136272605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79431426447487720363393613 29786784917807895136272605)
  ·
    refine ⟨11170044344177960676102227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29786784917807895136272605 11170044344177960676102227)
    ·
      refine ⟨16755066516266941014153341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11170044344177960676102227 16755066516266941014153341)
      ·
        refine ⟨6283149943600102880307503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16755066516266941014153341 6283149943600102880307503)
        ·
          refine ⟨9424724915400154320461255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283149943600102880307503 9424724915400154320461255)
          ·
            refine ⟨14137087373100231480691883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424724915400154320461255 14137087373100231480691883)
            ·
              refine ⟨21205631059650347221037825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14137087373100231480691883 21205631059650347221037825)
              ·
                refine ⟨15904223294737760415778369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21205631059650347221037825 15904223294737760415778369)
                ·
                  refine ⟨11928167471053320311833777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904223294737760415778369 11928167471053320311833777)
                  ·
                    refine ⟨8946125603289990233875333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11928167471053320311833777 8946125603289990233875333)
                    ·
                      refine ⟨1677398550616873168851625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8946125603289990233875333 1677398550616873168851625)
                      ·
                        rfl

theorem cell23_3266722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3266722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266722 prefixEnd_3266722 := by exact prefixLift 3266722
  have htrace : WordTrace (prefixWord ++ tailWord_3266722) baseStart_3266722 baseEnd_3266722 := by
    simpa [prefixWord, tailWord_3266722, baseEnd_3266722] using wordTrace_append hprefix tailTrace_3266722
  have hstable : (prefixWord ++ tailWord_3266722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266722).length < 2 ^ (prefixWord ++ tailWord_3266722).sum := by decide
  have hdescent : baseEnd_3266722 < baseStart_3266722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266725 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_3266725 : Nat := 118140960795 + 3266725 * 2 ^ 59
def prefixEnd_3266725 : Nat := 4983230072969 + 3 ^ 40 * 3266725 * 2
def baseEnd_3266725 : Nat := 1677400091058836657114111

theorem tailTrace_3266725 : CollatzResearch.WordTrace tailWord_3266725 prefixEnd_3266725 1677400091058836657114111 := by
  unfold tailWord_3266725
  simp only [CollatzResearch.WordTrace]
  refine ⟨119147249090220712057449629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79431499393480474704966419 119147249090220712057449629)
  ·
    refine ⟨44680218408832767021543611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119147249090220712057449629 44680218408832767021543611)
    ·
      refine ⟨67020327613249150532315417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44680218408832767021543611 67020327613249150532315417)
      ·
        refine ⟨50265245709936862899236563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67020327613249150532315417 50265245709936862899236563)
        ·
          refine ⟨75397868564905294348854845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50265245709936862899236563 75397868564905294348854845)
          ·
            refine ⟨28274200711839485380820567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75397868564905294348854845 28274200711839485380820567)
            ·
              refine ⟨42411301067759228071230851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28274200711839485380820567 42411301067759228071230851)
              ·
                refine ⟨63616951601638842106846277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42411301067759228071230851 63616951601638842106846277)
                ·
                  refine ⟨11928178425307282895033677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63616951601638842106846277 11928178425307282895033677)
                  ·
                    refine ⟨4473066909490231085637629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11928178425307282895033677 4473066909490231085637629)
                    ·
                      refine ⟨1677400091058836657114111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473066909490231085637629 1677400091058836657114111)
                      ·
                        rfl

theorem cell23_3266725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_3266725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266725 prefixEnd_3266725 := by exact prefixLift 3266725
  have htrace : WordTrace (prefixWord ++ tailWord_3266725) baseStart_3266725 baseEnd_3266725 := by
    simpa [prefixWord, tailWord_3266725, baseEnd_3266725] using wordTrace_append hprefix tailTrace_3266725
  have hstable : (prefixWord ++ tailWord_3266725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266725).length < 2 ^ (prefixWord ++ tailWord_3266725).sum := by decide
  have hdescent : baseEnd_3266725 < baseStart_3266725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266852 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_3266852 : Nat := 118140960795 + 3266852 * 2 ^ 59
def prefixEnd_3266852 : Nat := 4983230072969 + 3 ^ 40 * 3266852 * 2
def baseEnd_3266852 : Nat := 559155101033985886742009

theorem tailTrace_3266852 : CollatzResearch.WordTrace tailWord_3266852 prefixEnd_3266852 559155101033985886742009 := by
  unfold tailWord_3266852
  simp only [CollatzResearch.WordTrace]
  refine ⟨59575940580380306373661405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79434587440507075164881873 59575940580380306373661405)
  ·
    refine ⟨22340977717642614890123027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59575940580380306373661405 22340977717642614890123027)
    ·
      refine ⟨33511466576463922335184541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22340977717642614890123027 33511466576463922335184541)
      ·
        refine ⟨12566799966173970875694203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33511466576463922335184541 12566799966173970875694203)
        ·
          refine ⟨18850199949260956313541305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12566799966173970875694203 18850199949260956313541305)
          ·
            refine ⟨14137649961945717235155979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18850199949260956313541305 14137649961945717235155979)
            ·
              refine ⟨21206474942918575852733969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14137649961945717235155979 21206474942918575852733969)
              ·
                refine ⟨15904856207188931889550477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21206474942918575852733969 15904856207188931889550477)
                ·
                  refine ⟨5964321077695849458581429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15904856207188931889550477 5964321077695849458581429)
                  ·
                    refine ⟨559155101033985886742009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5964321077695849458581429 559155101033985886742009)
                    ·
                      rfl

theorem cell23_3266852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_3266852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266852 prefixEnd_3266852 := by exact prefixLift 3266852
  have htrace : WordTrace (prefixWord ++ tailWord_3266852) baseStart_3266852 baseEnd_3266852 := by
    simpa [prefixWord, tailWord_3266852, baseEnd_3266852] using wordTrace_append hprefix tailTrace_3266852
  have hstable : (prefixWord ++ tailWord_3266852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266852).length < 2 ^ (prefixWord ++ tailWord_3266852).sum := by decide
  have hdescent : baseEnd_3266852 < baseStart_3266852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266866 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3266866 : Nat := 118140960795 + 3266866 * 2 ^ 59
def prefixEnd_3266866 : Nat := 4983230072969 + 3 ^ 40 * 3266866 * 2
def baseEnd_3266866 : Nat := 1677472491831120605450963

theorem tailTrace_3266866 : CollatzResearch.WordTrace tailWord_3266866 prefixEnd_3266866 1677472491831120605450963 := by
  unfold tailWord_3266866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788097945677473284583113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79434927855139928758888301 29788097945677473284583113)
  ·
    refine ⟨22341073459258104963437335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29788097945677473284583113 22341073459258104963437335)
    ·
      refine ⟨33511610188887157445156003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22341073459258104963437335 33511610188887157445156003)
      ·
        refine ⟨50267415283330736167734005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33511610188887157445156003 50267415283330736167734005)
        ·
          refine ⟨4712570182812256515725063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50267415283330736167734005 4712570182812256515725063)
          ·
            refine ⟨7068855274218384773587595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712570182812256515725063 7068855274218384773587595)
            ·
              refine ⟨10603282911327577160381393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068855274218384773587595 10603282911327577160381393)
              ·
                refine ⟨7952462183495682870286045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10603282911327577160381393 7952462183495682870286045)
                ·
                  refine ⟨2982173318810881076357267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7952462183495682870286045 2982173318810881076357267)
                  ·
                    refine ⟨4473259978216321614535901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982173318810881076357267 4473259978216321614535901)
                    ·
                      refine ⟨1677472491831120605450963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473259978216321614535901 1677472491831120605450963)
                      ·
                        rfl

theorem cell23_3266866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3266866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266866 prefixEnd_3266866 := by exact prefixLift 3266866
  have htrace : WordTrace (prefixWord ++ tailWord_3266866) baseStart_3266866 baseEnd_3266866 := by
    simpa [prefixWord, tailWord_3266866, baseEnd_3266866] using wordTrace_append hprefix tailTrace_3266866
  have hstable : (prefixWord ++ tailWord_3266866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266866).length < 2 ^ (prefixWord ++ tailWord_3266866).sum := by decide
  have hdescent : baseEnd_3266866 < baseStart_3266866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266872 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3266872 : Nat := 118140960795 + 3266872 * 2 ^ 59
def prefixEnd_3266872 : Nat := 4983230072969 + 3 ^ 40 * 3266872 * 2
def baseEnd_3266872 : Nat := 1677475572715047581975935

theorem tailTrace_3266872 : CollatzResearch.WordTrace tailWord_3266872 prefixEnd_3266872 1677475572715047581975935 := by
  unfold tailWord_3266872
  simp only [CollatzResearch.WordTrace]
  refine ⟨59576305310344078081525435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79435073747125437442033913 59576305310344078081525435)
  ·
    refine ⟨89364457965516117122288153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59576305310344078081525435 89364457965516117122288153)
    ·
      refine ⟨67023343474137087841716115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89364457965516117122288153 67023343474137087841716115)
      ·
        refine ⟨100535015211205631762574173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67023343474137087841716115 100535015211205631762574173)
        ·
          refine ⟨37700630704202111910965315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100535015211205631762574173 37700630704202111910965315)
          ·
            refine ⟨56550946056303167866447973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37700630704202111910965315 56550946056303167866447973)
            ·
              refine ⟨10603302385556843974958995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56550946056303167866447973 10603302385556843974958995)
              ·
                refine ⟨15904953578335265962438493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603302385556843974958995 15904953578335265962438493)
                ·
                  refine ⟨5964357591875724735914435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15904953578335265962438493 5964357591875724735914435)
                  ·
                    refine ⟨8946536387813587103871653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5964357591875724735914435 8946536387813587103871653)
                    ·
                      refine ⟨1677475572715047581975935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8946536387813587103871653 1677475572715047581975935)
                      ·
                        rfl

theorem cell23_3266872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3266872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266872 prefixEnd_3266872 := by exact prefixLift 3266872
  have htrace : WordTrace (prefixWord ++ tailWord_3266872) baseStart_3266872 baseEnd_3266872 := by
    simpa [prefixWord, tailWord_3266872, baseEnd_3266872] using wordTrace_append hprefix tailTrace_3266872
  have hstable : (prefixWord ++ tailWord_3266872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266872).length < 2 ^ (prefixWord ++ tailWord_3266872).sum := by decide
  have hdescent : baseEnd_3266872 < baseStart_3266872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266885 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_3266885 : Nat := 118140960795 + 3266885 * 2 ^ 59
def prefixEnd_3266885 : Nat := 4983230072969 + 3 ^ 40 * 3266885 * 2
def baseEnd_3266885 : Nat := 1677482247963556031113375

theorem tailTrace_3266885 : CollatzResearch.WordTrace tailWord_3266885 prefixEnd_3266885 1677482247963556031113375 := by
  unfold tailWord_3266885
  simp only [CollatzResearch.WordTrace]
  refine ⟨119153084769641059383274109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79435389846427372922182739 119153084769641059383274109)
  ·
    refine ⟨44682406788615397268727791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119153084769641059383274109 44682406788615397268727791)
    ·
      refine ⟨67023610182923095903091687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44682406788615397268727791 67023610182923095903091687)
      ·
        refine ⟨100535415274384643854637531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67023610182923095903091687 100535415274384643854637531)
        ·
          refine ⟨150803122911576965781956297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100535415274384643854637531 150803122911576965781956297)
          ·
            refine ⟨113102342183682724336467223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150803122911576965781956297 113102342183682724336467223)
            ·
              refine ⟨169653513275524086504700835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113102342183682724336467223 169653513275524086504700835)
              ·
                refine ⟨254480269913286129757051253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169653513275524086504700835 254480269913286129757051253)
                ·
                  refine ⟨23857525304370574664723555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254480269913286129757051253 23857525304370574664723555)
                  ·
                    refine ⟨35786287956555861997085333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23857525304370574664723555 35786287956555861997085333)
                    ·
                      refine ⟨1677482247963556031113375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35786287956555861997085333 1677482247963556031113375)
                      ·
                        rfl

theorem cell23_3266885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_3266885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266885 prefixEnd_3266885 := by exact prefixLift 3266885
  have htrace : WordTrace (prefixWord ++ tailWord_3266885) baseStart_3266885 baseEnd_3266885 := by
    simpa [prefixWord, tailWord_3266885, baseEnd_3266885] using wordTrace_append hprefix tailTrace_3266885
  have hstable : (prefixWord ++ tailWord_3266885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266885).length < 2 ^ (prefixWord ++ tailWord_3266885).sum := by decide
  have hdescent : baseEnd_3266885 < baseStart_3266885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266889 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 7, 2, 2]
def baseStart_3266889 : Nat := 118140960795 + 3266889 * 2 ^ 59
def prefixEnd_3266889 : Nat := 4983230072969 + 3 ^ 40 * 3266889 * 2
def baseEnd_3266889 : Nat := 1677484301886174015463357

theorem tailTrace_3266889 : CollatzResearch.WordTrace tailWord_3266889 prefixEnd_3266889 1677484301886174015463357 := by
  unfold tailWord_3266889
  simp only [CollatzResearch.WordTrace]
  refine ⟨119153230661626568066419721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79435487107751045377613147 119153230661626568066419721)
  ·
    refine ⟨89364922996219926049814791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119153230661626568066419721 89364922996219926049814791)
    ·
      refine ⟨134047384494329889074722187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89364922996219926049814791 134047384494329889074722187)
      ·
        refine ⟨201071076741494833612083281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134047384494329889074722187 201071076741494833612083281)
        ·
          refine ⟨150803307556121125209062461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201071076741494833612083281 150803307556121125209062461)
          ·
            refine ⟨56551240333545421953398423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150803307556121125209062461 56551240333545421953398423)
            ·
              refine ⟨84826860500318132930097635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56551240333545421953398423 84826860500318132930097635)
              ·
                refine ⟨127240290750477199395146453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84826860500318132930097635 127240290750477199395146453)
                ·
                  refine ⟨2982194314464309360823745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127240290750477199395146453 2982194314464309360823745)
                  ·
                    refine ⟨2236645735848232020617809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2982194314464309360823745 2236645735848232020617809)
                    ·
                      refine ⟨1677484301886174015463357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236645735848232020617809 1677484301886174015463357)
                      ·
                        rfl

theorem cell23_3266889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2, 2].length) (baseStart_3266889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266889 prefixEnd_3266889 := by exact prefixLift 3266889
  have htrace : WordTrace (prefixWord ++ tailWord_3266889) baseStart_3266889 baseEnd_3266889 := by
    simpa [prefixWord, tailWord_3266889, baseEnd_3266889] using wordTrace_append hprefix tailTrace_3266889
  have hstable : (prefixWord ++ tailWord_3266889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266889).length < 2 ^ (prefixWord ++ tailWord_3266889).sum := by decide
  have hdescent : baseEnd_3266889 < baseStart_3266889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266892 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3266892 : Nat := 118140960795 + 3266892 * 2 ^ 59
def prefixEnd_3266892 : Nat := 4983230072969 + 3 ^ 40 * 3266892 * 2
def baseEnd_3266892 : Nat := 1677485842328137503725843

theorem tailTrace_3266892 : CollatzResearch.WordTrace tailWord_3266892 prefixEnd_3266892 1677485842328137503725843 := by
  unfold tailWord_3266892
  simp only [CollatzResearch.WordTrace]
  refine ⟨59576670040307849789389465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79435560053743799719185953 59576670040307849789389465)
  ·
    refine ⟨44682502530230887342042099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59576670040307849789389465 44682502530230887342042099)
    ·
      refine ⟨67023753795346331013063149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44682502530230887342042099 67023753795346331013063149)
      ·
        refine ⟨25133907673254874129898681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67023753795346331013063149 25133907673254874129898681)
        ·
          refine ⟨18850430754941155597424011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25133907673254874129898681 18850430754941155597424011)
          ·
            refine ⟨28275646132411733396136017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18850430754941155597424011 28275646132411733396136017)
            ·
              refine ⟨21206734599308800047102013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28275646132411733396136017 21206734599308800047102013)
              ·
                refine ⟨7952525474740800017663255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21206734599308800047102013 7952525474740800017663255)
                ·
                  refine ⟨11928788212111200026494883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952525474740800017663255 11928788212111200026494883)
                  ·
                    refine ⟨17893182318166800039742325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11928788212111200026494883 17893182318166800039742325)
                    ·
                      refine ⟨1677485842328137503725843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17893182318166800039742325 1677485842328137503725843)
                      ·
                        rfl

theorem cell23_3266892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3266892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266892 prefixEnd_3266892 := by exact prefixLift 3266892
  have htrace : WordTrace (prefixWord ++ tailWord_3266892) baseStart_3266892 baseEnd_3266892 := by
    simpa [prefixWord, tailWord_3266892, baseEnd_3266892] using wordTrace_append hprefix tailTrace_3266892
  have hstable : (prefixWord ++ tailWord_3266892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266892).length < 2 ^ (prefixWord ++ tailWord_3266892).sum := by decide
  have hdescent : baseEnd_3266892 < baseStart_3266892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266905 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3266905 : Nat := 118140960795 + 3266905 * 2 ^ 59
def prefixEnd_3266905 : Nat := 4983230072969 + 3 ^ 40 * 3266905 * 2
def baseEnd_3266905 : Nat := 1677492517576645952863283

theorem tailTrace_3266905 : CollatzResearch.WordTrace tailWord_3266905 prefixEnd_3266905 1677492517576645952863283 := by
  unfold tailWord_3266905
  simp only [CollatzResearch.WordTrace]
  refine ⟨119153814229568602799002169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79435876153045735199334779 119153814229568602799002169)
  ·
    refine ⟨89365360672176452099251627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119153814229568602799002169 89365360672176452099251627)
    ·
      refine ⟨134048041008264678148877441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89365360672176452099251627 134048041008264678148877441)
      ·
        refine ⟨100536030756198508611658081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134048041008264678148877441 100536030756198508611658081)
        ·
          refine ⟨75402023067148881458743561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100536030756198508611658081 75402023067148881458743561)
          ·
            refine ⟨56551517300361661094057671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75402023067148881458743561 56551517300361661094057671)
            ·
              refine ⟨84827275950542491641086507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56551517300361661094057671 84827275950542491641086507)
              ·
                refine ⟨127240913925813737461629761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84827275950542491641086507 127240913925813737461629761)
                ·
                  refine ⟨95430685444360303096222321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127240913925813737461629761 95430685444360303096222321)
                  ·
                    refine ⟨71573014083270227322166741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95430685444360303096222321 71573014083270227322166741)
                    ·
                      refine ⟨1677492517576645952863283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71573014083270227322166741 1677492517576645952863283)
                      ·
                        rfl

theorem cell23_3266905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3266905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266905 prefixEnd_3266905 := by exact prefixLift 3266905
  have htrace : WordTrace (prefixWord ++ tailWord_3266905) baseStart_3266905 baseEnd_3266905 := by
    simpa [prefixWord, tailWord_3266905, baseEnd_3266905] using wordTrace_append hprefix tailTrace_3266905
  have hstable : (prefixWord ++ tailWord_3266905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266905).length < 2 ^ (prefixWord ++ tailWord_3266905).sum := by decide
  have hdescent : baseEnd_3266905 < baseStart_3266905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266916 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_3266916 : Nat := 118140960795 + 3266916 * 2 ^ 59
def prefixEnd_3266916 : Nat := 4983230072969 + 3 ^ 40 * 3266916 * 2
def baseEnd_3266916 : Nat := 559166055287948469941911

theorem tailTrace_3266916 : CollatzResearch.WordTrace tailWord_3266916 prefixEnd_3266916 559166055287948469941911 := by
  unfold tailWord_3266916
  simp only [CollatzResearch.WordTrace]
  refine ⟨59577107716264375838826301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79436143621685834451768401 59577107716264375838826301)
  ·
    refine ⟨22341415393599140939559863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59577107716264375838826301 22341415393599140939559863)
    ·
      refine ⟨33512123090398711409339795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22341415393599140939559863 33512123090398711409339795)
      ·
        refine ⟨50268184635598067114009693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33512123090398711409339795 50268184635598067114009693)
        ·
          refine ⟨18850569238349275167753635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50268184635598067114009693 18850569238349275167753635)
          ·
            refine ⟨28275853857523912751630453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18850569238349275167753635 28275853857523912751630453)
            ·
              refine ⟨2650861299142866820465355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28275853857523912751630453 2650861299142866820465355)
              ·
                refine ⟨3976291948714300230698033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650861299142866820465355 3976291948714300230698033)
                ·
                  refine ⟨2982218961535725173023525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976291948714300230698033 2982218961535725173023525)
                  ·
                    refine ⟨559166055287948469941911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982218961535725173023525 559166055287948469941911)
                    ·
                      rfl

theorem cell23_3266916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_3266916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266916 prefixEnd_3266916 := by exact prefixLift 3266916
  have htrace : WordTrace (prefixWord ++ tailWord_3266916) baseStart_3266916 baseEnd_3266916 := by
    simpa [prefixWord, tailWord_3266916, baseEnd_3266916] using wordTrace_append hprefix tailTrace_3266916
  have hstable : (prefixWord ++ tailWord_3266916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266916).length < 2 ^ (prefixWord ++ tailWord_3266916).sum := by decide
  have hdescent : baseEnd_3266916 < baseStart_3266916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266919 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3266919 : Nat := 118140960795 + 3266919 * 2 ^ 59
def prefixEnd_3266919 : Nat := 4983230072969 + 3 ^ 40 * 3266919 * 2
def baseEnd_3266919 : Nat := 1677499706305808898088219

theorem tailTrace_3266919 : CollatzResearch.WordTrace tailWord_3266919 prefixEnd_3266919 1677499706305808898088219 := by
  unfold tailWord_3266919
  simp only [CollatzResearch.WordTrace]
  refine ⟨119154324851517883190011811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79436216567678588793341207 119154324851517883190011811)
  ·
    refine ⟨178731487277276824785017717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119154324851517883190011811 178731487277276824785017717)
    ·
      refine ⟨16756076932244702323595411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178731487277276824785017717 16756076932244702323595411)
      ·
        refine ⟨25134115398367053485393117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16756076932244702323595411 25134115398367053485393117)
        ·
          refine ⟨9425293274387645057022419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25134115398367053485393117 9425293274387645057022419)
          ·
            refine ⟨14137939911581467585533629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425293274387645057022419 14137939911581467585533629)
            ·
              refine ⟨5301727466843050344575111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14137939911581467585533629 5301727466843050344575111)
              ·
                refine ⟨7952591200264575516862667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301727466843050344575111 7952591200264575516862667)
                ·
                  refine ⟨11928886800396863275294001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952591200264575516862667 11928886800396863275294001)
                  ·
                    refine ⟨8946665100297647456470501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11928886800396863275294001 8946665100297647456470501)
                    ·
                      refine ⟨1677499706305808898088219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8946665100297647456470501 1677499706305808898088219)
                      ·
                        rfl

theorem cell23_3266919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3266919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266919 prefixEnd_3266919 := by exact prefixLift 3266919
  have htrace : WordTrace (prefixWord ++ tailWord_3266919) baseStart_3266919 baseEnd_3266919 := by
    simpa [prefixWord, tailWord_3266919, baseEnd_3266919] using wordTrace_append hprefix tailTrace_3266919
  have hstable : (prefixWord ++ tailWord_3266919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266919).length < 2 ^ (prefixWord ++ tailWord_3266919).sum := by decide
  have hdescent : baseEnd_3266919 < baseStart_3266919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266934 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3266934 : Nat := 118140960795 + 3266934 * 2 ^ 59
def prefixEnd_3266934 : Nat := 4983230072969 + 3 ^ 40 * 3266934 * 2
def baseEnd_3266934 : Nat := 1677507408515626339400651

theorem tailTrace_3266934 : CollatzResearch.WordTrace tailWord_3266934 prefixEnd_3266934 1677507408515626339400651 := by
  unfold tailWord_3266934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447179496653971296987991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79436581297642360501205237 7447179496653971296987991)
  ·
    refine ⟨11170769244980956945481987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447179496653971296987991 11170769244980956945481987)
    ·
      refine ⟨16756153867471435418222981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11170769244980956945481987 16756153867471435418222981)
      ·
        refine ⟨3141778850150894140916809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16756153867471435418222981 3141778850150894140916809)
        ·
          refine ⟨2356334137613170605687607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3141778850150894140916809 2356334137613170605687607)
          ·
            refine ⟨3534501206419755908531411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356334137613170605687607 3534501206419755908531411)
            ·
              refine ⟨5301751809629633862797117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534501206419755908531411 5301751809629633862797117)
              ·
                refine ⟨1988156928611112698548919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301751809629633862797117 1988156928611112698548919)
                ·
                  refine ⟨2982235392916669047823379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988156928611112698548919 2982235392916669047823379)
                  ·
                    refine ⟨4473353089375003571735069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982235392916669047823379 4473353089375003571735069)
                    ·
                      refine ⟨1677507408515626339400651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473353089375003571735069 1677507408515626339400651)
                      ·
                        rfl

theorem cell23_3266934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3266934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266934 prefixEnd_3266934 := by exact prefixLift 3266934
  have htrace : WordTrace (prefixWord ++ tailWord_3266934) baseStart_3266934 baseEnd_3266934 := by
    simpa [prefixWord, tailWord_3266934, baseEnd_3266934] using wordTrace_append hprefix tailTrace_3266934
  have hstable : (prefixWord ++ tailWord_3266934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266934).length < 2 ^ (prefixWord ++ tailWord_3266934).sum := by decide
  have hdescent : baseEnd_3266934 < baseStart_3266934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266939 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 3]
def baseStart_3266939 : Nat := 118140960795 + 3266939 * 2 ^ 59
def prefixEnd_3266939 : Nat := 4983230072969 + 3 ^ 40 * 3266939 * 2
def baseEnd_3266939 : Nat := 1677509975918898819838127

theorem tailTrace_3266939 : CollatzResearch.WordTrace tailWord_3266939 prefixEnd_3266939 1677509975918898819838127 := by
  unfold tailWord_3266939
  simp only [CollatzResearch.WordTrace]
  refine ⟨119155054311445426605739871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79436702874296951070493247 119155054311445426605739871)
  ·
    refine ⟨178732581467168139908609807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119155054311445426605739871 178732581467168139908609807)
    ·
      refine ⟨268098872200752209862914711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178732581467168139908609807 268098872200752209862914711)
      ·
        refine ⟨402148308301128314794372067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268098872200752209862914711 402148308301128314794372067)
        ·
          refine ⟨603222462451692472191558101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402148308301128314794372067 603222462451692472191558101)
          ·
            refine ⟨14138026463711542316989643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 603222462451692472191558101 14138026463711542316989643)
            ·
              refine ⟨21207039695567313475484465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14138026463711542316989643 21207039695567313475484465)
              ·
                refine ⟨15905279771675485106613349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21207039695567313475484465 15905279771675485106613349)
                ·
                  refine ⟨2982239957189153457490003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15905279771675485106613349 2982239957189153457490003)
                  ·
                    refine ⟨4473359935783730186235005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982239957189153457490003 4473359935783730186235005)
                    ·
                      refine ⟨1677509975918898819838127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473359935783730186235005 1677509975918898819838127)
                      ·
                        rfl

theorem cell23_3266939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 3].length) (baseStart_3266939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266939 prefixEnd_3266939 := by exact prefixLift 3266939
  have htrace : WordTrace (prefixWord ++ tailWord_3266939) baseStart_3266939 baseEnd_3266939 := by
    simpa [prefixWord, tailWord_3266939, baseEnd_3266939] using wordTrace_append hprefix tailTrace_3266939
  have hstable : (prefixWord ++ tailWord_3266939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266939).length < 2 ^ (prefixWord ++ tailWord_3266939).sum := by decide
  have hdescent : baseEnd_3266939 < baseStart_3266939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266946 : List Nat := [3, 4, 2, 1, 2, 2, 9]
def baseStart_3266946 : Nat := 118140960795 + 3266946 * 2 ^ 59
def prefixEnd_3266946 : Nat := 4983230072969 + 3 ^ 40 * 3266946 * 2
def baseEnd_3266946 : Nat := 20710044077573830770995

theorem tailTrace_3266946 : CollatzResearch.WordTrace tailWord_3266946 prefixEnd_3266946 20710044077573830770995 := by
  unfold tailWord_3266946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788827405605016700311173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79436873081613377867496461 29788827405605016700311173)
  ·
    refine ⟨5585405138550940631308345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29788827405605016700311173 5585405138550940631308345)
    ·
      refine ⟨4189053853913205473481259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5585405138550940631308345 4189053853913205473481259)
      ·
        refine ⟨6283580780869808210221889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189053853913205473481259 6283580780869808210221889)
        ·
          refine ⟨4712685585652356157666417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6283580780869808210221889 4712685585652356157666417)
          ·
            refine ⟨3534514189239267118249813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712685585652356157666417 3534514189239267118249813)
            ·
              refine ⟨20710044077573830770995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3534514189239267118249813 20710044077573830770995)
              ·
                rfl

theorem cell23_3266946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 9].length) (baseStart_3266946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266946 prefixEnd_3266946 := by exact prefixLift 3266946
  have htrace : WordTrace (prefixWord ++ tailWord_3266946) baseStart_3266946 baseEnd_3266946 := by
    simpa [prefixWord, tailWord_3266946, baseEnd_3266946] using wordTrace_append hprefix tailTrace_3266946
  have hstable : (prefixWord ++ tailWord_3266946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266946).length < 2 ^ (prefixWord ++ tailWord_3266946).sum := by decide
  have hdescent : baseEnd_3266946 < baseStart_3266946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266949 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_3266949 : Nat := 118140960795 + 3266949 * 2 ^ 59
def prefixEnd_3266949 : Nat := 4983230072969 + 3 ^ 40 * 3266949 * 2
def baseEnd_3266949 : Nat := 1677515110725443780713081

theorem tailTrace_3266949 : CollatzResearch.WordTrace tailWord_3266949 prefixEnd_3266949 1677515110725443780713081 := by
  unfold tailWord_3266949
  simp only [CollatzResearch.WordTrace]
  refine ⟨119155419041409198313603901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79436946027606132209069267 119155419041409198313603901)
  ·
    refine ⟨44683282140528449367601463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119155419041409198313603901 44683282140528449367601463)
    ·
      refine ⟨67024923210792674051402195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44683282140528449367601463 67024923210792674051402195)
      ·
        refine ⟨100537384816189011077103293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67024923210792674051402195 100537384816189011077103293)
        ·
          refine ⟨37701519306070879153913735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100537384816189011077103293 37701519306070879153913735)
          ·
            refine ⟨56552278959106318730870603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37701519306070879153913735 56552278959106318730870603)
            ·
              refine ⟨84828418438659478096305905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56552278959106318730870603 84828418438659478096305905)
              ·
                refine ⟨63621313828994608572229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84828418438659478096305905 63621313828994608572229429)
                ·
                  refine ⟨5964498171468244553646509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63621313828994608572229429 5964498171468244553646509)
                  ·
                    refine ⟨2236686814300591707617441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5964498171468244553646509 2236686814300591707617441)
                    ·
                      refine ⟨1677515110725443780713081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236686814300591707617441 1677515110725443780713081)
                      ·
                        rfl

theorem cell23_3266949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_3266949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266949 prefixEnd_3266949 := by exact prefixLift 3266949
  have htrace : WordTrace (prefixWord ++ tailWord_3266949) baseStart_3266949 baseEnd_3266949 := by
    simpa [prefixWord, tailWord_3266949, baseEnd_3266949] using wordTrace_append hprefix tailTrace_3266949
  have hstable : (prefixWord ++ tailWord_3266949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266949).length < 2 ^ (prefixWord ++ tailWord_3266949).sum := by decide
  have hdescent : baseEnd_3266949 < baseStart_3266949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266952 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3266952 : Nat := 118140960795 + 3266952 * 2 ^ 59
def prefixEnd_3266952 : Nat := 4983230072969 + 3 ^ 40 * 3266952 * 2
def baseEnd_3266952 : Nat := 1677516651167407268975567

theorem tailTrace_3266952 : CollatzResearch.WordTrace tailWord_3266952 prefixEnd_3266952 1677516651167407268975567 := by
  unfold tailWord_3266952
  simp only [CollatzResearch.WordTrace]
  refine ⟨59577764230199164912981555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79437018973598886550642073 59577764230199164912981555)
  ·
    refine ⟨89366646345298747369472333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59577764230199164912981555 89366646345298747369472333)
    ·
      refine ⟨33512492379487030263552125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89366646345298747369472333 33512492379487030263552125)
      ·
        refine ⟨12567184642307636348832047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33512492379487030263552125 12567184642307636348832047)
        ·
          refine ⟨18850776963461454523248071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567184642307636348832047 18850776963461454523248071)
          ·
            refine ⟨28276165445192181784872107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18850776963461454523248071 28276165445192181784872107)
            ·
              refine ⟨42414248167788272677308161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28276165445192181784872107 42414248167788272677308161)
              ·
                refine ⟨31810686125841204507981121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42414248167788272677308161 31810686125841204507981121)
                ·
                  refine ⟨23858014594380903380985841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31810686125841204507981121 23858014594380903380985841)
                  ·
                    refine ⟨17893510945785677535739381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23858014594380903380985841 17893510945785677535739381)
                    ·
                      refine ⟨1677516651167407268975567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17893510945785677535739381 1677516651167407268975567)
                      ·
                        rfl

theorem cell23_3266952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3266952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266952 prefixEnd_3266952 := by exact prefixLift 3266952
  have htrace : WordTrace (prefixWord ++ tailWord_3266952) baseStart_3266952 baseEnd_3266952 := by
    simpa [prefixWord, tailWord_3266952, baseEnd_3266952] using wordTrace_append hprefix tailTrace_3266952
  have hstable : (prefixWord ++ tailWord_3266952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266952).length < 2 ^ (prefixWord ++ tailWord_3266952).sum := by decide
  have hdescent : baseEnd_3266952 < baseStart_3266952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266973 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3266973 : Nat := 118140960795 + 3266973 * 2 ^ 59
def prefixEnd_3266973 : Nat := 4983230072969 + 3 ^ 40 * 3266973 * 2
def baseEnd_3266973 : Nat := 1677527434261151686812971

theorem tailTrace_3266973 : CollatzResearch.WordTrace tailWord_3266973 prefixEnd_3266973 1677527434261151686812971 := by
  unfold tailWord_3266973
  simp only [CollatzResearch.WordTrace]
  refine ⟨119156294393322250412477573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79437529595548166941651715 119156294393322250412477573)
  ·
    refine ⟨22341805198747921952339545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119156294393322250412477573 22341805198747921952339545)
    ·
      refine ⟨16756353899060941464254659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22341805198747921952339545 16756353899060941464254659)
      ·
        refine ⟨25134530848591412196381989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16756353899060941464254659 25134530848591412196381989)
        ·
          refine ⟨4712724534110889786821623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25134530848591412196381989 4712724534110889786821623)
          ·
            refine ⟨7069086801166334680232435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712724534110889786821623 7069086801166334680232435)
            ·
              refine ⟨10603630201749502020348653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069086801166334680232435 10603630201749502020348653)
              ·
                refine ⟨3976361325656063257630745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10603630201749502020348653 3976361325656063257630745)
                ·
                  refine ⟨2982270994242047443223059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976361325656063257630745 2982270994242047443223059)
                  ·
                    refine ⟨4473406491363071164834589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982270994242047443223059 4473406491363071164834589)
                    ·
                      refine ⟨1677527434261151686812971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473406491363071164834589 1677527434261151686812971)
                      ·
                        rfl

theorem cell23_3266973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3266973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266973 prefixEnd_3266973 := by exact prefixLift 3266973
  have htrace : WordTrace (prefixWord ++ tailWord_3266973) baseStart_3266973 baseEnd_3266973 := by
    simpa [prefixWord, tailWord_3266973, baseEnd_3266973] using wordTrace_append hprefix tailTrace_3266973
  have hstable : (prefixWord ++ tailWord_3266973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266973).length < 2 ^ (prefixWord ++ tailWord_3266973).sum := by decide
  have hdescent : baseEnd_3266973 < baseStart_3266973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266983 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_3266983 : Nat := 118140960795 + 3266983 * 2 ^ 59
def prefixEnd_3266983 : Nat := 4983230072969 + 3 ^ 40 * 3266983 * 2
def baseEnd_3266983 : Nat := 1677532569067696647687925

theorem tailTrace_3266983 : CollatzResearch.WordTrace tailWord_3266983 prefixEnd_3266983 1677532569067696647687925 := by
  unfold tailWord_3266983
  simp only [CollatzResearch.WordTrace]
  refine ⟨119156659123286022120341603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79437772748857348080227735 119156659123286022120341603)
  ·
    refine ⟨178734988684929033180512405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119156659123286022120341603 178734988684929033180512405)
    ·
      refine ⟨8378202594606048430336519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178734988684929033180512405 8378202594606048430336519)
      ·
        refine ⟨12567303891909072645504779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378202594606048430336519 12567303891909072645504779)
        ·
          refine ⟨18850955837863608968257169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567303891909072645504779 18850955837863608968257169)
          ·
            refine ⟨14138216878397706726192877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18850955837863608968257169 14138216878397706726192877)
            ·
              refine ⟨5301831329399140022322329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14138216878397706726192877 5301831329399140022322329)
              ·
                refine ⟨3976373497049355016741747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5301831329399140022322329 3976373497049355016741747)
                ·
                  refine ⟨5964560245574032525112621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976373497049355016741747 5964560245574032525112621)
                  ·
                    refine ⟨2236710092090262196917233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5964560245574032525112621 2236710092090262196917233)
                    ·
                      refine ⟨1677532569067696647687925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236710092090262196917233 1677532569067696647687925)
                      ·
                        rfl

theorem cell23_3266983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_3266983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3266983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3266983 prefixEnd_3266983 := by exact prefixLift 3266983
  have htrace : WordTrace (prefixWord ++ tailWord_3266983) baseStart_3266983 baseEnd_3266983 := by
    simpa [prefixWord, tailWord_3266983, baseEnd_3266983] using wordTrace_append hprefix tailTrace_3266983
  have hstable : (prefixWord ++ tailWord_3266983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266983).length < 2 ^ (prefixWord ++ tailWord_3266983).sum := by decide
  have hdescent : baseEnd_3266983 < baseStart_3266983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267022 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3267022 : Nat := 118140960795 + 3267022 * 2 ^ 59
def prefixEnd_3267022 : Nat := 4983230072969 + 3 ^ 40 * 3267022 * 2
def baseEnd_3267022 : Nat := 1677552594813221995100245

theorem tailTrace_3267022 : CollatzResearch.WordTrace tailWord_3267022 prefixEnd_3267022 1677552594813221995100245 := by
  unfold tailWord_3267022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14894760196268091472626415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79438721046763154520674213 14894760196268091472626415)
  ·
    refine ⟨22342140294402137208939623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14894760196268091472626415 22342140294402137208939623)
    ·
      refine ⟨33513210441603205813409435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22342140294402137208939623 33513210441603205813409435)
      ·
        refine ⟨50269815662404808720114153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33513210441603205813409435 50269815662404808720114153)
        ·
          refine ⟨37702361746803606540085615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50269815662404808720114153 37702361746803606540085615)
          ·
            refine ⟨56553542620205409810128423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37702361746803606540085615 56553542620205409810128423)
            ·
              refine ⟨84830313930308114715192635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56553542620205409810128423 84830313930308114715192635)
              ·
                refine ⟨127245470895462172072788953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84830313930308114715192635 127245470895462172072788953)
                ·
                  refine ⟨95434103171596629054591715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127245470895462172072788953 95434103171596629054591715)
                  ·
                    refine ⟨143151154757394943581887573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95434103171596629054591715 143151154757394943581887573)
                    ·
                      refine ⟨1677552594813221995100245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 143151154757394943581887573 1677552594813221995100245)
                      ·
                        rfl

theorem cell23_3267022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3267022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267022 prefixEnd_3267022 := by exact prefixLift 3267022
  have htrace : WordTrace (prefixWord ++ tailWord_3267022) baseStart_3267022 baseEnd_3267022 := by
    simpa [prefixWord, tailWord_3267022, baseEnd_3267022] using wordTrace_append hprefix tailTrace_3267022
  have hstable : (prefixWord ++ tailWord_3267022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267022).length < 2 ^ (prefixWord ++ tailWord_3267022).sum := by decide
  have hdescent : baseEnd_3267022 < baseStart_3267022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267029 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3267029 : Nat := 118140960795 + 3267029 * 2 ^ 59
def prefixEnd_3267029 : Nat := 4983230072969 + 3 ^ 40 * 3267029 * 2
def baseEnd_3267029 : Nat := 1677556189177803467712713

theorem tailTrace_3267029 : CollatzResearch.WordTrace tailWord_3267029 prefixEnd_3267029 1677556189177803467712713 := by
  unfold tailWord_3267029
  simp only [CollatzResearch.WordTrace]
  refine ⟨119158336881119371976516141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79438891254079581317677427 119158336881119371976516141)
  ·
    refine ⟨44684376330419764491193553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119158336881119371976516141 44684376330419764491193553)
    ·
      refine ⟨33513282247814823368395165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44684376330419764491193553 33513282247814823368395165)
      ·
        refine ⟨12567480842930558763148187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33513282247814823368395165 12567480842930558763148187)
        ·
          refine ⟨18851221264395838144722281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567480842930558763148187 18851221264395838144722281)
          ·
            refine ⟨14138415948296878608541711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18851221264395838144722281 14138415948296878608541711)
            ·
              refine ⟨21207623922445317912812567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14138415948296878608541711 21207623922445317912812567)
              ·
                refine ⟨31811435883667976869218851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21207623922445317912812567 31811435883667976869218851)
                ·
                  refine ⟨47717153825501965303828277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31811435883667976869218851 47717153825501965303828277)
                  ·
                    refine ⟨4473483171140809247233901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47717153825501965303828277 4473483171140809247233901)
                    ·
                      refine ⟨1677556189177803467712713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473483171140809247233901 1677556189177803467712713)
                      ·
                        rfl

theorem cell23_3267029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3267029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267029 prefixEnd_3267029 := by exact prefixLift 3267029
  have htrace : WordTrace (prefixWord ++ tailWord_3267029) baseStart_3267029 baseEnd_3267029 := by
    simpa [prefixWord, tailWord_3267029, baseEnd_3267029] using wordTrace_append hprefix tailTrace_3267029
  have hstable : (prefixWord ++ tailWord_3267029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267029).length < 2 ^ (prefixWord ++ tailWord_3267029).sum := by decide
  have hdescent : baseEnd_3267029 < baseStart_3267029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267030 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3267030 : Nat := 118140960795 + 3267030 * 2 ^ 59
def prefixEnd_3267030 : Nat := 4983230072969 + 3 ^ 40 * 3267030 * 2
def baseEnd_3267030 : Nat := 1677556702658457963800209

theorem tailTrace_3267030 : CollatzResearch.WordTrace tailWord_3267030 prefixEnd_3267030 1677556702658457963800209 := by
  unfold tailWord_3267030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447398334632234321706409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79438915569410499431535029 7447398334632234321706409)
  ·
    refine ⟨5585548750974175741279807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7447398334632234321706409 5585548750974175741279807)
    ·
      refine ⟨8378323126461263611919711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585548750974175741279807 8378323126461263611919711)
      ·
        refine ⟨12567484689691895417879567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378323126461263611919711 12567484689691895417879567)
        ·
          refine ⟨18851227034537843126819351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567484689691895417879567 18851227034537843126819351)
          ·
            refine ⟨28276840551806764690229027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18851227034537843126819351 28276840551806764690229027)
            ·
              refine ⟨42415260827710147035343541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28276840551806764690229027 42415260827710147035343541)
              ·
                refine ⟨3976430702597826284563457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42415260827710147035343541 3976430702597826284563457)
                ·
                  refine ⟨2982323026948369713422593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976430702597826284563457 2982323026948369713422593)
                  ·
                    refine ⟨2236742270211277285066945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2982323026948369713422593 2236742270211277285066945)
                    ·
                      refine ⟨1677556702658457963800209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236742270211277285066945 1677556702658457963800209)
                      ·
                        rfl

theorem cell23_3267030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3267030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267030 prefixEnd_3267030 := by exact prefixLift 3267030
  have htrace : WordTrace (prefixWord ++ tailWord_3267030) baseStart_3267030 baseEnd_3267030 := by
    simpa [prefixWord, tailWord_3267030, baseEnd_3267030] using wordTrace_append hprefix tailTrace_3267030
  have hstable : (prefixWord ++ tailWord_3267030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267030).length < 2 ^ (prefixWord ++ tailWord_3267030).sum := by decide
  have hdescent : baseEnd_3267030 < baseStart_3267030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267032 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_3267032 : Nat := 118140960795 + 3267032 * 2 ^ 59
def prefixEnd_3267032 : Nat := 4983230072969 + 3 ^ 40 * 3267032 * 2
def baseEnd_3267032 : Nat := 559185909873255651991733

theorem tailTrace_3267032 : CollatzResearch.WordTrace tailWord_3267032 prefixEnd_3267032 559185909873255651991733 := by
  unfold tailWord_3267032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59579223150054251744437675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79438964200072335659250233 59579223150054251744437675)
  ·
    refine ⟨89368834725081377616656513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59579223150054251744437675 89368834725081377616656513)
    ·
      refine ⟨67026626043811033212492385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89368834725081377616656513 67026626043811033212492385)
      ·
        refine ⟨50269969532858274909369289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67026626043811033212492385 50269969532858274909369289)
        ·
          refine ⟨37702477149643706182026967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50269969532858274909369289 37702477149643706182026967)
          ·
            refine ⟨56553715724465559273040451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37702477149643706182026967 56553715724465559273040451)
            ·
              refine ⟨84830573586698338909560677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56553715724465559273040451 84830573586698338909560677)
              ·
                refine ⟨15905732547505938545542627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84830573586698338909560677 15905732547505938545542627)
                ·
                  refine ⟨23858598821258907818313941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15905732547505938545542627 23858598821258907818313941)
                  ·
                    refine ⟨559185909873255651991733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23858598821258907818313941 559185909873255651991733)
                    ·
                      rfl

theorem cell23_3267032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_3267032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267032 prefixEnd_3267032 := by exact prefixLift 3267032
  have htrace : WordTrace (prefixWord ++ tailWord_3267032) baseStart_3267032 baseEnd_3267032 := by
    simpa [prefixWord, tailWord_3267032, baseEnd_3267032] using wordTrace_append hprefix tailTrace_3267032
  have hstable : (prefixWord ++ tailWord_3267032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267032).length < 2 ^ (prefixWord ++ tailWord_3267032).sum := by decide
  have hdescent : baseEnd_3267032 < baseStart_3267032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267053 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 5]
def baseStart_3267053 : Nat := 118140960795 + 3267053 * 2 ^ 59
def prefixEnd_3267053 : Nat := 4983230072969 + 3 ^ 40 * 3267053 * 2
def baseEnd_3267053 : Nat := 186396501412612374868067

theorem tailTrace_3267053 : CollatzResearch.WordTrace tailWord_3267053 prefixEnd_3267053 186396501412612374868067 := by
  unfold tailWord_3267053
  simp only [CollatzResearch.WordTrace]
  refine ⟨119159212233032424075389813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79439474822021616050259875 119159212233032424075389813)
  ·
    refine ⟨11171176146846789757067795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119159212233032424075389813 11171176146846789757067795)
    ·
      refine ⟨16756764220270184635601693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11171176146846789757067795 16756764220270184635601693)
      ·
        refine ⟨6283786582601319238350635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16756764220270184635601693 6283786582601319238350635)
        ·
          refine ⟨9425679873901978857525953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283786582601319238350635 9425679873901978857525953)
          ·
            refine ⟨7069259905426484143144465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9425679873901978857525953 7069259905426484143144465)
            ·
              refine ⟨5301944929069863107358349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7069259905426484143144465 5301944929069863107358349)
              ·
                refine ⟨1988229348401198665259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301944929069863107358349 1988229348401198665259381)
                ·
                  refine ⟨186396501412612374868067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1988229348401198665259381 186396501412612374868067)
                  ·
                    rfl

theorem cell23_3267053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_3267053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267053 prefixEnd_3267053 := by exact prefixLift 3267053
  have htrace : WordTrace (prefixWord ++ tailWord_3267053) baseStart_3267053 baseEnd_3267053 := by
    simpa [prefixWord, tailWord_3267053, baseEnd_3267053] using wordTrace_append hprefix tailTrace_3267053
  have hstable : (prefixWord ++ tailWord_3267053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267053).length < 2 ^ (prefixWord ++ tailWord_3267053).sum := by decide
  have hdescent : baseEnd_3267053 < baseStart_3267053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267069 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_3267069 : Nat := 118140960795 + 3267069 * 2 ^ 59
def prefixEnd_3267069 : Nat := 4983230072969 + 3 ^ 40 * 3267069 * 2
def baseEnd_3267069 : Nat := 1677576728403983311212529

theorem tailTrace_3267069 : CollatzResearch.WordTrace tailWord_3267069 prefixEnd_3267069 1677576728403983311212529 := by
  unfold tailWord_3267069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119159795800974458807972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79439863867316305871981507 119159795800974458807972261)
  ·
    refine ⟨22342461712682711026494799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119159795800974458807972261 22342461712682711026494799)
    ·
      refine ⟨33513692569024066539742199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22342461712682711026494799 33513692569024066539742199)
      ·
        refine ⟨50270538853536099809613299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33513692569024066539742199 50270538853536099809613299)
        ·
          refine ⟨75405808280304149714419949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50270538853536099809613299 75405808280304149714419949)
          ·
            refine ⟨28277178105114056142907481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75405808280304149714419949 28277178105114056142907481)
            ·
              refine ⟨21207883578835542107180611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28277178105114056142907481 21207883578835542107180611)
              ·
                refine ⟨31811825368253313160770917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21207883578835542107180611 31811825368253313160770917)
                ·
                  refine ⟨5964717256547496217644547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31811825368253313160770917 5964717256547496217644547)
                  ·
                    refine ⟨8947075884821244326466821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5964717256547496217644547 8947075884821244326466821)
                    ·
                      refine ⟨1677576728403983311212529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8947075884821244326466821 1677576728403983311212529)
                      ·
                        rfl

theorem cell23_3267069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_3267069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267069 prefixEnd_3267069 := by exact prefixLift 3267069
  have htrace : WordTrace (prefixWord ++ tailWord_3267069) baseStart_3267069 baseEnd_3267069 := by
    simpa [prefixWord, tailWord_3267069, baseEnd_3267069] using wordTrace_append hprefix tailTrace_3267069
  have hstable : (prefixWord ++ tailWord_3267069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267069).length < 2 ^ (prefixWord ++ tailWord_3267069).sum := by decide
  have hdescent : baseEnd_3267069 < baseStart_3267069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267089 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_3267089 : Nat := 118140960795 + 3267089 * 2 ^ 59
def prefixEnd_3267089 : Nat := 4983230072969 + 3 ^ 40 * 3267089 * 2
def baseEnd_3267089 : Nat := 1677586998017073232962437

theorem tailTrace_3267089 : CollatzResearch.WordTrace tailWord_3267089 prefixEnd_3267089 1677586998017073232962437 := by
  unfold tailWord_3267089
  simp only [CollatzResearch.WordTrace]
  refine ⟨119160525260902002223700321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79440350173934668149133547 119160525260902002223700321)
  ·
    refine ⟨89370393945676501667775241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119160525260902002223700321 89370393945676501667775241)
    ·
      refine ⟨67027795459257376250831431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89370393945676501667775241 67027795459257376250831431)
      ·
        refine ⟨100541693188886064376247147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67027795459257376250831431 100541693188886064376247147)
        ·
          refine ⟨150812539783329096564370721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100541693188886064376247147 150812539783329096564370721)
          ·
            refine ⟨113109404837496822423278041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150812539783329096564370721 113109404837496822423278041)
            ·
              refine ⟨84832053628122616817458531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113109404837496822423278041 84832053628122616817458531)
              ·
                refine ⟨127248080442183925226187797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84832053628122616817458531 127248080442183925226187797)
                ·
                  refine ⟨5964753770727371494977553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127248080442183925226187797 5964753770727371494977553)
                  ·
                    refine ⟨4473565328045528621233165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5964753770727371494977553 4473565328045528621233165)
                    ·
                      refine ⟨1677586998017073232962437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473565328045528621233165 1677586998017073232962437)
                      ·
                        rfl

theorem cell23_3267089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_3267089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267089 prefixEnd_3267089 := by exact prefixLift 3267089
  have htrace : WordTrace (prefixWord ++ tailWord_3267089) baseStart_3267089 baseEnd_3267089 := by
    simpa [prefixWord, tailWord_3267089, baseEnd_3267089] using wordTrace_append hprefix tailTrace_3267089
  have hstable : (prefixWord ++ tailWord_3267089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267089).length < 2 ^ (prefixWord ++ tailWord_3267089).sum := by decide
  have hdescent : baseEnd_3267089 < baseStart_3267089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267096 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_3267096 : Nat := 118140960795 + 3267096 * 2 ^ 59
def prefixEnd_3267096 : Nat := 4983230072969 + 3 ^ 40 * 3267096 * 2
def baseEnd_3267096 : Nat := 559196864127218235191635

theorem tailTrace_3267096 : CollatzResearch.WordTrace tailWord_3267096 prefixEnd_3267096 559196864127218235191635 := by
  unfold tailWord_3267096
  simp only [CollatzResearch.WordTrace]
  refine ⟨59580390285938321209602571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79440520381251094946136761 59580390285938321209602571)
  ·
    refine ⟨89370585428907481814403857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59580390285938321209602571 89370585428907481814403857)
    ·
      refine ⟨67027939071680611360802893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89370585428907481814403857 67027939071680611360802893)
      ·
        refine ⟨25135477151880229260301085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67027939071680611360802893 25135477151880229260301085)
        ·
          refine ⟨9425803931955085972612907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25135477151880229260301085 9425803931955085972612907)
          ·
            refine ⟨14138705897932628958919361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425803931955085972612907 14138705897932628958919361)
            ·
              refine ⟨10604029423449471719189521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14138705897932628958919361 10604029423449471719189521)
              ·
                refine ⟨7953022067587103789392141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10604029423449471719189521 7953022067587103789392141)
                ·
                  refine ⟨2982383275345163921022053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7953022067587103789392141 2982383275345163921022053)
                  ·
                    refine ⟨559196864127218235191635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982383275345163921022053 559196864127218235191635)
                    ·
                      rfl

theorem cell23_3267096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_3267096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267096 prefixEnd_3267096 := by exact prefixLift 3267096
  have htrace : WordTrace (prefixWord ++ tailWord_3267096) baseStart_3267096 baseEnd_3267096 := by
    simpa [prefixWord, tailWord_3267096, baseEnd_3267096] using wordTrace_append hprefix tailTrace_3267096
  have hstable : (prefixWord ++ tailWord_3267096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267096).length < 2 ^ (prefixWord ++ tailWord_3267096).sum := by decide
  have hdescent : baseEnd_3267096 < baseStart_3267096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267106 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3267106 : Nat := 118140960795 + 3267106 * 2 ^ 59
def prefixEnd_3267106 : Nat := 4983230072969 + 3 ^ 40 * 3267106 * 2
def baseEnd_3267106 : Nat := 1677595727188199666449859

theorem tailTrace_3267106 : CollatzResearch.WordTrace tailWord_3267106 prefixEnd_3267106 1677595727188199666449859 := by
  unfold tailWord_3267106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29790286325460103531767293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79440763534560276084712781 29790286325460103531767293)
  ·
    refine ⟨11171357372047538824412735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29790286325460103531767293 11171357372047538824412735)
    ·
      refine ⟨16757036058071308236619103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11171357372047538824412735 16757036058071308236619103)
      ·
        refine ⟨25135554087106962354928655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16757036058071308236619103 25135554087106962354928655)
        ·
          refine ⟨37703331130660443532392983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25135554087106962354928655 37703331130660443532392983)
          ·
            refine ⟨56554996695990665298589475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37703331130660443532392983 56554996695990665298589475)
            ·
              refine ⟨84832495043985997947884213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56554996695990665298589475 84832495043985997947884213)
              ·
                refine ⟨7953046410373687307614145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84832495043985997947884213 7953046410373687307614145)
                ·
                  refine ⟨5964784807780265480710609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7953046410373687307614145 5964784807780265480710609)
                  ·
                    refine ⟨4473588605835199110532957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5964784807780265480710609 4473588605835199110532957)
                    ·
                      refine ⟨1677595727188199666449859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473588605835199110532957 1677595727188199666449859)
                      ·
                        rfl

theorem cell23_3267106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3267106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267106 prefixEnd_3267106 := by exact prefixLift 3267106
  have htrace : WordTrace (prefixWord ++ tailWord_3267106) baseStart_3267106 baseEnd_3267106 := by
    simpa [prefixWord, tailWord_3267106, baseEnd_3267106] using wordTrace_append hprefix tailTrace_3267106
  have hstable : (prefixWord ++ tailWord_3267106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267106).length < 2 ^ (prefixWord ++ tailWord_3267106).sum := by decide
  have hdescent : baseEnd_3267106 < baseStart_3267106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267126 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_3267126 : Nat := 118140960795 + 3267126 * 2 ^ 59
def prefixEnd_3267126 : Nat := 4983230072969 + 3 ^ 40 * 3267126 * 2
def baseEnd_3267126 : Nat := 186400666311254398688863

theorem tailTrace_3267126 : CollatzResearch.WordTrace tailWord_3267126 prefixEnd_3267126 186400666311254398688863 := by
  unfold tailWord_3267126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447617172610497346424827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79441249841178638361864821 7447617172610497346424827)
  ·
    refine ⟨11171425758915746019637241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447617172610497346424827 11171425758915746019637241)
    ·
      refine ⟨8378569319186809514727931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11171425758915746019637241 8378569319186809514727931)
      ·
        refine ⟨12567853978780214272091897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378569319186809514727931 12567853978780214272091897)
        ·
          refine ⟨9425890484085160704068923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12567853978780214272091897 9425890484085160704068923)
          ·
            refine ⟨14138835726127741056103385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425890484085160704068923 14138835726127741056103385)
            ·
              refine ⟨10604126794595805792077539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14138835726127741056103385 10604126794595805792077539)
              ·
                refine ⟨15906190191893708688116309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604126794595805792077539 15906190191893708688116309)
                ·
                  refine ⟨186400666311254398688863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15906190191893708688116309 186400666311254398688863)
                  ·
                    rfl

theorem cell23_3267126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_3267126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267126 prefixEnd_3267126 := by exact prefixLift 3267126
  have htrace : WordTrace (prefixWord ++ tailWord_3267126) baseStart_3267126 baseEnd_3267126 := by
    simpa [prefixWord, tailWord_3267126, baseEnd_3267126] using wordTrace_append hprefix tailTrace_3267126
  have hstable : (prefixWord ++ tailWord_3267126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267126).length < 2 ^ (prefixWord ++ tailWord_3267126).sum := by decide
  have hdescent : baseEnd_3267126 < baseStart_3267126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267130 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_3267130 : Nat := 118140960795 + 3267130 * 2 ^ 59
def prefixEnd_3267130 : Nat := 4983230072969 + 3 ^ 40 * 3267130 * 2
def baseEnd_3267130 : Nat := 559202683574635857516583

theorem tailTrace_3267130 : CollatzResearch.WordTrace tailWord_3267130 prefixEnd_3267130 559202683574635857516583 := by
  unfold tailWord_3267130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29790505163438366556485711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79441347102502310817295229 29790505163438366556485711)
  ·
    refine ⟨44685757745157549834728567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29790505163438366556485711 44685757745157549834728567)
    ·
      refine ⟨67028636617736324752092851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44685757745157549834728567 67028636617736324752092851)
      ·
        refine ⟨100542954926604487128139277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67028636617736324752092851 100542954926604487128139277)
        ·
          refine ⟨37703608097476682673052229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100542954926604487128139277 37703608097476682673052229)
          ·
            refine ⟨7069426518276878001197293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37703608097476682673052229 7069426518276878001197293)
            ·
              refine ⟨2651034944353829250448985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7069426518276878001197293 2651034944353829250448985)
              ·
                refine ⟨1988276208265371937836739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651034944353829250448985 1988276208265371937836739)
                ·
                  refine ⟨2982414312398057906755109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988276208265371937836739 2982414312398057906755109)
                  ·
                    refine ⟨559202683574635857516583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982414312398057906755109 559202683574635857516583)
                    ·
                      rfl

theorem cell23_3267130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_3267130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267130 prefixEnd_3267130 := by exact prefixLift 3267130
  have htrace : WordTrace (prefixWord ++ tailWord_3267130) baseStart_3267130 baseEnd_3267130 := by
    simpa [prefixWord, tailWord_3267130, baseEnd_3267130] using wordTrace_append hprefix tailTrace_3267130
  have hstable : (prefixWord ++ tailWord_3267130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267130).length < 2 ^ (prefixWord ++ tailWord_3267130).sum := by decide
  have hdescent : baseEnd_3267130 < baseStart_3267130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267143 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 6]
def baseStart_3267143 : Nat := 118140960795 + 3267143 * 2 ^ 59
def prefixEnd_3267143 : Nat := 4983230072969 + 3 ^ 40 * 3267143 * 2
def baseEnd_3267143 : Nat := 186401636219157335743021

theorem tailTrace_3267143 : CollatzResearch.WordTrace tailWord_3267143 prefixEnd_3267143 186401636219157335743021 := by
  unfold tailWord_3267143
  simp only [CollatzResearch.WordTrace]
  refine ⟨119162494802706369446166083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79441663201804246297444055 119162494802706369446166083)
  ·
    refine ⟨178743742204059554169249125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119162494802706369446166083 178743742204059554169249125)
    ·
      refine ⟨33514451663261166406734211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178743742204059554169249125 33514451663261166406734211)
      ·
        refine ⟨50271677494891749610101317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33514451663261166406734211 50271677494891749610101317)
        ·
          refine ⟨9425939530292203051893997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50271677494891749610101317 9425939530292203051893997)
          ·
            refine ⟨3534727323859576144460249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9425939530292203051893997 3534727323859576144460249)
            ·
              refine ⟨2651045492894682108345187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534727323859576144460249 2651045492894682108345187)
              ·
                refine ⟨3976568239342023162517781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651045492894682108345187 3976568239342023162517781)
                ·
                  refine ⟨186401636219157335743021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3976568239342023162517781 186401636219157335743021)
                  ·
                    rfl

theorem cell23_3267143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 6].length) (baseStart_3267143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267143 prefixEnd_3267143 := by exact prefixLift 3267143
  have htrace : WordTrace (prefixWord ++ tailWord_3267143) baseStart_3267143 baseEnd_3267143 := by
    simpa [prefixWord, tailWord_3267143, baseEnd_3267143] using wordTrace_append hprefix tailTrace_3267143
  have hstable : (prefixWord ++ tailWord_3267143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267143).length < 2 ^ (prefixWord ++ tailWord_3267143).sum := by decide
  have hdescent : baseEnd_3267143 < baseStart_3267143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267156 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3267156 : Nat := 118140960795 + 3267156 * 2 ^ 59
def prefixEnd_3267156 : Nat := 4983230072969 + 3 ^ 40 * 3267156 * 2
def baseEnd_3267156 : Nat := 559207133740308156941543

theorem tailTrace_3267156 : CollatzResearch.WordTrace tailWord_3267156 prefixEnd_3267156 559207133740308156941543 := by
  unfold tailWord_3267156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59581484475829636333194661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79441979301106181777592881 59581484475829636333194661)
  ·
    refine ⟨11171528339218056812473999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59581484475829636333194661 11171528339218056812473999)
    ·
      refine ⟨16757292508827085218710999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11171528339218056812473999 16757292508827085218710999)
      ·
        refine ⟨25135938763240627828066499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16757292508827085218710999 25135938763240627828066499)
        ·
          refine ⟨37703908144860941742099749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25135938763240627828066499 37703908144860941742099749)
          ·
            refine ⟨7069482777161426576643703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37703908144860941742099749 7069482777161426576643703)
            ·
              refine ⟨10604224165742139864965555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069482777161426576643703 10604224165742139864965555)
              ·
                refine ⟨15906336248613209797448333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604224165742139864965555 15906336248613209797448333)
                ·
                  refine ⟨5964876093229953674043125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15906336248613209797448333 5964876093229953674043125)
                  ·
                    refine ⟨559207133740308156941543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5964876093229953674043125 559207133740308156941543)
                    ·
                      rfl

theorem cell23_3267156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3267156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267156 prefixEnd_3267156 := by exact prefixLift 3267156
  have htrace : WordTrace (prefixWord ++ tailWord_3267156) baseStart_3267156 baseEnd_3267156 := by
    simpa [prefixWord, tailWord_3267156, baseEnd_3267156] using wordTrace_append hprefix tailTrace_3267156
  have hstable : (prefixWord ++ tailWord_3267156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267156).length < 2 ^ (prefixWord ++ tailWord_3267156).sum := by decide
  have hdescent : baseEnd_3267156 < baseStart_3267156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267169 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3267169 : Nat := 118140960795 + 3267169 * 2 ^ 59
def prefixEnd_3267169 : Nat := 4983230072969 + 3 ^ 40 * 3267169 * 2
def baseEnd_3267169 : Nat := 559209358823144306654023

theorem tailTrace_3267169 : CollatzResearch.WordTrace tailWord_3267169 prefixEnd_3267169 559209358823144306654023 := by
  unfold tailWord_3267169
  simp only [CollatzResearch.WordTrace]
  refine ⟨119163443100612175886612561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79442295400408117257741707 119163443100612175886612561)
  ·
    refine ⟨89372582325459131914959421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119163443100612175886612561 89372582325459131914959421)
    ·
      refine ⟨33514718372047174468109783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89372582325459131914959421 33514718372047174468109783)
      ·
        refine ⟨50272077558070761702164675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33514718372047174468109783 50272077558070761702164675)
        ·
          refine ⟨75408116337106142553247013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50272077558070761702164675 75408116337106142553247013)
          ·
            refine ⟨14139021813207401728733815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75408116337106142553247013 14139021813207401728733815)
            ·
              refine ⟨21208532719811102593100723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14139021813207401728733815 21208532719811102593100723)
              ·
                refine ⟨31812799079716653889651085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21208532719811102593100723 31812799079716653889651085)
                ·
                  refine ⟨11929799654893745208619157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31812799079716653889651085 11929799654893745208619157)
                  ·
                    refine ⟨559209358823144306654023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11929799654893745208619157 559209358823144306654023)
                    ·
                      rfl

theorem cell23_3267169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3267169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267169 prefixEnd_3267169 := by exact prefixLift 3267169
  have htrace : WordTrace (prefixWord ++ tailWord_3267169) baseStart_3267169 baseEnd_3267169 := by
    simpa [prefixWord, tailWord_3267169, baseEnd_3267169] using wordTrace_append hprefix tailTrace_3267169
  have hstable : (prefixWord ++ tailWord_3267169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267169).length < 2 ^ (prefixWord ++ tailWord_3267169).sum := by decide
  have hdescent : baseEnd_3267169 < baseStart_3267169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267179 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5]
def baseStart_3267179 : Nat := 118140960795 + 3267179 * 2 ^ 59
def prefixEnd_3267179 : Nat := 4983230072969 + 3 ^ 40 * 3267179 * 2
def baseEnd_3267179 : Nat := 1677633211275977880837023

theorem tailTrace_3267179 : CollatzResearch.WordTrace tailWord_3267179 prefixEnd_3267179 1677633211275977880837023 := by
  unfold tailWord_3267179
  simp only [CollatzResearch.WordTrace]
  refine ⟨119163807830575947594476591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79442538553717298396317727 119163807830575947594476591)
  ·
    refine ⟨178745711745863921391714887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119163807830575947594476591 178745711745863921391714887)
    ·
      refine ⟨268118567618795882087572331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178745711745863921391714887 268118567618795882087572331)
      ·
        refine ⟨402177851428193823131358497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268118567618795882087572331 402177851428193823131358497)
        ·
          refine ⟨301633388571145367348518873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402177851428193823131358497 301633388571145367348518873)
          ·
            refine ⟨226225041428359025511389155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301633388571145367348518873 226225041428359025511389155)
            ·
              refine ⟨339337562142538538267083733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226225041428359025511389155 339337562142538538267083733)
              ·
                refine ⟨7953224112715746990634775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 339337562142538538267083733 7953224112715746990634775)
                ·
                  refine ⟨11929836169073620485952163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953224112715746990634775 11929836169073620485952163)
                  ·
                    refine ⟨17894754253610430728928245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11929836169073620485952163 17894754253610430728928245)
                    ·
                      refine ⟨1677633211275977880837023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17894754253610430728928245 1677633211275977880837023)
                      ·
                        rfl

theorem cell23_3267179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_3267179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267179 prefixEnd_3267179 := by exact prefixLift 3267179
  have htrace : WordTrace (prefixWord ++ tailWord_3267179) baseStart_3267179 baseEnd_3267179 := by
    simpa [prefixWord, tailWord_3267179, baseEnd_3267179] using wordTrace_append hprefix tailTrace_3267179
  have hstable : (prefixWord ++ tailWord_3267179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267179).length < 2 ^ (prefixWord ++ tailWord_3267179).sum := by decide
  have hdescent : baseEnd_3267179 < baseStart_3267179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267196 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_3267196 : Nat := 118140960795 + 3267196 * 2 ^ 59
def prefixEnd_3267196 : Nat := 4983230072969 + 3 ^ 40 * 3267196 * 2
def baseEnd_3267196 : Nat := 1677641940447104314324445

theorem tailTrace_3267196 : CollatzResearch.WordTrace tailWord_3267196 prefixEnd_3267196 1677641940447104314324445 := by
  unfold tailWord_3267196
  simp only [CollatzResearch.WordTrace]
  refine ⟨59582213935757179748922721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79442951914342906331896961 59582213935757179748922721)
  ·
    refine ⟨44686660451817884811692041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59582213935757179748922721 44686660451817884811692041)
    ·
      refine ⟨33514995338863413608769031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44686660451817884811692041 33514995338863413608769031)
      ·
        refine ⟨50272493008295120413153547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33514995338863413608769031 50272493008295120413153547)
        ·
          refine ⟨75408739512442680619730321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50272493008295120413153547 75408739512442680619730321)
          ·
            refine ⟨56556554634332010464797741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75408739512442680619730321 56556554634332010464797741)
            ·
              refine ⟨21208707987874503924299153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56556554634332010464797741 21208707987874503924299153)
              ·
                refine ⟨15906530990905877943224365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21208707987874503924299153 15906530990905877943224365)
                ·
                  refine ⟨5964949121589704228709137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15906530990905877943224365 5964949121589704228709137)
                  ·
                    refine ⟨4473711841192278171531853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5964949121589704228709137 4473711841192278171531853)
                    ·
                      refine ⟨1677641940447104314324445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473711841192278171531853 1677641940447104314324445)
                      ·
                        rfl

theorem cell23_3267196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_3267196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267196 prefixEnd_3267196 := by exact prefixLift 3267196
  have htrace : WordTrace (prefixWord ++ tailWord_3267196) baseStart_3267196 baseEnd_3267196 := by
    simpa [prefixWord, tailWord_3267196, baseEnd_3267196] using wordTrace_append hprefix tailTrace_3267196
  have hstable : (prefixWord ++ tailWord_3267196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267196).length < 2 ^ (prefixWord ++ tailWord_3267196).sum := by decide
  have hdescent : baseEnd_3267196 < baseStart_3267196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267230 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3267230 : Nat := 118140960795 + 3267230 * 2 ^ 59
def prefixEnd_3267230 : Nat := 4983230072969 + 3 ^ 40 * 3267230 * 2
def baseEnd_3267230 : Nat := 1677659398789357181299289

theorem tailTrace_3267230 : CollatzResearch.WordTrace tailWord_3267230 prefixEnd_3267230 1677659398789357181299289 := by
  unfold tailWord_3267230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14895708494173897913072893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79443778635594122203055429 14895708494173897913072893)
  ·
    refine ⟨5585890685315211717402335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14895708494173897913072893 5585890685315211717402335)
    ·
      refine ⟨8378836027972817576103503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585890685315211717402335 8378836027972817576103503)
      ·
        refine ⟨12568254041959226364155255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378836027972817576103503 12568254041959226364155255)
        ·
          refine ⟨18852381062938839546232883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12568254041959226364155255 18852381062938839546232883)
          ·
            refine ⟨28278571594408259319349325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18852381062938839546232883 28278571594408259319349325)
            ·
              refine ⟨10604464347903097244755997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28278571594408259319349325 10604464347903097244755997)
              ·
                refine ⟨3976674130463661466783499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10604464347903097244755997 3976674130463661466783499)
                ·
                  refine ⟨5965011195695492200175249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976674130463661466783499 5965011195695492200175249)
                  ·
                    refine ⟨4473758396771619150131437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965011195695492200175249 4473758396771619150131437)
                    ·
                      refine ⟨1677659398789357181299289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4473758396771619150131437 1677659398789357181299289)
                      ·
                        rfl

theorem cell23_3267230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3267230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267230 prefixEnd_3267230 := by exact prefixLift 3267230
  have htrace : WordTrace (prefixWord ++ tailWord_3267230) baseStart_3267230 baseEnd_3267230 := by
    simpa [prefixWord, tailWord_3267230, baseEnd_3267230] using wordTrace_append hprefix tailTrace_3267230
  have hstable : (prefixWord ++ tailWord_3267230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267230).length < 2 ^ (prefixWord ++ tailWord_3267230).sum := by decide
  have hdescent : baseEnd_3267230 < baseStart_3267230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267254 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3267254 : Nat := 118140960795 + 3267254 * 2 ^ 59
def prefixEnd_3267254 : Nat := 4983230072969 + 3 ^ 40 * 3267254 * 2
def baseEnd_3267254 : Nat := 559223907441688362466393

theorem tailTrace_3267254 : CollatzResearch.WordTrace tailWord_3267254 prefixEnd_3267254 559223907441688362466393 := by
  unfold tailWord_3267254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447908956581514712716051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79444362203536156935637877 7447908956581514712716051)
  ·
    refine ⟨11171863434872272069074077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447908956581514712716051 11171863434872272069074077)
    ·
      refine ⟨4189448788077102025902779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11171863434872272069074077 4189448788077102025902779)
      ·
        refine ⟨6284173182115653038854169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189448788077102025902779 6284173182115653038854169)
        ·
          refine ⟨4713129886586739779140627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6284173182115653038854169 4713129886586739779140627)
          ·
            refine ⟨7069694829880109668710941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713129886586739779140627 7069694829880109668710941)
            ·
              refine ⟨2651135561205041125766603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7069694829880109668710941 2651135561205041125766603)
              ·
                refine ⟨3976703341807561688649905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651135561205041125766603 3976703341807561688649905)
                ·
                  refine ⟨2982527506355671266487429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976703341807561688649905 2982527506355671266487429)
                  ·
                    refine ⟨559223907441688362466393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982527506355671266487429 559223907441688362466393)
                    ·
                      rfl

theorem cell23_3267254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3267254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267254 prefixEnd_3267254 := by exact prefixLift 3267254
  have htrace : WordTrace (prefixWord ++ tailWord_3267254) baseStart_3267254 baseEnd_3267254 := by
    simpa [prefixWord, tailWord_3267254, baseEnd_3267254] using wordTrace_append hprefix tailTrace_3267254
  have hstable : (prefixWord ++ tailWord_3267254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267254).length < 2 ^ (prefixWord ++ tailWord_3267254).sum := by decide
  have hdescent : baseEnd_3267254 < baseStart_3267254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267300 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_3267300 : Nat := 118140960795 + 3267300 * 2 ^ 59
def prefixEnd_3267300 : Nat := 4983230072969 + 3 ^ 40 * 3267300 * 2
def baseEnd_3267300 : Nat := 1677695342435171907423967

theorem tailTrace_3267300 : CollatzResearch.WordTrace tailWord_3267300 prefixEnd_3267300 1677695342435171907423967 := by
  unfold tailWord_3267300
  simp only [CollatzResearch.WordTrace]
  refine ⟨59584110531568792629815677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79445480708758390173087569 59584110531568792629815677)
  ·
    refine ⟨22344041449338297236180879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59584110531568792629815677 22344041449338297236180879)
    ·
      refine ⟨33516062174007445854271319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22344041449338297236180879 33516062174007445854271319)
      ·
        refine ⟨50274093261011168781406979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33516062174007445854271319 50274093261011168781406979)
        ·
          refine ⟨75411139891516753172110469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50274093261011168781406979 75411139891516753172110469)
          ·
            refine ⟨14139588729659391219770713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75411139891516753172110469 14139588729659391219770713)
            ·
              refine ⟨10604691547244543414828035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14139588729659391219770713 10604691547244543414828035)
              ·
                refine ⟨15907037320866815122242053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604691547244543414828035 15907037320866815122242053)
                ·
                  refine ⟨2982569497662527835420385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15907037320866815122242053 2982569497662527835420385)
                  ·
                    refine ⟨2236927123246895876565289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2982569497662527835420385 2236927123246895876565289)
                    ·
                      refine ⟨1677695342435171907423967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2236927123246895876565289 1677695342435171907423967)
                      ·
                        rfl

theorem cell23_3267300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_3267300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267300 prefixEnd_3267300 := by exact prefixLift 3267300
  have htrace : WordTrace (prefixWord ++ tailWord_3267300) baseStart_3267300 baseEnd_3267300 := by
    simpa [prefixWord, tailWord_3267300, baseEnd_3267300] using wordTrace_append hprefix tailTrace_3267300
  have hstable : (prefixWord ++ tailWord_3267300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267300).length < 2 ^ (prefixWord ++ tailWord_3267300).sum := by decide
  have hdescent : baseEnd_3267300 < baseStart_3267300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267357 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 5]
def baseStart_3267357 : Nat := 118140960795 + 3267357 * 2 ^ 59
def prefixEnd_3267357 : Nat := 4983230072969 + 3 ^ 40 * 3267357 * 2
def baseEnd_3267357 : Nat := 186413845648053131601245

theorem tailTrace_3267357 : CollatzResearch.WordTrace tailWord_3267357 prefixEnd_3267357 186413845648053131601245 := by
  unfold tailWord_3267357
  simp only [CollatzResearch.WordTrace]
  refine ⟨119170300023931083994456325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79446866682620722662970883 119170300023931083994456325)
  ·
    refine ⟨22344431254487078248960561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119170300023931083994456325 22344431254487078248960561)
    ·
      refine ⟨16758323440865308686720421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22344431254487078248960561 16758323440865308686720421)
      ·
        refine ⟨3142185645162245378760079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16758323440865308686720421 3142185645162245378760079)
        ·
          refine ⟨4713278467743368068140119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142185645162245378760079 4713278467743368068140119)
          ·
            refine ⟨7069917701615052102210179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713278467743368068140119 7069917701615052102210179)
            ·
              refine ⟨10604876552422578153315269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069917701615052102210179 10604876552422578153315269)
              ·
                refine ⟨1988414353579233403746613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10604876552422578153315269 1988414353579233403746613)
                ·
                  refine ⟨186413845648053131601245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1988414353579233403746613 186413845648053131601245)
                  ·
                    rfl

theorem cell23_3267357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_3267357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267357 prefixEnd_3267357 := by exact prefixLift 3267357
  have htrace : WordTrace (prefixWord ++ tailWord_3267357) baseStart_3267357 baseEnd_3267357 := by
    simpa [prefixWord, tailWord_3267357, baseEnd_3267357] using wordTrace_append hprefix tailTrace_3267357
  have hstable : (prefixWord ++ tailWord_3267357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267357).length < 2 ^ (prefixWord ++ tailWord_3267357).sum := by decide
  have hdescent : baseEnd_3267357 < baseStart_3267357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267383 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 3, 4]
def baseStart_3267383 : Nat := 118140960795 + 3267383 * 2 ^ 59
def prefixEnd_3267383 : Nat := 4983230072969 + 3 ^ 40 * 3267383 * 2
def baseEnd_3267383 : Nat := 559245987109831694228695

theorem tailTrace_3267383 : CollatzResearch.WordTrace tailWord_3267383 prefixEnd_3267383 559245987109831694228695 := by
  unfold tailWord_3267383
  simp only [CollatzResearch.WordTrace]
  refine ⟨119171248321836890434902803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79447498881224593623268535 119171248321836890434902803)
  ·
    refine ⟨178756872482755335652354205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119171248321836890434902803 178756872482755335652354205)
    ·
      refine ⟨67033827181033250869632827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178756872482755335652354205 67033827181033250869632827)
      ·
        refine ⟨100550740771549876304449241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67033827181033250869632827 100550740771549876304449241)
        ·
          refine ⟨75413055578662407228336931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100550740771549876304449241 75413055578662407228336931)
          ·
            refine ⟨113119583367993610842505397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75413055578662407228336931 113119583367993610842505397)
            ·
              refine ⟨10604960940749401016484881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113119583367993610842505397 10604960940749401016484881)
              ·
                refine ⟨7953720705562050762363661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10604960940749401016484881 7953720705562050762363661)
                ·
                  refine ⟨2982645264585769035886373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7953720705562050762363661 2982645264585769035886373)
                  ·
                    refine ⟨559245987109831694228695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982645264585769035886373 559245987109831694228695)
                    ·
                      rfl

theorem cell23_3267383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_3267383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267383 prefixEnd_3267383 := by exact prefixLift 3267383
  have htrace : WordTrace (prefixWord ++ tailWord_3267383) baseStart_3267383 baseEnd_3267383 := by
    simpa [prefixWord, tailWord_3267383, baseEnd_3267383] using wordTrace_append hprefix tailTrace_3267383
  have hstable : (prefixWord ++ tailWord_3267383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267383).length < 2 ^ (prefixWord ++ tailWord_3267383).sum := by decide
  have hdescent : baseEnd_3267383 < baseStart_3267383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267390 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3267390 : Nat := 118140960795 + 3267390 * 2 ^ 59
def prefixEnd_3267390 : Nat := 4983230072969 + 3 ^ 40 * 3267390 * 2
def baseEnd_3267390 : Nat := 1677741555694076555298553

theorem tailTrace_3267390 : CollatzResearch.WordTrace tailWord_3267390 prefixEnd_3267390 1677741555694076555298553 := by
  unfold tailWord_3267390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896437954101441328800953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79447669088541020420271749 14896437954101441328800953)
  ·
    refine ⟨11172328465576080996600715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14896437954101441328800953 11172328465576080996600715)
    ·
      refine ⟨16758492698364121494901073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11172328465576080996600715 16758492698364121494901073)
      ·
        refine ⟨12568869523773091121175805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16758492698364121494901073 12568869523773091121175805)
        ·
          refine ⟨4713326071414909170440927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12568869523773091121175805 4713326071414909170440927)
          ·
            refine ⟨7069989107122363755661391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713326071414909170440927 7069989107122363755661391)
            ·
              refine ⟨10604983660683545633492087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069989107122363755661391 10604983660683545633492087)
              ·
                refine ⟨15907475491025318450238131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604983660683545633492087 15907475491025318450238131)
                ·
                  refine ⟨23861213236537977675357197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15907475491025318450238131 23861213236537977675357197)
                  ·
                    refine ⟨8947954963701741628258949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23861213236537977675357197 8947954963701741628258949)
                    ·
                      refine ⟨1677741555694076555298553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8947954963701741628258949 1677741555694076555298553)
                      ·
                        rfl

theorem cell23_3267390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3267390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267390 prefixEnd_3267390 := by exact prefixLift 3267390
  have htrace : WordTrace (prefixWord ++ tailWord_3267390) baseStart_3267390 baseEnd_3267390 := by
    simpa [prefixWord, tailWord_3267390, baseEnd_3267390] using wordTrace_append hprefix tailTrace_3267390
  have hstable : (prefixWord ++ tailWord_3267390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267390).length < 2 ^ (prefixWord ++ tailWord_3267390).sum := by decide
  have hdescent : baseEnd_3267390 < baseStart_3267390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267440 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3]
def baseStart_3267440 : Nat := 118140960795 + 3267440 * 2 ^ 59
def prefixEnd_3267440 : Nat := 4983230072969 + 3 ^ 40 * 3267440 * 2
def baseEnd_3267440 : Nat := 1677767229726801359673323

theorem tailTrace_3267440 : CollatzResearch.WordTrace tailWord_3267440 prefixEnd_3267440 1677767229726801359673323 := by
  unfold tailWord_3267440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59586663641315194584863887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79448884855086926113151849 59586663641315194584863887)
  ·
    refine ⟨89379995461972791877295831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59586663641315194584863887 89379995461972791877295831)
    ·
      refine ⟨134069993192959187815943747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89379995461972791877295831 134069993192959187815943747)
      ·
        refine ⟨201104989789438781723915621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134069993192959187815943747 201104989789438781723915621)
        ·
          refine ⟨37707185585519771573234179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201104989789438781723915621 37707185585519771573234179)
          ·
            refine ⟨56560778378279657359851269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37707185585519771573234179 56560778378279657359851269)
            ·
              refine ⟨10605145945927435754972113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56560778378279657359851269 10605145945927435754972113)
              ·
                refine ⟨7953859459445576816229085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10605145945927435754972113 7953859459445576816229085)
                ·
                  refine ⟨2982697297292091306085907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7953859459445576816229085 2982697297292091306085907)
                  ·
                    refine ⟨4474045945938136959128861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982697297292091306085907 4474045945938136959128861)
                    ·
                      refine ⟨1677767229726801359673323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474045945938136959128861 1677767229726801359673323)
                      ·
                        rfl

theorem cell23_3267440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_3267440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267440 prefixEnd_3267440 := by exact prefixLift 3267440
  have htrace : WordTrace (prefixWord ++ tailWord_3267440) baseStart_3267440 baseEnd_3267440 := by
    simpa [prefixWord, tailWord_3267440, baseEnd_3267440] using wordTrace_append hprefix tailTrace_3267440
  have hstable : (prefixWord ++ tailWord_3267440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267440).length < 2 ^ (prefixWord ++ tailWord_3267440).sum := by decide
  have hdescent : baseEnd_3267440 < baseStart_3267440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267443 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 1, 5]
def baseStart_3267443 : Nat := 118140960795 + 3267443 * 2 ^ 59
def prefixEnd_3267443 : Nat := 4983230072969 + 3 ^ 40 * 3267443 * 2
def baseEnd_3267443 : Nat := 559256256722921615978603

theorem tailTrace_3267443 : CollatzResearch.WordTrace tailWord_3267443 prefixEnd_3267443 559256256722921615978603 := by
  unfold tailWord_3267443
  simp only [CollatzResearch.WordTrace]
  refine ⟨119173436701619520682086983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79448957801079680454724655 119173436701619520682086983)
  ·
    refine ⟨178760155052429281023130475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119173436701619520682086983 178760155052429281023130475)
    ·
      refine ⟨268140232578643921534695713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178760155052429281023130475 268140232578643921534695713)
      ·
        refine ⟨201105174433982941151021785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268140232578643921534695713 201105174433982941151021785)
        ·
          refine ⟨150828880825487205863266339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201105174433982941151021785 150828880825487205863266339)
          ·
            refine ⟨226243321238230808794899509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150828880825487205863266339 226243321238230808794899509)
            ·
              refine ⟨21210311366084138324521829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226243321238230808794899509 21210311366084138324521829)
              ·
                refine ⟨3976933381140775935847843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21210311366084138324521829 3976933381140775935847843)
                ·
                  refine ⟨5965400071711163903771765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976933381140775935847843 5965400071711163903771765)
                  ·
                    refine ⟨559256256722921615978603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5965400071711163903771765 559256256722921615978603)
                    ·
                      rfl

theorem cell23_3267443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 5].length) (baseStart_3267443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267443 prefixEnd_3267443 := by exact prefixLift 3267443
  have htrace : WordTrace (prefixWord ++ tailWord_3267443) baseStart_3267443 baseEnd_3267443 := by
    simpa [prefixWord, tailWord_3267443, baseEnd_3267443] using wordTrace_append hprefix tailTrace_3267443
  have hstable : (prefixWord ++ tailWord_3267443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267443).length < 2 ^ (prefixWord ++ tailWord_3267443).sum := by decide
  have hdescent : baseEnd_3267443 < baseStart_3267443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267450 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_3267450 : Nat := 118140960795 + 3267450 * 2 ^ 59
def prefixEnd_3267450 : Nat := 4983230072969 + 3 ^ 40 * 3267450 * 2
def baseEnd_3267450 : Nat := 1677772364533346320548277

theorem tailTrace_3267450 : CollatzResearch.WordTrace tailWord_3267450 prefixEnd_3267450 1677772364533346320548277 := by
  unfold tailWord_3267450
  simp only [CollatzResearch.WordTrace]
  refine ⟨29793423003148540219397951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79449128008396107251727869 29793423003148540219397951)
  ·
    refine ⟨44690134504722810329096927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29793423003148540219397951 44690134504722810329096927)
    ·
      refine ⟨67035201757084215493645391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44690134504722810329096927 67035201757084215493645391)
      ·
        refine ⟨100552802635626323240468087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67035201757084215493645391 100552802635626323240468087)
        ·
          refine ⟨150829203953439484860702131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100552802635626323240468087 150829203953439484860702131)
          ·
            refine ⟨226243805930159227291053197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150829203953439484860702131 226243805930159227291053197)
            ·
              refine ⟨84841427223809710234144949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226243805930159227291053197 84841427223809710234144949)
              ·
                refine ⟨7953883802232160334451089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84841427223809710234144949 7953883802232160334451089)
                ·
                  refine ⟨5965412851674120250838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7953883802232160334451089 5965412851674120250838317)
                  ·
                    refine ⟨2237029819377795094064369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5965412851674120250838317 2237029819377795094064369)
                    ·
                      refine ⟨1677772364533346320548277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237029819377795094064369 1677772364533346320548277)
                      ·
                        rfl

theorem cell23_3267450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_3267450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267450 prefixEnd_3267450 := by exact prefixLift 3267450
  have htrace : WordTrace (prefixWord ++ tailWord_3267450) baseStart_3267450 baseEnd_3267450 := by
    simpa [prefixWord, tailWord_3267450, baseEnd_3267450] using wordTrace_append hprefix tailTrace_3267450
  have hstable : (prefixWord ++ tailWord_3267450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267450).length < 2 ^ (prefixWord ++ tailWord_3267450).sum := by decide
  have hdescent : baseEnd_3267450 < baseStart_3267450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267501 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3267501 : Nat := 118140960795 + 3267501 * 2 ^ 59
def prefixEnd_3267501 : Nat := 4983230072969 + 3 ^ 40 * 3267501 * 2
def baseEnd_3267501 : Nat := 1677798552046725621010543

theorem tailTrace_3267501 : CollatzResearch.WordTrace tailWord_3267501 prefixEnd_3267501 1677798552046725621010543 := by
  unfold tailWord_3267501
  simp only [CollatzResearch.WordTrace]
  refine ⟨119175552135409396587698357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79450368090272931058465571 119175552135409396587698357)
  ·
    refine ⟨11172708012694630930096721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119175552135409396587698357 11172708012694630930096721)
    ·
      refine ⟨8379531009520973197572541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11172708012694630930096721 8379531009520973197572541)
      ·
        refine ⟨3142324128570364949089703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8379531009520973197572541 3142324128570364949089703)
        ·
          refine ⟨4713486192855547423634555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142324128570364949089703 4713486192855547423634555)
          ·
            refine ⟨7070229289283321135451833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713486192855547423634555 7070229289283321135451833)
            ·
              refine ⟨5302671966962490851588875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7070229289283321135451833 5302671966962490851588875)
              ·
                refine ⟨7954007950443736277383313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302671966962490851588875 7954007950443736277383313)
                ·
                  refine ⟨5965505962832802208037485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7954007950443736277383313 5965505962832802208037485)
                  ·
                    refine ⟨2237064736062300828014057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5965505962832802208037485 2237064736062300828014057)
                    ·
                      refine ⟨1677798552046725621010543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237064736062300828014057 1677798552046725621010543)
                      ·
                        rfl

theorem cell23_3267501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3267501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267501 prefixEnd_3267501 := by exact prefixLift 3267501
  have htrace : WordTrace (prefixWord ++ tailWord_3267501) baseStart_3267501 baseEnd_3267501 := by
    simpa [prefixWord, tailWord_3267501, baseEnd_3267501] using wordTrace_append hprefix tailTrace_3267501
  have hstable : (prefixWord ++ tailWord_3267501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267501).length < 2 ^ (prefixWord ++ tailWord_3267501).sum := by decide
  have hdescent : baseEnd_3267501 < baseStart_3267501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267514 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2]
def baseStart_3267514 : Nat := 118140960795 + 3267514 * 2 ^ 59
def prefixEnd_3267514 : Nat := 4983230072969 + 3 ^ 40 * 3267514 * 2
def baseEnd_3267514 : Nat := 1677805227295234070147983

theorem tailTrace_3267514 : CollatzResearch.WordTrace tailWord_3267514 prefixEnd_3267514 1677805227295234070147983 := by
  unfold tailWord_3267514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29794006571090574951980399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79450684189574866538614397 29794006571090574951980399)
  ·
    refine ⟨44691009856635862427970599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29794006571090574951980399 44691009856635862427970599)
    ·
      refine ⟨67036514784953793641955899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44691009856635862427970599 67036514784953793641955899)
      ·
        refine ⟨100554772177430690462933849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67036514784953793641955899 100554772177430690462933849)
        ·
          refine ⟨75416079133073017847200387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100554772177430690462933849 75416079133073017847200387)
          ·
            refine ⟨113124118699609526770800581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75416079133073017847200387 113124118699609526770800581)
            ·
              refine ⟨21210772256176786269525109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113124118699609526770800581 21210772256176786269525109)
              ·
                refine ⟨1988509899016573712767979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21210772256176786269525109 1988509899016573712767979)
                ·
                  refine ⟨2982764848524860569151969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988509899016573712767979 2982764848524860569151969)
                  ·
                    refine ⟨2237073636393645426863977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2982764848524860569151969 2237073636393645426863977)
                    ·
                      refine ⟨1677805227295234070147983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237073636393645426863977 1677805227295234070147983)
                      ·
                        rfl

theorem cell23_3267514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_3267514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267514 prefixEnd_3267514 := by exact prefixLift 3267514
  have htrace : WordTrace (prefixWord ++ tailWord_3267514) baseStart_3267514 baseEnd_3267514 := by
    simpa [prefixWord, tailWord_3267514, baseEnd_3267514] using wordTrace_append hprefix tailTrace_3267514
  have hstable : (prefixWord ++ tailWord_3267514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267514).length < 2 ^ (prefixWord ++ tailWord_3267514).sum := by decide
  have hdescent : baseEnd_3267514 < baseStart_3267514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267517 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3267517 : Nat := 118140960795 + 3267517 * 2 ^ 59
def prefixEnd_3267517 : Nat := 4983230072969 + 3 ^ 40 * 3267517 * 2
def baseEnd_3267517 : Nat := 1677806767737197558410469

theorem tailTrace_3267517 : CollatzResearch.WordTrace tailWord_3267517 prefixEnd_3267517 1677806767737197558410469 := by
  unfold tailWord_3267517
  simp only [CollatzResearch.WordTrace]
  refine ⟨119176135703351431320280805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79450757135567620880187203 119176135703351431320280805)
  ·
    refine ⟨22345525444378393372552651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119176135703351431320280805 22345525444378393372552651)
    ·
      refine ⟨33518288166567590058828977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22345525444378393372552651 33518288166567590058828977)
      ·
        refine ⟨25138716124925692544121733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33518288166567590058828977 25138716124925692544121733)
        ·
          refine ⟨4713509273423567352022825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25138716124925692544121733 4713509273423567352022825)
          ·
            refine ⟨3535131955067675514017119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713509273423567352022825 3535131955067675514017119)
            ·
              refine ⟨5302697932601513271025679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535131955067675514017119 5302697932601513271025679)
              ·
                refine ⟨7954046898902269906538519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302697932601513271025679 7954046898902269906538519)
                ·
                  refine ⟨11931070348353404859807779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7954046898902269906538519 11931070348353404859807779)
                  ·
                    refine ⟨17896605522530107289711669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11931070348353404859807779 17896605522530107289711669)
                    ·
                      refine ⟨1677806767737197558410469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17896605522530107289711669 1677806767737197558410469)
                      ·
                        rfl

theorem cell23_3267517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3267517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267517 prefixEnd_3267517 := by exact prefixLift 3267517
  have htrace : WordTrace (prefixWord ++ tailWord_3267517) baseStart_3267517 baseEnd_3267517 := by
    simpa [prefixWord, tailWord_3267517, baseEnd_3267517] using wordTrace_append hprefix tailTrace_3267517
  have hstable : (prefixWord ++ tailWord_3267517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267517).length < 2 ^ (prefixWord ++ tailWord_3267517).sum := by decide
  have hdescent : baseEnd_3267517 < baseStart_3267517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267531 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 1, 2, 2]
def baseStart_3267531 : Nat := 118140960795 + 3267531 * 2 ^ 59
def prefixEnd_3267531 : Nat := 4983230072969 + 3 ^ 40 * 3267531 * 2
def baseEnd_3267531 : Nat := 1677813956466360503635405

theorem tailTrace_3267531 : CollatzResearch.WordTrace tailWord_3267531 prefixEnd_3267531 1677813956466360503635405 := by
  unfold tailWord_3267531
  simp only [CollatzResearch.WordTrace]
  refine ⟨119176646325300711711290447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79451097550200474474193631 119176646325300711711290447)
  ·
    refine ⟨178764969487951067566935671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119176646325300711711290447 178764969487951067566935671)
    ·
      refine ⟨268147454231926601350403507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178764969487951067566935671 268147454231926601350403507)
      ·
        refine ⟨402221181347889902025605261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268147454231926601350403507 402221181347889902025605261)
        ·
          refine ⟨150832943005458713259601973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402221181347889902025605261 150832943005458713259601973)
          ·
            refine ⟨14140588406761754368087685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150832943005458713259601973 14140588406761754368087685)
            ·
              refine ⟨2651360326267828944016441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14140588406761754368087685 2651360326267828944016441)
              ·
                refine ⟨1988520244700871708012331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651360326267828944016441 1988520244700871708012331)
                ·
                  refine ⟨2982780367051307562018497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988520244700871708012331 2982780367051307562018497)
                  ·
                    refine ⟨2237085275288480671513873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2982780367051307562018497 2237085275288480671513873)
                    ·
                      refine ⟨1677813956466360503635405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237085275288480671513873 1677813956466360503635405)
                      ·
                        rfl

theorem cell23_3267531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 2, 2].length) (baseStart_3267531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267531 prefixEnd_3267531 := by exact prefixLift 3267531
  have htrace : WordTrace (prefixWord ++ tailWord_3267531) baseStart_3267531 baseEnd_3267531 := by
    simpa [prefixWord, tailWord_3267531, baseEnd_3267531] using wordTrace_append hprefix tailTrace_3267531
  have hstable : (prefixWord ++ tailWord_3267531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267531).length < 2 ^ (prefixWord ++ tailWord_3267531).sum := by decide
  have hdescent : baseEnd_3267531 < baseStart_3267531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267553 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_3267553 : Nat := 118140960795 + 3267553 * 2 ^ 59
def prefixEnd_3267553 : Nat := 4983230072969 + 3 ^ 40 * 3267553 * 2
def baseEnd_3267553 : Nat := 1677825253040759417560303

theorem tailTrace_3267553 : CollatzResearch.WordTrace tailWord_3267553 prefixEnd_3267553 1677825253040759417560303 := by
  unfold tailWord_3267553
  simp only [CollatzResearch.WordTrace]
  refine ⟨119177448731221009468591313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79451632487480672979060875 119177448731221009468591313)
  ·
    refine ⟨89383086548415757101443485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119177448731221009468591313 89383086548415757101443485)
    ·
      refine ⟨33518657455655908913041307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89383086548415757101443485 33518657455655908913041307)
      ·
        refine ⟨50277986183483863369561961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33518657455655908913041307 50277986183483863369561961)
        ·
          refine ⟨37708489637612897527171471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50277986183483863369561961 37708489637612897527171471)
          ·
            refine ⟨56562734456419346290757207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37708489637612897527171471 56562734456419346290757207)
            ·
              refine ⟨84844101684629019436135811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56562734456419346290757207 84844101684629019436135811)
              ·
                refine ⟨127266152526943529154203717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84844101684629019436135811 127266152526943529154203717)
                ·
                  refine ⟨23862403598801911716413197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127266152526943529154203717 23862403598801911716413197)
                  ·
                    refine ⟨8948401349550716893654949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23862403598801911716413197 8948401349550716893654949)
                    ·
                      refine ⟨1677825253040759417560303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8948401349550716893654949 1677825253040759417560303)
                      ·
                        rfl

theorem cell23_3267553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_3267553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267553 prefixEnd_3267553 := by exact prefixLift 3267553
  have htrace : WordTrace (prefixWord ++ tailWord_3267553) baseStart_3267553 baseEnd_3267553 := by
    simpa [prefixWord, tailWord_3267553, baseEnd_3267553] using wordTrace_append hprefix tailTrace_3267553
  have hstable : (prefixWord ++ tailWord_3267553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267553).length < 2 ^ (prefixWord ++ tailWord_3267553).sum := by decide
  have hdescent : baseEnd_3267553 < baseStart_3267553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267640 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_3267640 : Nat := 118140960795 + 3267640 * 2 ^ 59
def prefixEnd_3267640 : Nat := 4983230072969 + 3 ^ 40 * 3267640 * 2
def baseEnd_3267640 : Nat := 559289975285900192390801

theorem tailTrace_3267640 : CollatzResearch.WordTrace tailWord_3267640 prefixEnd_3267640 559289975285900192390801 := by
  unfold tailWord_3267640
  simp only [CollatzResearch.WordTrace]
  refine ⟨59590310940952911663504187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79453747921270548884672249 59590310940952911663504187)
  ·
    refine ⟨89385466411429367495256281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59590310940952911663504187 89385466411429367495256281)
    ·
      refine ⟨67039099808572025621442211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89385466411429367495256281 67039099808572025621442211)
      ·
        refine ⟨100558649712858038432163317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67039099808572025621442211 100558649712858038432163317)
        ·
          refine ⟨9427373410580441103015311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100558649712858038432163317 9427373410580441103015311)
          ·
            refine ⟨14141060115870661654522967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427373410580441103015311 14141060115870661654522967)
            ·
              refine ⟨21211590173805992481784451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14141060115870661654522967 21211590173805992481784451)
              ·
                refine ⟨31817385260708988722676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21211590173805992481784451 31817385260708988722676677)
                ·
                  refine ⟨5965759736382935385501877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31817385260708988722676677 5965759736382935385501877)
                  ·
                    refine ⟨559289975285900192390801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5965759736382935385501877 559289975285900192390801)
                    ·
                      rfl

theorem cell23_3267640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_3267640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267640 prefixEnd_3267640 := by exact prefixLift 3267640
  have htrace : WordTrace (prefixWord ++ tailWord_3267640) baseStart_3267640 baseEnd_3267640 := by
    simpa [prefixWord, tailWord_3267640, baseEnd_3267640] using wordTrace_append hprefix tailTrace_3267640
  have hstable : (prefixWord ++ tailWord_3267640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267640).length < 2 ^ (prefixWord ++ tailWord_3267640).sum := by decide
  have hdescent : baseEnd_3267640 < baseStart_3267640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267644 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 5]
def baseStart_3267644 : Nat := 118140960795 + 3267644 * 2 ^ 59
def prefixEnd_3267644 : Nat := 4983230072969 + 3 ^ 40 * 3267644 * 2
def baseEnd_3267644 : Nat := 186430219975590951280265

theorem tailTrace_3267644 : CollatzResearch.WordTrace tailWord_3267644 prefixEnd_3267644 186430219975590951280265 := by
  unfold tailWord_3267644
  simp only [CollatzResearch.WordTrace]
  refine ⟨59590383886945666005076993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79453845182594221340102657 59590383886945666005076993)
  ·
    refine ⟨44692787915209249503807745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59590383886945666005076993 44692787915209249503807745)
    ·
      refine ⟨33519590936406937127855809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44692787915209249503807745 33519590936406937127855809)
      ·
        refine ⟨25139693202305202845891857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33519590936406937127855809 25139693202305202845891857)
        ·
          refine ⟨18854769901728902134418893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25139693202305202845891857 18854769901728902134418893)
          ·
            refine ⟨7070538713148338300407085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18854769901728902134418893 7070538713148338300407085)
            ·
              refine ⟨2651452017430626862652657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7070538713148338300407085 2651452017430626862652657)
              ·
                refine ⟨1988589013072970146989493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651452017430626862652657 1988589013072970146989493)
                ·
                  refine ⟨186430219975590951280265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1988589013072970146989493 186430219975590951280265)
                  ·
                    rfl

theorem cell23_3267644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_3267644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267644 prefixEnd_3267644 := by exact prefixLift 3267644
  have htrace : WordTrace (prefixWord ++ tailWord_3267644) baseStart_3267644 baseEnd_3267644 := by
    simpa [prefixWord, tailWord_3267644, baseEnd_3267644] using wordTrace_append hprefix tailTrace_3267644
  have hstable : (prefixWord ++ tailWord_3267644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267644).length < 2 ^ (prefixWord ++ tailWord_3267644).sum := by decide
  have hdescent : baseEnd_3267644 < baseStart_3267644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267660 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3267660 : Nat := 118140960795 + 3267660 * 2 ^ 59
def prefixEnd_3267660 : Nat := 4983230072969 + 3 ^ 40 * 3267660 * 2
def baseEnd_3267660 : Nat := 1677880195470790498922311

theorem tailTrace_3267660 : CollatzResearch.WordTrace tailWord_3267660 prefixEnd_3267660 1677880195470790498922311 := by
  unfold tailWord_3267660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59590675670916683371368217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79454234227888911161824289 59590675670916683371368217)
  ·
    refine ⟨44693006753187512528526163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59590675670916683371368217 44693006753187512528526163)
    ·
      refine ⟨67039510129781268792789245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44693006753187512528526163 67039510129781268792789245)
      ·
        refine ⟨25139816298667975797295967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67039510129781268792789245 25139816298667975797295967)
        ·
          refine ⟨37709724448001963695943951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25139816298667975797295967 37709724448001963695943951)
          ·
            refine ⟨56564586672002945543915927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37709724448001963695943951 56564586672002945543915927)
            ·
              refine ⟨84846880008004418315873891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56564586672002945543915927 84846880008004418315873891)
              ·
                refine ⟨127270320012006627473810837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84846880008004418315873891 127270320012006627473810837)
                ·
                  refine ⟨5965796250562810662834883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127270320012006627473810837 5965796250562810662834883)
                  ·
                    refine ⟨8948694375844215994252325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5965796250562810662834883 8948694375844215994252325)
                    ·
                      refine ⟨1677880195470790498922311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8948694375844215994252325 1677880195470790498922311)
                      ·
                        rfl

theorem cell23_3267660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3267660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267660 prefixEnd_3267660 := by exact prefixLift 3267660
  have htrace : WordTrace (prefixWord ++ tailWord_3267660) baseStart_3267660 baseEnd_3267660 := by
    simpa [prefixWord, tailWord_3267660, baseEnd_3267660] using wordTrace_append hprefix tailTrace_3267660
  have hstable : (prefixWord ++ tailWord_3267660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267660).length < 2 ^ (prefixWord ++ tailWord_3267660).sum := by decide
  have hdescent : baseEnd_3267660 < baseStart_3267660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267761 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3267761 : Nat := 118140960795 + 3267761 * 2 ^ 59
def prefixEnd_3267761 : Nat := 4983230072969 + 3 ^ 40 * 3267761 * 2
def baseEnd_3267761 : Nat := 1677932057016894603759347

theorem tailTrace_3267761 : CollatzResearch.WordTrace tailWord_3267761 prefixEnd_3267761 1677932057016894603759347 := by
  unfold tailWord_3267761
  simp only [CollatzResearch.WordTrace]
  refine ⟨119185035114467460992163137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79456690076311640661442091 119185035114467460992163137)
  ·
    refine ⟨89388776335850595744122353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119185035114467460992163137 89388776335850595744122353)
    ·
      refine ⟨67041582251887946808091765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89388776335850595744122353 67041582251887946808091765)
      ·
        refine ⟨6285148336114495013258603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67041582251887946808091765 6285148336114495013258603)
        ·
          refine ⟨9427722504171742519887905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285148336114495013258603 9427722504171742519887905)
          ·
            refine ⟨7070791878128806889915929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9427722504171742519887905 7070791878128806889915929)
            ·
              refine ⟨5303093908596605167436947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7070791878128806889915929 5303093908596605167436947)
              ·
                refine ⟨7954640862894907751155421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303093908596605167436947 7954640862894907751155421)
                ·
                  refine ⟨2982990323585590406683283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7954640862894907751155421 2982990323585590406683283)
                  ·
                    refine ⟨4474485485378385610024925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982990323585590406683283 4474485485378385610024925)
                    ·
                      refine ⟨1677932057016894603759347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474485485378385610024925 1677932057016894603759347)
                      ·
                        rfl

theorem cell23_3267761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3267761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267761 prefixEnd_3267761 := by exact prefixLift 3267761
  have htrace : WordTrace (prefixWord ++ tailWord_3267761) baseStart_3267761 baseEnd_3267761 := by
    simpa [prefixWord, tailWord_3267761, baseEnd_3267761] using wordTrace_append hprefix tailTrace_3267761
  have hstable : (prefixWord ++ tailWord_3267761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267761).length < 2 ^ (prefixWord ++ tailWord_3267761).sum := by decide
  have hdescent : baseEnd_3267761 < baseStart_3267761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267818 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_3267818 : Nat := 118140960795 + 3267818 * 2 ^ 59
def prefixEnd_3267818 : Nat := 4983230072969 + 3 ^ 40 * 3267818 * 2
def baseEnd_3267818 : Nat := 1677961325414200880746585

theorem tailTrace_3267818 : CollatzResearch.WordTrace tailWord_3267818 prefixEnd_3267818 1677961325414200880746585 := by
  unfold tailWord_3267818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29796778518815239931747027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79458076050173973151325405 29796778518815239931747027)
  ·
    refine ⟨44695167778222859897620541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29796778518815239931747027 44695167778222859897620541)
    ·
      refine ⟨16760687916833572461607703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44695167778222859897620541 16760687916833572461607703)
      ·
        refine ⟨25141031875250358692411555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16760687916833572461607703 25141031875250358692411555)
        ·
          refine ⟨37711547812875538038617333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25141031875250358692411555 37711547812875538038617333)
          ·
            refine ⟨3535457607457081691120375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37711547812875538038617333 3535457607457081691120375)
            ·
              refine ⟨5303186411185622536680563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535457607457081691120375 5303186411185622536680563)
              ·
                refine ⟨7954779616778433805020845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303186411185622536680563 7954779616778433805020845)
                ·
                  refine ⟨2983042356291912676882817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7954779616778433805020845 2983042356291912676882817)
                  ·
                    refine ⟨2237281767218934507662113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983042356291912676882817 2237281767218934507662113)
                    ·
                      refine ⟨1677961325414200880746585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237281767218934507662113 1677961325414200880746585)
                      ·
                        rfl

theorem cell23_3267818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_3267818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267818 prefixEnd_3267818 := by exact prefixLift 3267818
  have htrace : WordTrace (prefixWord ++ tailWord_3267818) baseStart_3267818 baseEnd_3267818 := by
    simpa [prefixWord, tailWord_3267818, baseEnd_3267818] using wordTrace_append hprefix tailTrace_3267818
  have hstable : (prefixWord ++ tailWord_3267818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267818).length < 2 ^ (prefixWord ++ tailWord_3267818).sum := by decide
  have hdescent : baseEnd_3267818 < baseStart_3267818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267838 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3267838 : Nat := 118140960795 + 3267838 * 2 ^ 59
def prefixEnd_3267838 : Nat := 4983230072969 + 3 ^ 40 * 3267838 * 2
def baseEnd_3267838 : Nat := 1677971595027290802496493

theorem tailTrace_3267838 : CollatzResearch.WordTrace tailWord_3267838 prefixEnd_3267838 1677971595027290802496493 := by
  unfold tailWord_3267838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14898480441898562892839521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79458562356792335428477445 14898480441898562892839521)
  ·
    refine ⟨11173860331423922169629641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14898480441898562892839521 11173860331423922169629641)
    ·
      refine ⟨8380395248567941627222231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11173860331423922169629641 8380395248567941627222231)
      ·
        refine ⟨12570592872851912440833347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8380395248567941627222231 12570592872851912440833347)
        ·
          refine ⟨18855889309277868661250021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12570592872851912440833347 18855889309277868661250021)
          ·
            refine ⟨3535479245489600373984379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18855889309277868661250021 3535479245489600373984379)
            ·
              refine ⟨5303218868234400560976569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535479245489600373984379 5303218868234400560976569)
              ·
                refine ⟨3977414151175800420732427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303218868234400560976569 3977414151175800420732427)
                ·
                  refine ⟨5966121226763700631098641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977414151175800420732427 5966121226763700631098641)
                  ·
                    refine ⟨4474590920072775473323981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5966121226763700631098641 4474590920072775473323981)
                    ·
                      refine ⟨1677971595027290802496493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474590920072775473323981 1677971595027290802496493)
                      ·
                        rfl

theorem cell23_3267838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3267838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267838 prefixEnd_3267838 := by exact prefixLift 3267838
  have htrace : WordTrace (prefixWord ++ tailWord_3267838) baseStart_3267838 baseEnd_3267838 := by
    simpa [prefixWord, tailWord_3267838, baseEnd_3267838] using wordTrace_append hprefix tailTrace_3267838
  have hstable : (prefixWord ++ tailWord_3267838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267838).length < 2 ^ (prefixWord ++ tailWord_3267838).sum := by decide
  have hdescent : baseEnd_3267838 < baseStart_3267838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267840 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_3267840 : Nat := 118140960795 + 3267840 * 2 ^ 59
def prefixEnd_3267840 : Nat := 4983230072969 + 3 ^ 40 * 3267840 * 2
def baseEnd_3267840 : Nat := 1677972621988599794671483

theorem tailTrace_3267840 : CollatzResearch.WordTrace tailWord_3267840 prefixEnd_3267840 1677972621988599794671483 := by
  unfold tailWord_3267840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59593958240590628742144487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79458610987454171656192649 59593958240590628742144487)
  ·
    refine ⟨89390937360885943113216731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59593958240590628742144487 89390937360885943113216731)
    ·
      refine ⟨134086406041328914669825097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89390937360885943113216731 134086406041328914669825097)
      ·
        refine ⟨100564804530996686002368823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134086406041328914669825097 100564804530996686002368823)
        ·
          refine ⟨150847206796495029003553235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100564804530996686002368823 150847206796495029003553235)
          ·
            refine ⟨226270810194742543505329853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150847206796495029003553235 226270810194742543505329853)
            ·
              refine ⟨84851553823028453814498695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226270810194742543505329853 84851553823028453814498695)
              ·
                refine ⟨127277330734542680721748043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84851553823028453814498695 127277330734542680721748043)
                ·
                  refine ⟨190915996101814021082622065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127277330734542680721748043 190915996101814021082622065)
                  ·
                    refine ⟨143186997076360515811966549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190915996101814021082622065 143186997076360515811966549)
                    ·
                      refine ⟨1677972621988599794671483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 143186997076360515811966549 1677972621988599794671483)
                      ·
                        rfl

theorem cell23_3267840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_3267840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267840 prefixEnd_3267840 := by exact prefixLift 3267840
  have htrace : WordTrace (prefixWord ++ tailWord_3267840) baseStart_3267840 baseEnd_3267840 := by
    simpa [prefixWord, tailWord_3267840, baseEnd_3267840] using wordTrace_append hprefix tailTrace_3267840
  have hstable : (prefixWord ++ tailWord_3267840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267840).length < 2 ^ (prefixWord ++ tailWord_3267840).sum := by decide
  have hdescent : baseEnd_3267840 < baseStart_3267840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267891 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 1, 4, 2]
def baseStart_3267891 : Nat := 118140960795 + 3267891 * 2 ^ 59
def prefixEnd_3267891 : Nat := 4983230072969 + 3 ^ 40 * 3267891 * 2
def baseEnd_3267891 : Nat := 1677998809501979095133749

theorem tailTrace_3267891 : CollatzResearch.WordTrace tailWord_3267891 prefixEnd_3267891 1677998809501979095133749 := by
  unfold tailWord_3267891
  simp only [CollatzResearch.WordTrace]
  refine ⟨119189776603996493194395527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79459851069330995462930351 119189776603996493194395527)
  ·
    refine ⟨178784664905994739791593291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119189776603996493194395527 178784664905994739791593291)
    ·
      refine ⟨268176997358992109687389937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178784664905994739791593291 268176997358992109687389937)
      ·
        refine ⟨201132748019244082265542453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268176997358992109687389937 201132748019244082265542453)
        ·
          refine ⟨18856195126804132712394605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201132748019244082265542453 18856195126804132712394605)
          ·
            refine ⟨7071073172551549767147977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18856195126804132712394605 7071073172551549767147977)
            ·
              refine ⟨5303304879413662325360983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071073172551549767147977 5303304879413662325360983)
              ·
                refine ⟨7954957319120493488041475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303304879413662325360983 7954957319120493488041475)
                ·
                  refine ⟨11932435978680740232062213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7954957319120493488041475 11932435978680740232062213)
                  ·
                    refine ⟨2237331746002638793511665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11932435978680740232062213 2237331746002638793511665)
                    ·
                      refine ⟨1677998809501979095133749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237331746002638793511665 1677998809501979095133749)
                      ·
                        rfl

theorem cell23_3267891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 4, 2].length) (baseStart_3267891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267891 prefixEnd_3267891 := by exact prefixLift 3267891
  have htrace : WordTrace (prefixWord ++ tailWord_3267891) baseStart_3267891 baseEnd_3267891 := by
    simpa [prefixWord, tailWord_3267891, baseEnd_3267891] using wordTrace_append hprefix tailTrace_3267891
  have hstable : (prefixWord ++ tailWord_3267891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267891).length < 2 ^ (prefixWord ++ tailWord_3267891).sum := by decide
  have hdescent : baseEnd_3267891 < baseStart_3267891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267907 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3]
def baseStart_3267907 : Nat := 118140960795 + 3267907 * 2 ^ 59
def prefixEnd_3267907 : Nat := 4983230072969 + 3 ^ 40 * 3267907 * 2
def baseEnd_3267907 : Nat := 1678007025192451032533675

theorem tailTrace_3267907 : CollatzResearch.WordTrace tailWord_3267907 prefixEnd_3267907 1678007025192451032533675 := by
  unfold tailWord_3267907
  simp only [CollatzResearch.WordTrace]
  refine ⟨119190360171938527926977975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79460240114625685284651983 119190360171938527926977975)
  ·
    refine ⟨178785540257907791890466963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119190360171938527926977975 178785540257907791890466963)
    ·
      refine ⟨268178310386861687835700445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178785540257907791890466963 268178310386861687835700445)
      ·
        refine ⟨100566866395073132938387667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268178310386861687835700445 100566866395073132938387667)
        ·
          refine ⟨150850299592609699407581501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100566866395073132938387667 150850299592609699407581501)
          ·
            refine ⟨56568862347228637277843063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150850299592609699407581501 56568862347228637277843063)
            ·
              refine ⟨84853293520842955916764595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56568862347228637277843063 84853293520842955916764595)
              ·
                refine ⟨127279940281264433875146893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84853293520842955916764595 127279940281264433875146893)
                ·
                  refine ⟨47729977605474162703180085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127279940281264433875146893 47729977605474162703180085)
                  ·
                    refine ⟨4474685400513202753423133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47729977605474162703180085 4474685400513202753423133)
                    ·
                      refine ⟨1678007025192451032533675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474685400513202753423133 1678007025192451032533675)
                      ·
                        rfl

theorem cell23_3267907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_3267907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267907 prefixEnd_3267907 := by exact prefixLift 3267907
  have htrace : WordTrace (prefixWord ++ tailWord_3267907) baseStart_3267907 baseEnd_3267907 := by
    simpa [prefixWord, tailWord_3267907, baseEnd_3267907] using wordTrace_append hprefix tailTrace_3267907
  have hstable : (prefixWord ++ tailWord_3267907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267907).length < 2 ^ (prefixWord ++ tailWord_3267907).sum := by decide
  have hdescent : baseEnd_3267907 < baseStart_3267907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267908 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3267908 : Nat := 118140960795 + 3267908 * 2 ^ 59
def prefixEnd_3267908 : Nat := 4983230072969 + 3 ^ 40 * 3267908 * 2
def baseEnd_3267908 : Nat := 1678007538673105528621171

theorem tailTrace_3267908 : CollatzResearch.WordTrace tailWord_3267908 prefixEnd_3267908 1678007538673105528621171 := by
  unfold tailWord_3267908
  simp only [CollatzResearch.WordTrace]
  refine ⟨59595198322467452548882189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79460264429956603398509585 59595198322467452548882189)
  ·
    refine ⟨22348199370925294705830821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59595198322467452548882189 22348199370925294705830821)
    ·
      refine ⟨4190287382048492757343279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22348199370925294705830821 4190287382048492757343279)
      ·
        refine ⟨6285431073072739136014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190287382048492757343279 6285431073072739136014919)
        ·
          refine ⟨9428146609609108704022379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285431073072739136014919 9428146609609108704022379)
          ·
            refine ⟨14142219914413663056033569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9428146609609108704022379 14142219914413663056033569)
            ·
              refine ⟨10606664935810247292025177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14142219914413663056033569 10606664935810247292025177)
              ·
                refine ⟨7954998701857685469018883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10606664935810247292025177 7954998701857685469018883)
                ·
                  refine ⟨11932498052786528203528325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7954998701857685469018883 11932498052786528203528325)
                  ·
                    refine ⟨2237343384897474038161561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11932498052786528203528325 2237343384897474038161561)
                    ·
                      refine ⟨1678007538673105528621171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237343384897474038161561 1678007538673105528621171)
                      ·
                        rfl

theorem cell23_3267908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3267908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267908 prefixEnd_3267908 := by exact prefixLift 3267908
  have htrace : WordTrace (prefixWord ++ tailWord_3267908) baseStart_3267908 baseEnd_3267908 := by
    simpa [prefixWord, tailWord_3267908, baseEnd_3267908] using wordTrace_append hprefix tailTrace_3267908
  have hstable : (prefixWord ++ tailWord_3267908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267908).length < 2 ^ (prefixWord ++ tailWord_3267908).sum := by decide
  have hdescent : baseEnd_3267908 < baseStart_3267908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267924 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_3267924 : Nat := 118140960795 + 3267924 * 2 ^ 59
def prefixEnd_3267924 : Nat := 4983230072969 + 3 ^ 40 * 3267924 * 2
def baseEnd_3267924 : Nat := 1678015754363577466021097

theorem tailTrace_3267924 : CollatzResearch.WordTrace tailWord_3267924 prefixEnd_3267924 1678015754363577466021097 := by
  unfold tailWord_3267924
  simp only [CollatzResearch.WordTrace]
  refine ⟨59595490106438469915173413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79460653475251293220231217 59595490106438469915173413)
  ·
    refine ⟨11174154394957213109095015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59595490106438469915173413 11174154394957213109095015)
    ·
      refine ⟨16761231592435819663642523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11174154394957213109095015 16761231592435819663642523)
      ·
        refine ⟨25141847388653729495463785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16761231592435819663642523 25141847388653729495463785)
        ·
          refine ⟨18856385541490297121597839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25141847388653729495463785 18856385541490297121597839)
          ·
            refine ⟨28284578312235445682396759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18856385541490297121597839 28284578312235445682396759)
            ·
              refine ⟨42426867468353168523595139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28284578312235445682396759 42426867468353168523595139)
              ·
                refine ⟨63640301202529752785392709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42426867468353168523595139 63640301202529752785392709)
                ·
                  refine ⟨11932556475474328647261133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63640301202529752785392709 11932556475474328647261133)
                  ·
                    refine ⟨4474708678302873242722925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11932556475474328647261133 4474708678302873242722925)
                    ·
                      refine ⟨1678015754363577466021097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474708678302873242722925 1678015754363577466021097)
                      ·
                        rfl

theorem cell23_3267924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_3267924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267924 prefixEnd_3267924 := by exact prefixLift 3267924
  have htrace : WordTrace (prefixWord ++ tailWord_3267924) baseStart_3267924 baseEnd_3267924 := by
    simpa [prefixWord, tailWord_3267924, baseEnd_3267924] using wordTrace_append hprefix tailTrace_3267924
  have hstable : (prefixWord ++ tailWord_3267924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267924).length < 2 ^ (prefixWord ++ tailWord_3267924).sum := by decide
  have hdescent : baseEnd_3267924 < baseStart_3267924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267925 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3267925 : Nat := 118140960795 + 3267925 * 2 ^ 59
def prefixEnd_3267925 : Nat := 4983230072969 + 3 ^ 40 * 3267925 * 2
def baseEnd_3267925 : Nat := 1678016267844231962108593

theorem tailTrace_3267925 : CollatzResearch.WordTrace tailWord_3267925 prefixEnd_3267925 1678016267844231962108593 := by
  unfold tailWord_3267925
  simp only [CollatzResearch.WordTrace]
  refine ⟨119191016685873317001133229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79460677790582211334088819 119191016685873317001133229)
  ·
    refine ⟨44696631257202493875424961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119191016685873317001133229 44696631257202493875424961)
    ·
      refine ⟨33522473442901870406568721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44696631257202493875424961 33522473442901870406568721)
      ·
        refine ⟨25141855082176402804926541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33522473442901870406568721 25141855082176402804926541)
        ·
          refine ⟨9428195655816151051847453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25141855082176402804926541 9428195655816151051847453)
          ·
            refine ⟨3535573370931056644442795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9428195655816151051847453 3535573370931056644442795)
            ·
              refine ⟨5303360056396584966664193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535573370931056644442795 5303360056396584966664193)
              ·
                refine ⟨3977520042297438724998145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303360056396584966664193 3977520042297438724998145)
                ·
                  refine ⟨2983140031723079043748609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3977520042297438724998145 2983140031723079043748609)
                  ·
                    refine ⟨2237355023792309282811457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983140031723079043748609 2237355023792309282811457)
                    ·
                      refine ⟨1678016267844231962108593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237355023792309282811457 1678016267844231962108593)
                      ·
                        rfl

theorem cell23_3267925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3267925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267925 prefixEnd_3267925 := by exact prefixLift 3267925
  have htrace : WordTrace (prefixWord ++ tailWord_3267925) baseStart_3267925 baseEnd_3267925 := by
    simpa [prefixWord, tailWord_3267925, baseEnd_3267925] using wordTrace_append hprefix tailTrace_3267925
  have hstable : (prefixWord ++ tailWord_3267925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267925).length < 2 ^ (prefixWord ++ tailWord_3267925).sum := by decide
  have hdescent : baseEnd_3267925 < baseStart_3267925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267937 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_3267937 : Nat := 118140960795 + 3267937 * 2 ^ 59
def prefixEnd_3267937 : Nat := 4983230072969 + 3 ^ 40 * 3267937 * 2
def baseEnd_3267937 : Nat := 1678022429612085915158537

theorem tailTrace_3267937 : CollatzResearch.WordTrace tailWord_3267937 prefixEnd_3267937 1678022429612085915158537 := by
  unfold tailWord_3267937
  simp only [CollatzResearch.WordTrace]
  refine ⟨119191454361829843050570065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79460969574553228700380043 119191454361829843050570065)
  ·
    refine ⟨89393590771372382287927549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119191454361829843050570065 89393590771372382287927549)
    ·
      refine ⟨33522596539264643357972831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89393590771372382287927549 33522596539264643357972831)
      ·
        refine ⟨50283894808896965036959247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33522596539264643357972831 50283894808896965036959247)
        ·
          refine ⟨75425842213345447555438871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50283894808896965036959247 75425842213345447555438871)
          ·
            refine ⟨113138763320018171333158307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75425842213345447555438871 113138763320018171333158307)
            ·
              refine ⟨169708144980027256999737461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113138763320018171333158307 169708144980027256999737461)
              ·
                refine ⟨15910138591877555343725387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169708144980027256999737461 15910138591877555343725387)
                ·
                  refine ⟨23865207887816333015588081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15910138591877555343725387 23865207887816333015588081)
                  ·
                    refine ⟨17898905915862249761691061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23865207887816333015588081 17898905915862249761691061)
                    ·
                      refine ⟨1678022429612085915158537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17898905915862249761691061 1678022429612085915158537)
                      ·
                        rfl

theorem cell23_3267937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_3267937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267937 prefixEnd_3267937 := by exact prefixLift 3267937
  have htrace : WordTrace (prefixWord ++ tailWord_3267937) baseStart_3267937 baseEnd_3267937 := by
    simpa [prefixWord, tailWord_3267937, baseEnd_3267937] using wordTrace_append hprefix tailTrace_3267937
  have hstable : (prefixWord ++ tailWord_3267937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267937).length < 2 ^ (prefixWord ++ tailWord_3267937).sum := by decide
  have hdescent : baseEnd_3267937 < baseStart_3267937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267964 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3267964 : Nat := 118140960795 + 3267964 * 2 ^ 59
def prefixEnd_3267964 : Nat := 4983230072969 + 3 ^ 40 * 3267964 * 2
def baseEnd_3267964 : Nat := 1678036293589757309520913

theorem tailTrace_3267964 : CollatzResearch.WordTrace tailWord_3267964 prefixEnd_3267964 1678036293589757309520913 := by
  unfold tailWord_3267964
  simp only [CollatzResearch.WordTrace]
  refine ⟨59596219566366013330901473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79461626088488017774535297 59596219566366013330901473)
  ·
    refine ⟨44697164674774509998176105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59596219566366013330901473 44697164674774509998176105)
    ·
      refine ⟨33522873506080882498632079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44697164674774509998176105 33522873506080882498632079)
      ·
        refine ⟨50284310259121323747948119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33522873506080882498632079 50284310259121323747948119)
        ·
          refine ⟨75426465388681985621922179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50284310259121323747948119 75426465388681985621922179)
          ·
            refine ⟨113139698083022978432883269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75426465388681985621922179 113139698083022978432883269)
            ·
              refine ⟨21213693390566808456165613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113139698083022978432883269 21213693390566808456165613)
              ·
                refine ⟨7955135021462553171062105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21213693390566808456165613 7955135021462553171062105)
                ·
                  refine ⟨5966351266096914878296579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7955135021462553171062105 5966351266096914878296579)
                  ·
                    refine ⟨8949526899145372317444869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966351266096914878296579 8949526899145372317444869)
                    ·
                      refine ⟨1678036293589757309520913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8949526899145372317444869 1678036293589757309520913)
                      ·
                        rfl

theorem cell23_3267964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3267964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3267964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3267964 prefixEnd_3267964 := by exact prefixLift 3267964
  have htrace : WordTrace (prefixWord ++ tailWord_3267964) baseStart_3267964 baseEnd_3267964 := by
    simpa [prefixWord, tailWord_3267964, baseEnd_3267964] using wordTrace_append hprefix tailTrace_3267964
  have hstable : (prefixWord ++ tailWord_3267964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267964).length < 2 ^ (prefixWord ++ tailWord_3267964).sum := by decide
  have hdescent : baseEnd_3267964 < baseStart_3267964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268048 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 1, 1, 3]
def baseStart_3268048 : Nat := 118140960795 + 3268048 * 2 ^ 59
def prefixEnd_3268048 : Nat := 4983230072969 + 3 ^ 40 * 3268048 * 2
def baseEnd_3268048 : Nat := 1678079425964734980870527

theorem tailTrace_3268048 : CollatzResearch.WordTrace tailWord_3268048 prefixEnd_3268048 1678079425964734980870527 := by
  unfold tailWord_3268048
  simp only [CollatzResearch.WordTrace]
  refine ⟨59597751432213854503930399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79463668576285139338573865 59597751432213854503930399)
  ·
    refine ⟨89396627148320781755895599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59597751432213854503930399 89396627148320781755895599)
    ·
      refine ⟨134094940722481172633843399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89396627148320781755895599 134094940722481172633843399)
      ·
        refine ⟨201142411083721758950765099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134094940722481172633843399 201142411083721758950765099)
        ·
          refine ⟨301713616625582638426147649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201142411083721758950765099 301713616625582638426147649)
          ·
            refine ⟨226285212469186978819610737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301713616625582638426147649 226285212469186978819610737)
            ·
              refine ⟨169713909351890234114708053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226285212469186978819610737 169713909351890234114708053)
              ·
                refine ⟨1988834875217463681031735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 169713909351890234114708053 1988834875217463681031735)
                ·
                  refine ⟨2983252312826195521547603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988834875217463681031735 2983252312826195521547603)
                  ·
                    refine ⟨4474878469239293282321405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983252312826195521547603 4474878469239293282321405)
                    ·
                      refine ⟨1678079425964734980870527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474878469239293282321405 1678079425964734980870527)
                      ·
                        rfl

theorem cell23_3268048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 1, 3].length) (baseStart_3268048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268048 prefixEnd_3268048 := by exact prefixLift 3268048
  have htrace : WordTrace (prefixWord ++ tailWord_3268048) baseStart_3268048 baseEnd_3268048 := by
    simpa [prefixWord, tailWord_3268048, baseEnd_3268048] using wordTrace_append hprefix tailTrace_3268048
  have hstable : (prefixWord ++ tailWord_3268048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268048).length < 2 ^ (prefixWord ++ tailWord_3268048).sum := by decide
  have hdescent : baseEnd_3268048 < baseStart_3268048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268071 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3268071 : Nat := 118140960795 + 3268071 * 2 ^ 59
def prefixEnd_3268071 : Nat := 4983230072969 + 3 ^ 40 * 3268071 * 2
def baseEnd_3268071 : Nat := 1678091236019788390882921

theorem tailTrace_3268071 : CollatzResearch.WordTrace tailWord_3268071 prefixEnd_3268071 1678091236019788390882921 := by
  unfold tailWord_3268071
  simp only [CollatzResearch.WordTrace]
  refine ⟨119196341743344383935948067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79464227828896255957298711 119196341743344383935948067)
  ·
    refine ⟨178794512615016575903922101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119196341743344383935948067 178794512615016575903922101)
    ·
      refine ⟨16761985557657803990992697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178794512615016575903922101 16761985557657803990992697)
      ·
        refine ⟨12571489168243352993244523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16761985557657803990992697 12571489168243352993244523)
        ·
          refine ⟨18857233752365029489866785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571489168243352993244523 18857233752365029489866785)
          ·
            refine ⟨14142925314273772117400089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18857233752365029489866785 14142925314273772117400089)
            ·
              refine ⟨10607193985705329088050067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14142925314273772117400089 10607193985705329088050067)
              ·
                refine ⟨15910790978557993632075101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10607193985705329088050067 15910790978557993632075101)
                ·
                  refine ⟨5966546616959247612028163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15910790978557993632075101 5966546616959247612028163)
                  ·
                    refine ⟨8949819925438871418042245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966546616959247612028163 8949819925438871418042245)
                    ·
                      refine ⟨1678091236019788390882921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8949819925438871418042245 1678091236019788390882921)
                      ·
                        rfl

theorem cell23_3268071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3268071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268071 prefixEnd_3268071 := by exact prefixLift 3268071
  have htrace : WordTrace (prefixWord ++ tailWord_3268071) baseStart_3268071 baseEnd_3268071 := by
    simpa [prefixWord, tailWord_3268071, baseEnd_3268071] using wordTrace_append hprefix tailTrace_3268071
  have hstable : (prefixWord ++ tailWord_3268071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268071).length < 2 ^ (prefixWord ++ tailWord_3268071).sum := by decide
  have hdescent : baseEnd_3268071 < baseStart_3268071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268082 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3268082 : Nat := 118140960795 + 3268082 * 2 ^ 59
def prefixEnd_3268082 : Nat := 4983230072969 + 3 ^ 40 * 3268082 * 2
def baseEnd_3268082 : Nat := 1678096884306987847845371

theorem tailTrace_3268082 : CollatzResearch.WordTrace tailWord_3268082 prefixEnd_3268082 1678096884306987847845371 := by
  unfold tailWord_3268082
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799185736576133203649625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79464495297536355209732333 29799185736576133203649625)
  ·
    refine ⟨22349389302432099902737219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29799185736576133203649625 22349389302432099902737219)
    ·
      refine ⟨33524083953648149854105829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22349389302432099902737219 33524083953648149854105829)
      ·
        refine ⟨6285765741309028097644843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33524083953648149854105829 6285765741309028097644843)
        ·
          refine ⟨9428648611963542146467265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285765741309028097644843 9428648611963542146467265)
          ·
            refine ⟨7071486458972656609850449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9428648611963542146467265 7071486458972656609850449)
            ·
              refine ⟨5303614844229492457387837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071486458972656609850449 5303614844229492457387837)
              ·
                refine ⟨1988855566586059671520439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5303614844229492457387837 1988855566586059671520439)
                ·
                  refine ⟨2983283349879089507280659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988855566586059671520439 2983283349879089507280659)
                  ·
                    refine ⟨4474925024818634260920989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983283349879089507280659 4474925024818634260920989)
                    ·
                      refine ⟨1678096884306987847845371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474925024818634260920989 1678096884306987847845371)
                      ·
                        rfl

theorem cell23_3268082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3268082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268082 prefixEnd_3268082 := by exact prefixLift 3268082
  have htrace : WordTrace (prefixWord ++ tailWord_3268082) baseStart_3268082 baseEnd_3268082 := by
    simpa [prefixWord, tailWord_3268082, baseEnd_3268082] using wordTrace_append hprefix tailTrace_3268082
  have hstable : (prefixWord ++ tailWord_3268082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268082).length < 2 ^ (prefixWord ++ tailWord_3268082).sum := by decide
  have hdescent : baseEnd_3268082 < baseStart_3268082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268085 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3268085 : Nat := 118140960795 + 3268085 * 2 ^ 59
def prefixEnd_3268085 : Nat := 4983230072969 + 3 ^ 40 * 3268085 * 2
def baseEnd_3268085 : Nat := 559366141582983778702619

theorem tailTrace_3268085 : CollatzResearch.WordTrace tailWord_3268085 prefixEnd_3268085 559366141582983778702619 := by
  unfold tailWord_3268085
  simp only [CollatzResearch.WordTrace]
  refine ⟨119196852365293664326957709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79464568243529109551305139 119196852365293664326957709)
  ·
    refine ⟨44698819636985124122609141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119196852365293664326957709 44698819636985124122609141)
    ·
      refine ⟨4190514340967355386494607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44698819636985124122609141 4190514340967355386494607)
      ·
        refine ⟨6285771511451033079741911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190514340967355386494607 6285771511451033079741911)
        ·
          refine ⟨9428657267176549619612867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285771511451033079741911 9428657267176549619612867)
          ·
            refine ⟨14142985900764824429419301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9428657267176549619612867 14142985900764824429419301)
            ·
              refine ⟨2651809856393404580516119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14142985900764824429419301 2651809856393404580516119)
              ·
                refine ⟨3977714784590106870774179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651809856393404580516119 3977714784590106870774179)
                ·
                  refine ⟨5966572176885160306161269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977714784590106870774179 5966572176885160306161269)
                  ·
                    refine ⟨559366141582983778702619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5966572176885160306161269 559366141582983778702619)
                    ·
                      rfl

theorem cell23_3268085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3268085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268085 prefixEnd_3268085 := by exact prefixLift 3268085
  have htrace : WordTrace (prefixWord ++ tailWord_3268085) baseStart_3268085 baseEnd_3268085 := by
    simpa [prefixWord, tailWord_3268085, baseEnd_3268085] using wordTrace_append hprefix tailTrace_3268085
  have hstable : (prefixWord ++ tailWord_3268085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268085).length < 2 ^ (prefixWord ++ tailWord_3268085).sum := by decide
  have hdescent : baseEnd_3268085 < baseStart_3268085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268088 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_3268088 : Nat := 118140960795 + 3268088 * 2 ^ 59
def prefixEnd_3268088 : Nat := 4983230072969 + 3 ^ 40 * 3268088 * 2
def baseEnd_3268088 : Nat := 1678099965190914824370343

theorem tailTrace_3268088 : CollatzResearch.WordTrace tailWord_3268088 prefixEnd_3268088 1678099965190914824370343 := by
  unfold tailWord_3268088
  simp only [CollatzResearch.WordTrace]
  refine ⟨59598480892141397919658459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79464641189521863892877945 59598480892141397919658459)
  ·
    refine ⟨89397721338212096879487689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59598480892141397919658459 89397721338212096879487689)
    ·
      refine ⟨67048291003659072659615767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89397721338212096879487689 67048291003659072659615767)
      ·
        refine ⟨100572436505488608989423651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67048291003659072659615767 100572436505488608989423651)
        ·
          refine ⟨150858654758232913484135477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100572436505488608989423651 150858654758232913484135477)
          ·
            refine ⟨14142998883584335639137701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150858654758232913484135477 14142998883584335639137701)
            ·
              refine ⟨2651812290672062932338319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14142998883584335639137701 2651812290672062932338319)
              ·
                refine ⟨3977718436008094398507479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651812290672062932338319 3977718436008094398507479)
                ·
                  refine ⟨5966577654012141597761219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977718436008094398507479 5966577654012141597761219)
                  ·
                    refine ⟨8949866481018212396641829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966577654012141597761219 8949866481018212396641829)
                    ·
                      refine ⟨1678099965190914824370343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8949866481018212396641829 1678099965190914824370343)
                      ·
                        rfl

theorem cell23_3268088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_3268088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268088 prefixEnd_3268088 := by exact prefixLift 3268088
  have htrace : WordTrace (prefixWord ++ tailWord_3268088) baseStart_3268088 baseEnd_3268088 := by
    simpa [prefixWord, tailWord_3268088, baseEnd_3268088] using wordTrace_append hprefix tailTrace_3268088
  have hstable : (prefixWord ++ tailWord_3268088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268088).length < 2 ^ (prefixWord ++ tailWord_3268088).sum := by decide
  have hdescent : baseEnd_3268088 < baseStart_3268088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268091 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 3]
def baseStart_3268091 : Nat := 118140960795 + 3268091 * 2 ^ 59
def prefixEnd_3268091 : Nat := 4983230072969 + 3 ^ 40 * 3268091 * 2
def baseEnd_3268091 : Nat := 1678101505632878312632829

theorem tailTrace_3268091 : CollatzResearch.WordTrace tailWord_3268091 prefixEnd_3268091 1678101505632878312632829 := by
  unfold tailWord_3268091
  simp only [CollatzResearch.WordTrace]
  refine ⟨119197071203271927351676127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79464714135514618234450751 119197071203271927351676127)
  ·
    refine ⟨178795606804907891027514191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119197071203271927351676127 178795606804907891027514191)
    ·
      refine ⟨268193410207361836541271287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178795606804907891027514191 268193410207361836541271287)
      ·
        refine ⟨402290115311042754811906931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268193410207361836541271287 402290115311042754811906931)
        ·
          refine ⟨603435172966564132217860397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402290115311042754811906931 603435172966564132217860397)
          ·
            refine ⟨226288189862461549581697649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603435172966564132217860397 226288189862461549581697649)
            ·
              refine ⟨169716142396846162186273237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226288189862461549581697649 169716142396846162186273237)
              ·
                refine ⟨3977722087426081926240779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 169716142396846162186273237 3977722087426081926240779)
                ·
                  refine ⟨5966583131139122889361169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977722087426081926240779 5966583131139122889361169)
                  ·
                    refine ⟨4474937348354342167020877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5966583131139122889361169 4474937348354342167020877)
                    ·
                      refine ⟨1678101505632878312632829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474937348354342167020877 1678101505632878312632829)
                      ·
                        rfl

theorem cell23_3268091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 3].length) (baseStart_3268091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268091 prefixEnd_3268091 := by exact prefixLift 3268091
  have htrace : WordTrace (prefixWord ++ tailWord_3268091) baseStart_3268091 baseEnd_3268091 := by
    simpa [prefixWord, tailWord_3268091, baseEnd_3268091] using wordTrace_append hprefix tailTrace_3268091
  have hstable : (prefixWord ++ tailWord_3268091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268091).length < 2 ^ (prefixWord ++ tailWord_3268091).sum := by decide
  have hdescent : baseEnd_3268091 < baseStart_3268091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268105 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 1, 2, 2]
def baseStart_3268105 : Nat := 118140960795 + 3268105 * 2 ^ 59
def prefixEnd_3268105 : Nat := 4983230072969 + 3 ^ 40 * 3268105 * 2
def baseEnd_3268105 : Nat := 1678108694362041257857765

theorem tailTrace_3268105 : CollatzResearch.WordTrace tailWord_3268105 prefixEnd_3268105 1678108694362041257857765 := by
  unfold tailWord_3268105
  simp only [CollatzResearch.WordTrace]
  refine ⟨119197581825221207742685769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79465054550147471828457179 119197581825221207742685769)
  ·
    refine ⟨89398186368915905807014327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119197581825221207742685769 89398186368915905807014327)
    ·
      refine ⟨134097279553373858710521491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89398186368915905807014327 134097279553373858710521491)
      ·
        refine ⟨201145919330060788065782237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134097279553373858710521491 201145919330060788065782237)
        ·
          refine ⟨75429719748772795524668339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201145919330060788065782237 75429719748772795524668339)
          ·
            refine ⟨113144579623159193287002509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75429719748772795524668339 113144579623159193287002509)
            ·
              refine ⟨42429217358684697482625941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113144579623159193287002509 42429217358684697482625941)
              ·
                refine ⟨1988869563688345194498091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42429217358684697482625941 1988869563688345194498091)
                ·
                  refine ⟨2983304345532517791747137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988869563688345194498091 2983304345532517791747137)
                  ·
                    refine ⟨2237478259149388343810353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983304345532517791747137 2237478259149388343810353)
                    ·
                      refine ⟨1678108694362041257857765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237478259149388343810353 1678108694362041257857765)
                      ·
                        rfl

theorem cell23_3268105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 2, 2].length) (baseStart_3268105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268105 prefixEnd_3268105 := by exact prefixLift 3268105
  have htrace : WordTrace (prefixWord ++ tailWord_3268105) baseStart_3268105 baseEnd_3268105 := by
    simpa [prefixWord, tailWord_3268105, baseEnd_3268105] using wordTrace_append hprefix tailTrace_3268105
  have hstable : (prefixWord ++ tailWord_3268105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268105).length < 2 ^ (prefixWord ++ tailWord_3268105).sum := by decide
  have hdescent : baseEnd_3268105 < baseStart_3268105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268121 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 3]
def baseStart_3268121 : Nat := 118140960795 + 3268121 * 2 ^ 59
def prefixEnd_3268121 : Nat := 4983230072969 + 3 ^ 40 * 3268121 * 2
def baseEnd_3268121 : Nat := 1678116910052513195257691

theorem tailTrace_3268121 : CollatzResearch.WordTrace tailWord_3268121 prefixEnd_3268121 1678116910052513195257691 := by
  unfold tailWord_3268121
  simp only [CollatzResearch.WordTrace]
  refine ⟨119198165393163242475268217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79465443595442161650178811 119198165393163242475268217)
  ·
    refine ⟨89398624044872431856451163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119198165393163242475268217 89398624044872431856451163)
    ·
      refine ⟨134097936067308647784676745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89398624044872431856451163 134097936067308647784676745)
      ·
        refine ⟨100573452050481485838507559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134097936067308647784676745 100573452050481485838507559)
        ·
          refine ⟨150860178075722228757761339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100573452050481485838507559 150860178075722228757761339)
          ·
            refine ⟨226290267113583343136642009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150860178075722228757761339 226290267113583343136642009)
            ·
              refine ⟨169717700335187507352481507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226290267113583343136642009 169717700335187507352481507)
              ·
                refine ⟨254576550502781261028722261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169717700335187507352481507 254576550502781261028722261)
                ·
                  refine ⟨2983318951204467902680339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 254576550502781261028722261 2983318951204467902680339)
                  ·
                    refine ⟨4474978426806701854020509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983318951204467902680339 4474978426806701854020509)
                    ·
                      refine ⟨1678116910052513195257691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4474978426806701854020509 1678116910052513195257691)
                      ·
                        rfl

theorem cell23_3268121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_3268121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268121 prefixEnd_3268121 := by exact prefixLift 3268121
  have htrace : WordTrace (prefixWord ++ tailWord_3268121) baseStart_3268121 baseEnd_3268121 := by
    simpa [prefixWord, tailWord_3268121, baseEnd_3268121] using wordTrace_append hprefix tailTrace_3268121
  have hstable : (prefixWord ++ tailWord_3268121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268121).length < 2 ^ (prefixWord ++ tailWord_3268121).sum := by decide
  have hdescent : baseEnd_3268121 < baseStart_3268121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268128 : List Nat := [2, 1, 1, 6, 1, 3, 2, 7]
def baseStart_3268128 : Nat := 118140960795 + 3268128 * 2 ^ 59
def prefixEnd_3268128 : Nat := 4983230072969 + 3 ^ 40 * 3268128 * 2
def baseEnd_3268128 : Nat := 62152611274707209921117

theorem tailTrace_3268128 : CollatzResearch.WordTrace tailWord_3268128 prefixEnd_3268128 62152611274707209921117 := by
  unfold tailWord_3268128
  simp only [CollatzResearch.WordTrace]
  refine ⟨59599210352068941335386519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79465613802758588447182025 59599210352068941335386519)
  ·
    refine ⟨89398815528103412003079779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59599210352068941335386519 89398815528103412003079779)
    ·
      refine ⟨134098223292155118004619669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89398815528103412003079779 134098223292155118004619669)
      ·
        refine ⟨6285854216819771156466547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134098223292155118004619669 6285854216819771156466547)
        ·
          refine ⟨9428781325229656734699821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285854216819771156466547 9428781325229656734699821)
          ·
            refine ⟨3535792996961121275512433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9428781325229656734699821 3535792996961121275512433)
            ·
              refine ⟨2651844747720840956634325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535792996961121275512433 2651844747720840956634325)
              ·
                refine ⟨62152611274707209921117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2651844747720840956634325 62152611274707209921117)
                ·
                  rfl

theorem cell23_3268128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 7].length) (baseStart_3268128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268128 prefixEnd_3268128 := by exact prefixLift 3268128
  have htrace : WordTrace (prefixWord ++ tailWord_3268128) baseStart_3268128 baseEnd_3268128 := by
    simpa [prefixWord, tailWord_3268128, baseEnd_3268128] using wordTrace_append hprefix tailTrace_3268128
  have hstable : (prefixWord ++ tailWord_3268128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268128).length < 2 ^ (prefixWord ++ tailWord_3268128).sum := by decide
  have hdescent : baseEnd_3268128 < baseStart_3268128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268138 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3268138 : Nat := 118140960795 + 3268138 * 2 ^ 59
def prefixEnd_3268138 : Nat := 4983230072969 + 3 ^ 40 * 3268138 * 2
def baseEnd_3268138 : Nat := 1678125639223639628745113

theorem tailTrace_3268138 : CollatzResearch.WordTrace tailWord_3268138 prefixEnd_3268138 1678125639223639628745113 := by
  unfold tailWord_3268138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799696358525413594659267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79465856956067769585758045 29799696358525413594659267)
  ·
    refine ⟨44699544537788120391988901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29799696358525413594659267 44699544537788120391988901)
    ·
      refine ⟨8381164600835272573497919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44699544537788120391988901 8381164600835272573497919)
      ·
        refine ⟨12571746901252908860246879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381164600835272573497919 12571746901252908860246879)
        ·
          refine ⟨18857620351879363290370319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571746901252908860246879 18857620351879363290370319)
          ·
            refine ⟨28286430527819044935555479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857620351879363290370319 28286430527819044935555479)
            ·
              refine ⟨42429645791728567403333219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28286430527819044935555479 42429645791728567403333219)
              ·
                refine ⟨63644468687592851104999829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42429645791728567403333219 63644468687592851104999829)
                ·
                  refine ⟨2983334469730914895546867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63644468687592851104999829 2983334469730914895546867)
                  ·
                    refine ⟨4475001704596372343320301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983334469730914895546867 4475001704596372343320301)
                    ·
                      refine ⟨1678125639223639628745113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475001704596372343320301 1678125639223639628745113)
                      ·
                        rfl

theorem cell23_3268138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3268138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268138 prefixEnd_3268138 := by exact prefixLift 3268138
  have htrace : WordTrace (prefixWord ++ tailWord_3268138) baseStart_3268138 baseEnd_3268138 := by
    simpa [prefixWord, tailWord_3268138, baseEnd_3268138] using wordTrace_append hprefix tailTrace_3268138
  have hstable : (prefixWord ++ tailWord_3268138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268138).length < 2 ^ (prefixWord ++ tailWord_3268138).sum := by decide
  have hdescent : baseEnd_3268138 < baseStart_3268138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268144 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_3268144 : Nat := 118140960795 + 3268144 * 2 ^ 59
def prefixEnd_3268144 : Nat := 4983230072969 + 3 ^ 40 * 3268144 * 2
def baseEnd_3268144 : Nat := 1678128720107566605270085

theorem tailTrace_3268144 : CollatzResearch.WordTrace tailWord_3268144 prefixEnd_3268144 1678128720107566605270085 := by
  unfold tailWord_3268144
  simp only [CollatzResearch.WordTrace]
  refine ⟨59599502136039958701677743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79466002848053278268903657 59599502136039958701677743)
  ·
    refine ⟨89399253204059938052516615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59599502136039958701677743 89399253204059938052516615)
    ·
      refine ⟨134098879806089907078774923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89399253204059938052516615 134098879806089907078774923)
      ·
        refine ⟨201148319709134860618162385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134098879806089907078774923 201148319709134860618162385)
        ·
          refine ⟨150861239781851145463621789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201148319709134860618162385 150861239781851145463621789)
          ·
            refine ⟨56572964918194179548858171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150861239781851145463621789 56572964918194179548858171)
            ·
              refine ⟨84859447377291269323287257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56572964918194179548858171 84859447377291269323287257)
              ·
                refine ⟨63644585532968451992465443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84859447377291269323287257 63644585532968451992465443)
                ·
                  refine ⟨95466878299452677988698165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63644585532968451992465443 95466878299452677988698165)
                  ·
                    refine ⟨8950019840573688561440453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95466878299452677988698165 8950019840573688561440453)
                    ·
                      refine ⟨1678128720107566605270085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8950019840573688561440453 1678128720107566605270085)
                      ·
                        rfl

theorem cell23_3268144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_3268144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268144 prefixEnd_3268144 := by exact prefixLift 3268144
  have htrace : WordTrace (prefixWord ++ tailWord_3268144) baseStart_3268144 baseEnd_3268144 := by
    simpa [prefixWord, tailWord_3268144, baseEnd_3268144] using wordTrace_append hprefix tailTrace_3268144
  have hstable : (prefixWord ++ tailWord_3268144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268144).length < 2 ^ (prefixWord ++ tailWord_3268144).sum := by decide
  have hdescent : baseEnd_3268144 < baseStart_3268144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268161 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3268161 : Nat := 118140960795 + 3268161 * 2 ^ 59
def prefixEnd_3268161 : Nat := 4983230072969 + 3 ^ 40 * 3268161 * 2
def baseEnd_3268161 : Nat := 1678137449278693038757507

theorem tailTrace_3268161 : CollatzResearch.WordTrace tailWord_3268161 prefixEnd_3268161 1678137449278693038757507 := by
  unfold tailWord_3268161
  simp only [CollatzResearch.WordTrace]
  refine ⟨119199624313018329306724337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79466416208678886204482891 119199624313018329306724337)
  ·
    refine ⟨89399718234763746980043253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119199624313018329306724337 89399718234763746980043253)
    ·
      refine ⟨8381223584509101279379055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89399718234763746980043253 8381223584509101279379055)
      ·
        refine ⟨12571835376763651919068583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381223584509101279379055 12571835376763651919068583)
        ·
          refine ⟨18857753065145477878602875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571835376763651919068583 18857753065145477878602875)
          ·
            refine ⟨28286629597718216817904313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857753065145477878602875 28286629597718216817904313)
            ·
              refine ⟨21214972198288662613428235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28286629597718216817904313 21214972198288662613428235)
              ·
                refine ⟨31822458297432993920142353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21214972198288662613428235 31822458297432993920142353)
                ·
                  refine ⟨23866843723074745440106765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31822458297432993920142353 23866843723074745440106765)
                  ·
                    refine ⟨8950066396153029540040037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23866843723074745440106765 8950066396153029540040037)
                    ·
                      refine ⟨1678137449278693038757507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8950066396153029540040037 1678137449278693038757507)
                      ·
                        rfl

theorem cell23_3268161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3268161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268161 prefixEnd_3268161 := by exact prefixLift 3268161
  have htrace : WordTrace (prefixWord ++ tailWord_3268161) baseStart_3268161 baseEnd_3268161 := by
    simpa [prefixWord, tailWord_3268161, baseEnd_3268161] using wordTrace_append hprefix tailTrace_3268161
  have hstable : (prefixWord ++ tailWord_3268161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268161).length < 2 ^ (prefixWord ++ tailWord_3268161).sum := by decide
  have hdescent : baseEnd_3268161 < baseStart_3268161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268166 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_3268166 : Nat := 118140960795 + 3268166 * 2 ^ 59
def prefixEnd_3268166 : Nat := 4983230072969 + 3 ^ 40 * 3268166 * 2
def baseEnd_3268166 : Nat := 559380005560655173064995

theorem tailTrace_3268166 : CollatzResearch.WordTrace tailWord_3268166 prefixEnd_3268166 559380005560655173064995 := by
  unfold tailWord_3268166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724993958687506723770511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79466537785333476773770901 3724993958687506723770511)
  ·
    refine ⟨5587490938031260085655767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724993958687506723770511 5587490938031260085655767)
    ·
      refine ⟨8381236407046890128483651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587490938031260085655767 8381236407046890128483651)
      ·
        refine ⟨12571854610570335192725477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381236407046890128483651 12571854610570335192725477)
        ·
          refine ⟨2357222739481937848636027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12571854610570335192725477 2357222739481937848636027)
          ·
            refine ⟨3535834109222906772954041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357222739481937848636027 3535834109222906772954041)
            ·
              refine ⟨2651875581917180079715531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535834109222906772954041 2651875581917180079715531)
              ·
                refine ⟨3977813372875770119573297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651875581917180079715531 3977813372875770119573297)
                ·
                  refine ⟨2983360029656827589679973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3977813372875770119573297 2983360029656827589679973)
                  ·
                    refine ⟨559380005560655173064995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983360029656827589679973 559380005560655173064995)
                    ·
                      rfl

theorem cell23_3268166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_3268166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268166 prefixEnd_3268166 := by exact prefixLift 3268166
  have htrace : WordTrace (prefixWord ++ tailWord_3268166) baseStart_3268166 baseEnd_3268166 := by
    simpa [prefixWord, tailWord_3268166, baseEnd_3268166] using wordTrace_append hprefix tailTrace_3268166
  have hstable : (prefixWord ++ tailWord_3268166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268166).length < 2 ^ (prefixWord ++ tailWord_3268166).sum := by decide
  have hdescent : baseEnd_3268166 < baseStart_3268166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268172 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3268172 : Nat := 118140960795 + 3268172 * 2 ^ 59
def prefixEnd_3268172 : Nat := 4983230072969 + 3 ^ 40 * 3268172 * 2
def baseEnd_3268172 : Nat := 1678143097565892495719957

theorem tailTrace_3268172 : CollatzResearch.WordTrace tailWord_3268172 prefixEnd_3268172 1678143097565892495719957 := by
  unfold tailWord_3268172
  simp only [CollatzResearch.WordTrace]
  refine ⟨59600012757989239092687385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79466683677318985456916513 59600012757989239092687385)
  ·
    refine ⟨44700009568491929319515539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59600012757989239092687385 44700009568491929319515539)
    ·
      refine ⟨67050014352737893979273309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44700009568491929319515539 67050014352737893979273309)
      ·
        refine ⟨25143755382276710242227491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67050014352737893979273309 25143755382276710242227491)
        ·
          refine ⟨37715633073415065363341237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25143755382276710242227491 37715633073415065363341237)
          ·
            refine ⟨3535840600632662377813241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37715633073415065363341237 3535840600632662377813241)
            ·
              refine ⟨2651880450474496783359931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535840600632662377813241 2651880450474496783359931)
              ·
                refine ⟨3977820675711745175039897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651880450474496783359931 3977820675711745175039897)
                ·
                  refine ⟨2983365506783808881279923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3977820675711745175039897 2983365506783808881279923)
                  ·
                    refine ⟨4475048260175713321919885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983365506783808881279923 4475048260175713321919885)
                    ·
                      refine ⟨1678143097565892495719957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475048260175713321919885 1678143097565892495719957)
                      ·
                        rfl

theorem cell23_3268172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3268172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268172 prefixEnd_3268172 := by exact prefixLift 3268172
  have htrace : WordTrace (prefixWord ++ tailWord_3268172) baseStart_3268172 baseEnd_3268172 := by
    simpa [prefixWord, tailWord_3268172, baseEnd_3268172] using wordTrace_append hprefix tailTrace_3268172
  have hstable : (prefixWord ++ tailWord_3268172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268172).length < 2 ^ (prefixWord ++ tailWord_3268172).sum := by decide
  have hdescent : baseEnd_3268172 < baseStart_3268172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268184 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 9]
def baseStart_3268184 : Nat := 118140960795 + 3268184 * 2 ^ 59
def prefixEnd_3268184 : Nat := 4983230072969 + 3 ^ 40 * 3268184 * 2
def baseEnd_3268184 : Nat := 186461028814860716529989

theorem tailTrace_3268184 : CollatzResearch.WordTrace tailWord_3268184 prefixEnd_3268184 186461028814860716529989 := by
  unfold tailWord_3268184
  simp only [CollatzResearch.WordTrace]
  refine ⟨59600231595967502117405803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79466975461290002823207737 59600231595967502117405803)
  ·
    refine ⟨89400347393951253176108705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59600231595967502117405803 89400347393951253176108705)
    ·
      refine ⟨67050260545463439882081529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89400347393951253176108705 67050260545463439882081529)
      ·
        refine ⟨50287695409097579911561147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67050260545463439882081529 50287695409097579911561147)
        ·
          refine ⟨75431543113646369867341721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50287695409097579911561147 75431543113646369867341721)
          ·
            refine ⟨56573657335234777400506291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75431543113646369867341721 56573657335234777400506291)
            ·
              refine ⟨84860486002852166100759437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56573657335234777400506291 84860486002852166100759437)
              ·
                refine ⟨31822682251069562287784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84860486002852166100759437 31822682251069562287784789)
                ·
                  refine ⟨186461028814860716529989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31822682251069562287784789 186461028814860716529989)
                  ·
                    rfl

theorem cell23_3268184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_3268184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268184 prefixEnd_3268184 := by exact prefixLift 3268184
  have htrace : WordTrace (prefixWord ++ tailWord_3268184) baseStart_3268184 baseEnd_3268184 := by
    simpa [prefixWord, tailWord_3268184, baseEnd_3268184] using wordTrace_append hprefix tailTrace_3268184
  have hstable : (prefixWord ++ tailWord_3268184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268184).length < 2 ^ (prefixWord ++ tailWord_3268184).sum := by decide
  have hdescent : baseEnd_3268184 < baseStart_3268184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268248 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_3268248 : Nat := 118140960795 + 3268248 * 2 ^ 59
def prefixEnd_3268248 : Nat := 4983230072969 + 3 ^ 40 * 3268248 * 2
def baseEnd_3268248 : Nat := 559394040698544732789869

theorem tailTrace_3268248 : CollatzResearch.WordTrace tailWord_3268248 prefixEnd_3268248 559394040698544732789869 := by
  unfold tailWord_3268248
  simp only [CollatzResearch.WordTrace]
  refine ⟨59601398731851571582570699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79468531642468762110094265 59601398731851571582570699)
  ·
    refine ⟨89402098097777357373856049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59601398731851571582570699 89402098097777357373856049)
    ·
      refine ⟨67051573573333018030392037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89402098097777357373856049 67051573573333018030392037)
      ·
        refine ⟨12572170044999940880698507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67051573573333018030392037 12572170044999940880698507)
        ·
          refine ⟨18858255067499911321047761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12572170044999940880698507 18858255067499911321047761)
          ·
            refine ⟨14143691300624933490785821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18858255067499911321047761 14143691300624933490785821)
            ·
              refine ⟨5303884237734350059044683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14143691300624933490785821 5303884237734350059044683)
              ·
                refine ⟨7955826356601525088567025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303884237734350059044683 7955826356601525088567025)
                ·
                  refine ⟨5966869767451143816425269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7955826356601525088567025 5966869767451143816425269)
                  ·
                    refine ⟨559394040698544732789869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5966869767451143816425269 559394040698544732789869)
                    ·
                      rfl

theorem cell23_3268248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_3268248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268248 prefixEnd_3268248 := by exact prefixLift 3268248
  have htrace : WordTrace (prefixWord ++ tailWord_3268248) baseStart_3268248 baseEnd_3268248 := by
    simpa [prefixWord, tailWord_3268248, baseEnd_3268248] using wordTrace_append hprefix tailTrace_3268248
  have hstable : (prefixWord ++ tailWord_3268248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268248).length < 2 ^ (prefixWord ++ tailWord_3268248).sum := by decide
  have hdescent : baseEnd_3268248 < baseStart_3268248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268308 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3268308 : Nat := 118140960795 + 3268308 * 2 ^ 59
def prefixEnd_3268308 : Nat := 4983230072969 + 3 ^ 40 * 3268308 * 2
def baseEnd_3268308 : Nat := 186468103437211551513259

theorem tailTrace_3268308 : CollatzResearch.WordTrace tailWord_3268308 prefixEnd_3268308 186468103437211551513259 := by
  unfold tailWord_3268308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59602492921742886706162789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79469990562323848941550385 59602492921742886706162789)
  ·
    refine ⟨11175467422826791257405523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59602492921742886706162789 11175467422826791257405523)
    ·
      refine ⟨16763201134240186886108285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11175467422826791257405523 16763201134240186886108285)
      ·
        refine ⟨6286200425340070082290607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16763201134240186886108285 6286200425340070082290607)
        ·
          refine ⟨9429300638010105123435911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286200425340070082290607 9429300638010105123435911)
          ·
            refine ⟨14143950957015157685153867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429300638010105123435911 14143950957015157685153867)
            ·
              refine ⟨21215926435522736527730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14143950957015157685153867 21215926435522736527730801)
              ·
                refine ⟨15911944826642052395798101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21215926435522736527730801 15911944826642052395798101)
                ·
                  refine ⟨186468103437211551513259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15911944826642052395798101 186468103437211551513259)
                  ·
                    rfl

theorem cell23_3268308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3268308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268308 prefixEnd_3268308 := by exact prefixLift 3268308
  have htrace : WordTrace (prefixWord ++ tailWord_3268308) baseStart_3268308 baseEnd_3268308 := by
    simpa [prefixWord, tailWord_3268308, baseEnd_3268308] using wordTrace_append hprefix tailTrace_3268308
  have hstable : (prefixWord ++ tailWord_3268308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268308).length < 2 ^ (prefixWord ++ tailWord_3268308).sum := by decide
  have hdescent : baseEnd_3268308 < baseStart_3268308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268338 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3268338 : Nat := 118140960795 + 3268338 * 2 ^ 59
def prefixEnd_3268338 : Nat := 4983230072969 + 3 ^ 40 * 3268338 * 2
def baseEnd_3268338 : Nat := 559409445118179615414731

theorem tailTrace_3268338 : CollatzResearch.WordTrace tailWord_3268338 prefixEnd_3268338 559409445118179615414731 := by
  unfold tailWord_3268338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29801520008344272133979417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79470720022251392357278445 29801520008344272133979417)
  ·
    refine ⟨22351140006258204100484563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29801520008344272133979417 22351140006258204100484563)
    ·
      refine ⟨33526710009387306150726845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22351140006258204100484563 33526710009387306150726845)
      ·
        refine ⟨12572516253520239806522567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33526710009387306150726845 12572516253520239806522567)
        ·
          refine ⟨18858774380280359709783851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12572516253520239806522567 18858774380280359709783851)
          ·
            refine ⟨28288161570420539564675777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18858774380280359709783851 28288161570420539564675777)
            ·
              refine ⟨21216121177815404673506833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28288161570420539564675777 21216121177815404673506833)
              ·
                refine ⟨15912090883361553505130125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21216121177815404673506833 15912090883361553505130125)
                ·
                  refine ⟨5967034081260582564423797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15912090883361553505130125 5967034081260582564423797)
                  ·
                    refine ⟨559409445118179615414731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5967034081260582564423797 559409445118179615414731)
                    ·
                      rfl

theorem cell23_3268338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3268338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268338 prefixEnd_3268338 := by exact prefixLift 3268338
  have htrace : WordTrace (prefixWord ++ tailWord_3268338) baseStart_3268338 baseEnd_3268338 := by
    simpa [prefixWord, tailWord_3268338, baseEnd_3268338] using wordTrace_append hprefix tailTrace_3268338
  have hstable : (prefixWord ++ tailWord_3268338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268338).length < 2 ^ (prefixWord ++ tailWord_3268338).sum := by decide
  have hdescent : baseEnd_3268338 < baseStart_3268338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268342 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_3268342 : Nat := 118140960795 + 3268342 * 2 ^ 59
def prefixEnd_3268342 : Nat := 4983230072969 + 3 ^ 40 * 3268342 * 2
def baseEnd_3268342 : Nat := 186470043253017425621575

theorem tailTrace_3268342 : CollatzResearch.WordTrace tailWord_3268342 prefixEnd_3268342 186470043253017425621575 := by
  unfold tailWord_3268342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450389120335162326191455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79470817283575064812708853 7450389120335162326191455)
  ·
    refine ⟨11175583680502743489287183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7450389120335162326191455 11175583680502743489287183)
    ·
      refine ⟨16763375520754115233930775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11175583680502743489287183 16763375520754115233930775)
      ·
        refine ⟨25145063281131172850896163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16763375520754115233930775 25145063281131172850896163)
        ·
          refine ⟨37717594921696759276344245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25145063281131172850896163 37717594921696759276344245)
          ·
            refine ⟨3536024523909071182157273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37717594921696759276344245 3536024523909071182157273)
            ·
              refine ⟨2652018392931803386617955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536024523909071182157273 2652018392931803386617955)
              ·
                refine ⟨3978027589397705079926933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652018392931803386617955 3978027589397705079926933)
                ·
                  refine ⟨186470043253017425621575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978027589397705079926933 186470043253017425621575)
                  ·
                    rfl

theorem cell23_3268342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_3268342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268342 prefixEnd_3268342 := by exact prefixLift 3268342
  have htrace : WordTrace (prefixWord ++ tailWord_3268342) baseStart_3268342 baseEnd_3268342 := by
    simpa [prefixWord, tailWord_3268342, baseEnd_3268342] using wordTrace_append hprefix tailTrace_3268342
  have hstable : (prefixWord ++ tailWord_3268342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268342).length < 2 ^ (prefixWord ++ tailWord_3268342).sum := by decide
  have hdescent : baseEnd_3268342 < baseStart_3268342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268362 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_3268362 : Nat := 118140960795 + 3268362 * 2 ^ 59
def prefixEnd_3268362 : Nat := 4983230072969 + 3 ^ 40 * 3268362 * 2
def baseEnd_3268362 : Nat := 1678240658890246752344083

theorem tailTrace_3268362 : CollatzResearch.WordTrace tailWord_3268362 prefixEnd_3268362 1678240658890246752344083 := by
  unfold tailWord_3268362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29801738846322535158697835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79471303590193427089860893 29801738846322535158697835)
  ·
    refine ⟨44702608269483802738046753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29801738846322535158697835 44702608269483802738046753)
    ·
      refine ⟨33526956202112852053535065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44702608269483802738046753 33526956202112852053535065)
      ·
        refine ⟨25145217151584639040151299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33526956202112852053535065 25145217151584639040151299)
        ·
          refine ⟨37717825727376958560226949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25145217151584639040151299 37717825727376958560226949)
          ·
            refine ⟨7072092323883179730042553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37717825727376958560226949 7072092323883179730042553)
            ·
              refine ⟨5304069242912384797531915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7072092323883179730042553 5304069242912384797531915)
              ·
                refine ⟨7956103864368577196297873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304069242912384797531915 7956103864368577196297873)
                ·
                  refine ⟨5967077898276432897223405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956103864368577196297873 5967077898276432897223405)
                  ·
                    refine ⟨2237654211853662336458777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5967077898276432897223405 2237654211853662336458777)
                    ·
                      refine ⟨1678240658890246752344083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237654211853662336458777 1678240658890246752344083)
                      ·
                        rfl

theorem cell23_3268362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_3268362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268362 prefixEnd_3268362 := by exact prefixLift 3268362
  have htrace : WordTrace (prefixWord ++ tailWord_3268362) baseStart_3268362 baseEnd_3268362 := by
    simpa [prefixWord, tailWord_3268362, baseEnd_3268362] using wordTrace_append hprefix tailTrace_3268362
  have hstable : (prefixWord ++ tailWord_3268362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268362).length < 2 ^ (prefixWord ++ tailWord_3268362).sum := by decide
  have hdescent : baseEnd_3268362 < baseStart_3268362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268371 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_3268371 : Nat := 118140960795 + 3268371 * 2 ^ 59
def prefixEnd_3268371 : Nat := 4983230072969 + 3 ^ 40 * 3268371 * 2
def baseEnd_3268371 : Nat := 1678245280216137217131541

theorem tailTrace_3268371 : CollatzResearch.WordTrace tailWord_3268371 prefixEnd_3268371 1678245280216137217131541 := by
  unfold tailWord_3268371
  simp only [CollatzResearch.WordTrace]
  refine ⟨119207283642257535171868967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79471522428171690114579311 119207283642257535171868967)
  ·
    refine ⟨178810925463386302757803451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119207283642257535171868967 178810925463386302757803451)
    ·
      refine ⟨268216388195079454136705177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178810925463386302757803451 268216388195079454136705177)
      ·
        refine ⟨201162291146309590602528883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268216388195079454136705177 201162291146309590602528883)
        ·
          refine ⟨301743436719464385903793325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201162291146309590602528883 301743436719464385903793325)
          ·
            refine ⟨113153788769799144713922497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301743436719464385903793325 113153788769799144713922497)
            ·
              refine ⟨84865341577349358535441873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113153788769799144713922497 84865341577349358535441873)
              ·
                refine ⟨63649006183012018901581405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84865341577349358535441873 63649006183012018901581405)
                ·
                  refine ⟨23868377318629507088093027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63649006183012018901581405 23868377318629507088093027)
                  ·
                    refine ⟨35802565977944260632139541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23868377318629507088093027 35802565977944260632139541)
                    ·
                      refine ⟨1678245280216137217131541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35802565977944260632139541 1678245280216137217131541)
                      ·
                        rfl

theorem cell23_3268371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_3268371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268371 prefixEnd_3268371 := by exact prefixLift 3268371
  have htrace : WordTrace (prefixWord ++ tailWord_3268371) baseStart_3268371 baseEnd_3268371 := by
    simpa [prefixWord, tailWord_3268371, baseEnd_3268371] using wordTrace_append hprefix tailTrace_3268371
  have hstable : (prefixWord ++ tailWord_3268371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268371).length < 2 ^ (prefixWord ++ tailWord_3268371).sum := by decide
  have hdescent : baseEnd_3268371 < baseStart_3268371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268381 : List Nat := [1, 4, 2, 16]
def baseStart_3268381 : Nat := 118140960795 + 3268381 * 2 ^ 59
def prefixEnd_3268381 : Nat := 4983230072969 + 3 ^ 40 * 3268381 * 2
def baseEnd_3268381 : Nat := 767375589859479733885

theorem tailTrace_3268381 : CollatzResearch.WordTrace tailWord_3268381 prefixEnd_3268381 767375589859479733885 := by
  unfold tailWord_3268381
  simp only [CollatzResearch.WordTrace]
  refine ⟨119207648372221306879732997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79471765581480871253155331 119207648372221306879732997)
  ·
    refine ⟨22351434069791495039949937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119207648372221306879732997 22351434069791495039949937)
    ·
      refine ⟨16763575552343621279962453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22351434069791495039949937 16763575552343621279962453)
      ·
        refine ⟨767375589859479733885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 16763575552343621279962453 767375589859479733885)
        ·
          rfl

theorem cell23_3268381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 16].length) (baseStart_3268381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268381 prefixEnd_3268381 := by exact prefixLift 3268381
  have htrace : WordTrace (prefixWord ++ tailWord_3268381) baseStart_3268381 baseEnd_3268381 := by
    simpa [prefixWord, tailWord_3268381, baseEnd_3268381] using wordTrace_append hprefix tailTrace_3268381
  have hstable : (prefixWord ++ tailWord_3268381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268381).length < 2 ^ (prefixWord ++ tailWord_3268381).sum := by decide
  have hdescent : baseEnd_3268381 < baseStart_3268381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268385 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3268385 : Nat := 118140960795 + 3268385 * 2 ^ 59
def prefixEnd_3268385 : Nat := 4983230072969 + 3 ^ 40 * 3268385 * 2
def baseEnd_3268385 : Nat := 559417489648433387452159

theorem tailTrace_3268385 : CollatzResearch.WordTrace tailWord_3268385 prefixEnd_3268385 559417489648433387452159 := by
  unfold tailWord_3268385
  simp only [CollatzResearch.WordTrace]
  refine ⟨119207794264206815562878609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79471862842804543708585739 119207794264206815562878609)
  ·
    refine ⟨89405845698155111672158957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119207794264206815562878609 89405845698155111672158957)
    ·
      refine ⟨33527192136808166877059609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89405845698155111672158957 33527192136808166877059609)
      ·
        refine ⟨25145394102606125157794707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33527192136808166877059609 25145394102606125157794707)
        ·
          refine ⟨37718091153909187736692061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25145394102606125157794707 37718091153909187736692061)
          ·
            refine ⟨14144284182715945401259523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37718091153909187736692061 14144284182715945401259523)
            ·
              refine ⟨21216426274073918101889285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144284182715945401259523 21216426274073918101889285)
              ·
                refine ⟨3978079926388859644104241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21216426274073918101889285 3978079926388859644104241)
                ·
                  refine ⟨2983559944791644733078181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978079926388859644104241 2983559944791644733078181)
                  ·
                    refine ⟨559417489648433387452159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983559944791644733078181 559417489648433387452159)
                    ·
                      rfl

theorem cell23_3268385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3268385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268385 prefixEnd_3268385 := by exact prefixLift 3268385
  have htrace : WordTrace (prefixWord ++ tailWord_3268385) baseStart_3268385 baseEnd_3268385 := by
    simpa [prefixWord, tailWord_3268385, baseEnd_3268385] using wordTrace_append hprefix tailTrace_3268385
  have hstable : (prefixWord ++ tailWord_3268385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268385).length < 2 ^ (prefixWord ++ tailWord_3268385).sum := by decide
  have hdescent : baseEnd_3268385 < baseStart_3268385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268415 : List Nat := [1, 1, 2, 2, 6, 1, 3, 7]
def baseStart_3268415 : Nat := 118140960795 + 3268415 * 2 ^ 59
def prefixEnd_3268415 : Nat := 4983230072969 + 3 ^ 40 * 3268415 * 2
def baseEnd_3268415 : Nat := 62158069383886483147457

theorem tailTrace_3268415 : CollatzResearch.WordTrace tailWord_3268415 prefixEnd_3268415 62158069383886483147457 := by
  unfold tailWord_3268415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119208888454098130686470699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79472592302732087124313799 119208888454098130686470699)
  ·
    refine ⟨178813332681147196029706049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119208888454098130686470699 178813332681147196029706049)
    ·
      refine ⟨134109999510860397022279537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178813332681147196029706049 134109999510860397022279537)
      ·
        refine ⟨100582499633145297766709653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134109999510860397022279537 100582499633145297766709653)
        ·
          refine ⟨4714804670303685832814515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100582499633145297766709653 4714804670303685832814515)
          ·
            refine ⟨7072207005455528749221773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4714804670303685832814515 7072207005455528749221773)
            ·
              refine ⟨2652077627045823280958165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7072207005455528749221773 2652077627045823280958165)
              ·
                refine ⟨62158069383886483147457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2652077627045823280958165 62158069383886483147457)
                ·
                  rfl

theorem cell23_3268415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 7].length) (baseStart_3268415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268415 prefixEnd_3268415 := by exact prefixLift 3268415
  have htrace : WordTrace (prefixWord ++ tailWord_3268415) baseStart_3268415 baseEnd_3268415 := by
    simpa [prefixWord, tailWord_3268415, baseEnd_3268415] using wordTrace_append hprefix tailTrace_3268415
  have hstable : (prefixWord ++ tailWord_3268415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268415).length < 2 ^ (prefixWord ++ tailWord_3268415).sum := by decide
  have hdescent : baseEnd_3268415 < baseStart_3268415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268425 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 3]
def baseStart_3268425 : Nat := 118140960795 + 3268425 * 2 ^ 59
def prefixEnd_3268425 : Nat := 4983230072969 + 3 ^ 40 * 3268425 * 2
def baseEnd_3268425 : Nat := 1678273008171480005856293

theorem tailTrace_3268425 : CollatzResearch.WordTrace tailWord_3268425 prefixEnd_3268425 1678273008171480005856293 := by
  unfold tailWord_3268425
  simp only [CollatzResearch.WordTrace]
  refine ⟨119209253184061902394334729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79472835456041268262889819 119209253184061902394334729)
  ·
    refine ⟨89406939888046426795751047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119209253184061902394334729 89406939888046426795751047)
    ·
      refine ⟨134110409832069640193626571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89406939888046426795751047 134110409832069640193626571)
      ·
        refine ⟨201165614748104460290439857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134110409832069640193626571 201165614748104460290439857)
        ·
          refine ⟨150874211061078345217829893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201165614748104460290439857 150874211061078345217829893)
          ·
            refine ⟨28288914573952189728343105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150874211061078345217829893 28288914573952189728343105)
            ·
              refine ⟨21216685930464142296257329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28288914573952189728343105 21216685930464142296257329)
              ·
                refine ⟨15912514447848106722192997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21216685930464142296257329 15912514447848106722192997)
                ·
                  refine ⟨2983596458971520010411187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15912514447848106722192997 2983596458971520010411187)
                  ·
                    refine ⟨4475394688457280015616781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983596458971520010411187 4475394688457280015616781)
                    ·
                      refine ⟨1678273008171480005856293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475394688457280015616781 1678273008171480005856293)
                      ·
                        rfl

theorem cell23_3268425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_3268425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268425 prefixEnd_3268425 := by exact prefixLift 3268425
  have htrace : WordTrace (prefixWord ++ tailWord_3268425) baseStart_3268425 baseEnd_3268425 := by
    simpa [prefixWord, tailWord_3268425, baseEnd_3268425] using wordTrace_append hprefix tailTrace_3268425
  have hstable : (prefixWord ++ tailWord_3268425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268425).length < 2 ^ (prefixWord ++ tailWord_3268425).sum := by decide
  have hdescent : baseEnd_3268425 < baseStart_3268425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268429 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3268429 : Nat := 118140960795 + 3268429 * 2 ^ 59
def prefixEnd_3268429 : Nat := 4983230072969 + 3 ^ 40 * 3268429 * 2
def baseEnd_3268429 : Nat := 1678275062094097990206275

theorem tailTrace_3268429 : CollatzResearch.WordTrace tailWord_3268429 prefixEnd_3268429 1678275062094097990206275 := by
  unfold tailWord_3268429
  simp only [CollatzResearch.WordTrace]
  refine ⟨119209399076047411077480341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79472932717364940718320227 119209399076047411077480341)
  ·
    refine ⟨5587940581689722394256891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119209399076047411077480341 5587940581689722394256891)
    ·
      refine ⟨8381910872534583591385337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587940581689722394256891 8381910872534583591385337)
      ·
        refine ⟨6286433154400937693539003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8381910872534583591385337 6286433154400937693539003)
        ·
          refine ⟨9429649731601406540308505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286433154400937693539003 9429649731601406540308505)
          ·
            refine ⟨7072237298701054905231379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9429649731601406540308505 7072237298701054905231379)
            ·
              refine ⟨10608355948051582357847069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072237298701054905231379 10608355948051582357847069)
              ·
                refine ⟨3978133480519343384192651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10608355948051582357847069 3978133480519343384192651)
                ·
                  refine ⟨5967200220779015076288977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978133480519343384192651 5967200220779015076288977)
                  ·
                    refine ⟨4475400165584261307216733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967200220779015076288977 4475400165584261307216733)
                    ·
                      refine ⟨1678275062094097990206275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475400165584261307216733 1678275062094097990206275)
                      ·
                        rfl

theorem cell23_3268429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3268429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268429 prefixEnd_3268429 := by exact prefixLift 3268429
  have htrace : WordTrace (prefixWord ++ tailWord_3268429) baseStart_3268429 baseEnd_3268429 := by
    simpa [prefixWord, tailWord_3268429, baseEnd_3268429] using wordTrace_append hprefix tailTrace_3268429
  have hstable : (prefixWord ++ tailWord_3268429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268429).length < 2 ^ (prefixWord ++ tailWord_3268429).sum := by decide
  have hdescent : baseEnd_3268429 < baseStart_3268429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268469 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3268469 : Nat := 118140960795 + 3268469 * 2 ^ 59
def prefixEnd_3268469 : Nat := 4983230072969 + 3 ^ 40 * 3268469 * 2
def baseEnd_3268469 : Nat := 1678295601320277833706091

theorem tailTrace_3268469 : CollatzResearch.WordTrace tailWord_3268469 prefixEnd_3268469 1678295601320277833706091 := by
  unfold tailWord_3268469
  simp only [CollatzResearch.WordTrace]
  refine ⟨119210857995902497908936461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79473905330601665272624307 119210857995902497908936461)
  ·
    refine ⟨44704071748463436715851173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119210857995902497908936461 44704071748463436715851173)
    ·
      refine ⟨8382013452836894384222095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44704071748463436715851173 8382013452836894384222095)
      ·
        refine ⟨12573020179255341576333143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8382013452836894384222095 12573020179255341576333143)
        ·
          refine ⟨18859530268883012364499715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12573020179255341576333143 18859530268883012364499715)
          ·
            refine ⟨28289295403324518546749573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18859530268883012364499715 28289295403324518546749573)
            ·
              refine ⟨5304242888123347227515545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28289295403324518546749573 5304242888123347227515545)
              ·
                refine ⟨3978182166092510420636659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304242888123347227515545 3978182166092510420636659)
                ·
                  refine ⟨5967273249138765630954989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978182166092510420636659 5967273249138765630954989)
                  ·
                    refine ⟨2237727468427037111608121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5967273249138765630954989 2237727468427037111608121)
                    ·
                      refine ⟨1678295601320277833706091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237727468427037111608121 1678295601320277833706091)
                      ·
                        rfl

theorem cell23_3268469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3268469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268469 prefixEnd_3268469 := by exact prefixLift 3268469
  have htrace : WordTrace (prefixWord ++ tailWord_3268469) baseStart_3268469 baseEnd_3268469 := by
    simpa [prefixWord, tailWord_3268469, baseEnd_3268469] using wordTrace_append hprefix tailTrace_3268469
  have hstable : (prefixWord ++ tailWord_3268469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268469).length < 2 ^ (prefixWord ++ tailWord_3268469).sum := by decide
  have hdescent : baseEnd_3268469 < baseStart_3268469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268505 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 5]
def baseStart_3268505 : Nat := 118140960795 + 3268505 * 2 ^ 59
def prefixEnd_3268505 : Nat := 4983230072969 + 3 ^ 40 * 3268505 * 2
def baseEnd_3268505 : Nat := 186479342958204410317325

theorem tailTrace_3268505 : CollatzResearch.WordTrace tailWord_3268505 prefixEnd_3268505 186479342958204410317325 := by
  unfold tailWord_3268505
  simp only [CollatzResearch.WordTrace]
  refine ⟨119212171023772076057246969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79474780682514717371497979 119212171023772076057246969)
  ·
    refine ⟨89409128267829057042935227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119212171023772076057246969 89409128267829057042935227)
    ·
      refine ⟨134113692401743585564402841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89409128267829057042935227 134113692401743585564402841)
      ·
        refine ⟨100585269301307689173302131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134113692401743585564402841 100585269301307689173302131)
        ·
          refine ⟨150877903951961533759953197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100585269301307689173302131 150877903951961533759953197)
          ·
            refine ⟨56579213981985575159982449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150877903951961533759953197 56579213981985575159982449)
            ·
              refine ⟨42434410486489181369986837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56579213981985575159982449 42434410486489181369986837)
              ·
                refine ⟨1989112991554180376718133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42434410486489181369986837 1989112991554180376718133)
                ·
                  refine ⟨186479342958204410317325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1989112991554180376718133 186479342958204410317325)
                  ·
                    rfl

theorem cell23_3268505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 5].length) (baseStart_3268505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268505 prefixEnd_3268505 := by exact prefixLift 3268505
  have htrace : WordTrace (prefixWord ++ tailWord_3268505) baseStart_3268505 baseEnd_3268505 := by
    simpa [prefixWord, tailWord_3268505, baseEnd_3268505] using wordTrace_append hprefix tailTrace_3268505
  have hstable : (prefixWord ++ tailWord_3268505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268505).length < 2 ^ (prefixWord ++ tailWord_3268505).sum := by decide
  have hdescent : baseEnd_3268505 < baseStart_3268505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268510 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3268510 : Nat := 118140960795 + 3268510 * 2 ^ 59
def prefixEnd_3268510 : Nat := 4983230072969 + 3 ^ 40 * 3268510 * 2
def baseEnd_3268510 : Nat := 1678316654027112173293403

theorem tailTrace_3268510 : CollatzResearch.WordTrace tailWord_3268510 prefixEnd_3268510 1678316654027112173293403 := by
  unfold tailWord_3268510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901544173594245238897373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79474902259169307940785989 14901544173594245238897373)
  ·
    refine ⟨5588079065097841964586515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14901544173594245238897373 5588079065097841964586515)
    ·
      refine ⟨8382118597646762946879773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588079065097841964586515 8382118597646762946879773)
      ·
        refine ⟨3143294474117536105079915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8382118597646762946879773 3143294474117536105079915)
        ·
          refine ⟨4714941711176304157619873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143294474117536105079915 4714941711176304157619873)
          ·
            refine ⟨3536206283382228118214905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4714941711176304157619873 3536206283382228118214905)
            ·
              refine ⟨2652154712536671088661179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536206283382228118214905 2652154712536671088661179)
              ·
                refine ⟨3978232068805006632991769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652154712536671088661179 3978232068805006632991769)
                ·
                  refine ⟨2983674051603754974743827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978232068805006632991769 2983674051603754974743827)
                  ·
                    refine ⟨4475511077405632462115741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983674051603754974743827 4475511077405632462115741)
                    ·
                      refine ⟨1678316654027112173293403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475511077405632462115741 1678316654027112173293403)
                      ·
                        rfl

theorem cell23_3268510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3268510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268510 prefixEnd_3268510 := by exact prefixLift 3268510
  have htrace : WordTrace (prefixWord ++ tailWord_3268510) baseStart_3268510 baseEnd_3268510 := by
    simpa [prefixWord, tailWord_3268510, baseEnd_3268510] using wordTrace_append hprefix tailTrace_3268510
  have hstable : (prefixWord ++ tailWord_3268510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268510).length < 2 ^ (prefixWord ++ tailWord_3268510).sum := by decide
  have hdescent : baseEnd_3268510 < baseStart_3268510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268516 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_3268516 : Nat := 118140960795 + 3268516 * 2 ^ 59
def prefixEnd_3268516 : Nat := 4983230072969 + 3 ^ 40 * 3268516 * 2
def baseEnd_3268516 : Nat := 1678319734911039149818375

theorem tailTrace_3268516 : CollatzResearch.WordTrace tailWord_3268516 prefixEnd_3268516 1678319734911039149818375 := by
  unfold tailWord_3268516
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606286113366112467948701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79475048151154816623931601 59606286113366112467948701)
  ·
    refine ⟨22352357292512292175480763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59606286113366112467948701 22352357292512292175480763)
    ·
      refine ⟨33528535938768438263221145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22352357292512292175480763 33528535938768438263221145)
      ·
        refine ⟨25146401954076328697415859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33528535938768438263221145 25146401954076328697415859)
        ·
          refine ⟨37719602931114493046123789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25146401954076328697415859 37719602931114493046123789)
          ·
            refine ⟨14144851099167934892296421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37719602931114493046123789 14144851099167934892296421)
            ·
              refine ⟨2652159581093987792305579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14144851099167934892296421 2652159581093987792305579)
              ·
                refine ⟨3978239371640981688458369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652159581093987792305579 3978239371640981688458369)
                ·
                  refine ⟨2983679528730736266343777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978239371640981688458369 2983679528730736266343777)
                  ·
                    refine ⟨2237759646548052199757833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983679528730736266343777 2237759646548052199757833)
                    ·
                      refine ⟨1678319734911039149818375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237759646548052199757833 1678319734911039149818375)
                      ·
                        rfl

theorem cell23_3268516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_3268516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268516 prefixEnd_3268516 := by exact prefixLift 3268516
  have htrace : WordTrace (prefixWord ++ tailWord_3268516) baseStart_3268516 baseEnd_3268516 := by
    simpa [prefixWord, tailWord_3268516, baseEnd_3268516] using wordTrace_append hprefix tailTrace_3268516
  have hstable : (prefixWord ++ tailWord_3268516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268516).length < 2 ^ (prefixWord ++ tailWord_3268516).sum := by decide
  have hdescent : baseEnd_3268516 < baseStart_3268516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
