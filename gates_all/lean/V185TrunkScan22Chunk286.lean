import V185TrunkScan22Chunk285

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2551508 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2551508 : Nat := 118140960795 + 2551508 * 2 ^ 59
def prefixEnd_2551508 : Nat := 4983230072969 + 3 ^ 40 * 2551508 * 2
def baseEnd_2551508 : Nat := 873433331861405631277223

theorem tailTrace_2551508 : CollatzResearch.WordTrace tailWord_2551508 prefixEnd_2551508 873433331861405631277223 := by
  unfold tailWord_2551508
  simp only [CollatzResearch.WordTrace]
  refine ⟨46530571020164876859327589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62040761360219835812436785 46530571020164876859327589)
  ·
    refine ⟨8724482066280914411123923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46530571020164876859327589 8724482066280914411123923)
    ·
      refine ⟨13086723099421371616685885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724482066280914411123923 13086723099421371616685885)
      ·
        refine ⟨4907521162283014356257207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13086723099421371616685885 4907521162283014356257207)
        ·
          refine ⟨7361281743424521534385811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907521162283014356257207 7361281743424521534385811)
          ·
            refine ⟨11041922615136782301578717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361281743424521534385811 11041922615136782301578717)
            ·
              refine ⟨4140720980676293363092019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11041922615136782301578717 4140720980676293363092019)
              ·
                refine ⟨6211081471014440044638029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140720980676293363092019 6211081471014440044638029)
                ·
                  refine ⟨2329155551630415016739261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6211081471014440044638029 2329155551630415016739261)
                  ·
                    refine ⟨873433331861405631277223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329155551630415016739261 873433331861405631277223)
                    ·
                      rfl

theorem cell22_2551508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2551508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551508 prefixEnd_2551508 := by exact prefixLift 2551508
  have htrace : WordTrace (prefixWord ++ tailWord_2551508) baseStart_2551508 baseEnd_2551508 := by
    simpa [prefixWord, tailWord_2551508, baseEnd_2551508] using wordTrace_append hprefix tailTrace_2551508
  have hstable : (prefixWord ++ tailWord_2551508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551508).length < 2 ^ (prefixWord ++ tailWord_2551508).sum := by decide
  have hdescent : baseEnd_2551508 < baseStart_2551508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551521 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 5]
def baseStart_2551521 : Nat := 118140960795 + 2551521 * 2 ^ 59
def prefixEnd_2551521 : Nat := 4983230072969 + 3 ^ 40 * 2551521 * 2
def baseEnd_2551521 : Nat := 291145927342359310234061

theorem tailTrace_2551521 : CollatzResearch.WordTrace tailWord_2551521 prefixEnd_2551521 291145927342359310234061 := by
  unfold tailWord_2551521
  simp only [CollatzResearch.WordTrace]
  refine ⟨93061616189282656938878417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62041077459521771292585611 93061616189282656938878417)
  ·
    refine ⟨69796212141961992704158813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93061616189282656938878417 69796212141961992704158813)
    ·
      refine ⟨26173579553235747264059555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69796212141961992704158813 26173579553235747264059555)
      ·
        refine ⟨39260369329853620896089333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26173579553235747264059555 39260369329853620896089333)
        ·
          refine ⟨3680659624673776959008375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39260369329853620896089333 3680659624673776959008375)
          ·
            refine ⟨5520989437010665438512563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680659624673776959008375 5520989437010665438512563)
            ·
              refine ⟨8281484155515998157768845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520989437010665438512563 8281484155515998157768845)
              ·
                refine ⟨3105556558318499309163317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8281484155515998157768845 3105556558318499309163317)
                ·
                  refine ⟨291145927342359310234061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3105556558318499309163317 291145927342359310234061)
                  ·
                    rfl

theorem cell22_2551521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_2551521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551521 prefixEnd_2551521 := by exact prefixLift 2551521
  have htrace : WordTrace (prefixWord ++ tailWord_2551521) baseStart_2551521 baseEnd_2551521 := by
    simpa [prefixWord, tailWord_2551521, baseEnd_2551521] using wordTrace_append hprefix tailTrace_2551521
  have hstable : (prefixWord ++ tailWord_2551521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551521).length < 2 ^ (prefixWord ++ tailWord_2551521).sum := by decide
  have hdescent : baseEnd_2551521 < baseStart_2551521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551559 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2551559 : Nat := 118140960795 + 2551559 * 2 ^ 59
def prefixEnd_2551559 : Nat := 4983230072969 + 3 ^ 40 * 2551559 * 2
def baseEnd_2551559 : Nat := 873450790203658498252067

theorem tailTrace_2551559 : CollatzResearch.WordTrace tailWord_2551559 prefixEnd_2551559 873450790203658498252067 := by
  unfold tailWord_2551559
  simp only [CollatzResearch.WordTrace]
  refine ⟨93063002163144989428761731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62042001442096659619174487 93063002163144989428761731)
  ·
    refine ⟨139594503244717484143142597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93063002163144989428761731 139594503244717484143142597)
    ·
      refine ⟨26173969358384528276839237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139594503244717484143142597 26173969358384528276839237)
      ·
        refine ⟨4907619254697099051907357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26173969358384528276839237 4907619254697099051907357)
        ·
          refine ⟨1840357220511412144465259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4907619254697099051907357 1840357220511412144465259)
          ·
            refine ⟨2760535830767118216697889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840357220511412144465259 2760535830767118216697889)
            ·
              refine ⟨2070401873075338662523417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760535830767118216697889 2070401873075338662523417)
              ·
                refine ⟨1552801404806503996892563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070401873075338662523417 1552801404806503996892563)
                ·
                  refine ⟨2329202107209755995338845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552801404806503996892563 2329202107209755995338845)
                  ·
                    refine ⟨873450790203658498252067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329202107209755995338845 873450790203658498252067)
                    ·
                      rfl

theorem cell22_2551559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2551559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551559 prefixEnd_2551559 := by exact prefixLift 2551559
  have htrace : WordTrace (prefixWord ++ tailWord_2551559) baseStart_2551559 baseEnd_2551559 := by
    simpa [prefixWord, tailWord_2551559, baseEnd_2551559] using wordTrace_append hprefix tailTrace_2551559
  have hstable : (prefixWord ++ tailWord_2551559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551559).length < 2 ^ (prefixWord ++ tailWord_2551559).sum := by decide
  have hdescent : baseEnd_2551559 < baseStart_2551559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551596 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_2551596 : Nat := 118140960795 + 2551596 * 2 ^ 59
def prefixEnd_2551596 : Nat := 4983230072969 + 3 ^ 40 * 2551596 * 2
def baseEnd_2551596 : Nat := 873463456059802735076953

theorem tailTrace_2551596 : CollatzResearch.WordTrace tailWord_2551596 prefixEnd_2551596 873463456059802735076953 := by
  unfold tailWord_2551596
  simp only [CollatzResearch.WordTrace]
  refine ⟨46532175832005472373929321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62042901109340629831905761 46532175832005472373929321)
  ·
    refine ⟨34899131874004104280446991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46532175832005472373929321 34899131874004104280446991)
    ·
      refine ⟨52348697811006156420670487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34899131874004104280446991 52348697811006156420670487)
      ·
        refine ⟨78523046716509234631005731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52348697811006156420670487 78523046716509234631005731)
        ·
          refine ⟨117784570074763851946508597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78523046716509234631005731 117784570074763851946508597)
          ·
            refine ⟨11042303444509111119985181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117784570074763851946508597 11042303444509111119985181)
            ·
              refine ⟨4140863791690916669994443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11042303444509111119985181 4140863791690916669994443)
              ·
                refine ⟨6211295687536375004991665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140863791690916669994443 6211295687536375004991665)
                ·
                  refine ⟨4658471765652281253743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211295687536375004991665 4658471765652281253743749)
                  ·
                    refine ⟨873463456059802735076953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658471765652281253743749 873463456059802735076953)
                    ·
                      rfl

theorem cell22_2551596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_2551596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551596 prefixEnd_2551596 := by exact prefixLift 2551596
  have htrace : WordTrace (prefixWord ++ tailWord_2551596) baseStart_2551596 baseEnd_2551596 := by
    simpa [prefixWord, tailWord_2551596, baseEnd_2551596] using wordTrace_append hprefix tailTrace_2551596
  have hstable : (prefixWord ++ tailWord_2551596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551596).length < 2 ^ (prefixWord ++ tailWord_2551596).sum := by decide
  have hdescent : baseEnd_2551596 < baseStart_2551596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551615 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 2, 3]
def baseStart_2551615 : Nat := 118140960795 + 2551615 * 2 ^ 59
def prefixEnd_2551615 : Nat := 4983230072969 + 3 ^ 40 * 2551615 * 2
def baseEnd_2551615 : Nat := 873469960148093018851895

theorem tailTrace_2551615 : CollatzResearch.WordTrace tailWord_2551615 prefixEnd_2551615 873469960148093018851895 := by
  unfold tailWord_2551615
  simp only [CollatzResearch.WordTrace]
  refine ⟨93065044650942110992800299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62043363100628073995200199 93065044650942110992800299)
  ·
    refine ⟨139597566976413166489200449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93065044650942110992800299 139597566976413166489200449)
    ·
      refine ⟨104698175232309874866900337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139597566976413166489200449 104698175232309874866900337)
      ·
        refine ⟨78523631424232406150175253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104698175232309874866900337 78523631424232406150175253)
        ·
          refine ⟨3680795223010894038289465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78523631424232406150175253 3680795223010894038289465)
          ·
            refine ⟨2760596417258170528717099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3680795223010894038289465 2760596417258170528717099)
            ·
              refine ⟨4140894625887255793075649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760596417258170528717099 4140894625887255793075649)
              ·
                refine ⟨3105670969415441844806737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140894625887255793075649 3105670969415441844806737)
                ·
                  refine ⟨2329253227061581383605053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3105670969415441844806737 2329253227061581383605053)
                  ·
                    refine ⟨873469960148093018851895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329253227061581383605053 873469960148093018851895)
                    ·
                      rfl

theorem cell22_2551615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_2551615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551615 prefixEnd_2551615 := by exact prefixLift 2551615
  have htrace : WordTrace (prefixWord ++ tailWord_2551615) baseStart_2551615 baseEnd_2551615 := by
    simpa [prefixWord, tailWord_2551615, baseEnd_2551615] using wordTrace_append hprefix tailTrace_2551615
  have hstable : (prefixWord ++ tailWord_2551615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551615).length < 2 ^ (prefixWord ++ tailWord_2551615).sum := by decide
  have hdescent : baseEnd_2551615 < baseStart_2551615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551660 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_2551660 : Nat := 118140960795 + 2551660 * 2 ^ 59
def prefixEnd_2551660 : Nat := 4983230072969 + 3 ^ 40 * 2551660 * 2
def baseEnd_2551660 : Nat := 873485364567727901476757

theorem tailTrace_2551660 : CollatzResearch.WordTrace tailWord_2551660 prefixEnd_2551660 873485364567727901476757 := by
  unfold tailWord_2551660
  simp only [CollatzResearch.WordTrace]
  refine ⟨46533342967889541839094217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62044457290519389118792289 46533342967889541839094217)
  ·
    refine ⟨34900007225917156379320663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46533342967889541839094217 34900007225917156379320663)
    ·
      refine ⟨52350010838875734568980995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34900007225917156379320663 52350010838875734568980995)
      ·
        refine ⟨78525016258313601853471493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52350010838875734568980995 78525016258313601853471493)
        ·
          refine ⟨14723440548433800347525905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78525016258313601853471493 14723440548433800347525905)
          ·
            refine ⟨11042580411325350260644429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14723440548433800347525905 11042580411325350260644429)
            ·
              refine ⟨4140967654247006347741661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11042580411325350260644429 4140967654247006347741661)
              ·
                refine ⟨1552862870342627380403123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4140967654247006347741661 1552862870342627380403123)
                ·
                  refine ⟨2329294305513941070604685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552862870342627380403123 2329294305513941070604685)
                  ·
                    refine ⟨873485364567727901476757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329294305513941070604685 873485364567727901476757)
                    ·
                      rfl

theorem cell22_2551660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_2551660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551660 prefixEnd_2551660 := by exact prefixLift 2551660
  have htrace : WordTrace (prefixWord ++ tailWord_2551660) baseStart_2551660 baseEnd_2551660 := by
    simpa [prefixWord, tailWord_2551660, baseEnd_2551660] using wordTrace_append hprefix tailTrace_2551660
  have hstable : (prefixWord ++ tailWord_2551660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551660).length < 2 ^ (prefixWord ++ tailWord_2551660).sum := by decide
  have hdescent : baseEnd_2551660 < baseStart_2551660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551703 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2551703 : Nat := 118140960795 + 2551703 * 2 ^ 59
def prefixEnd_2551703 : Nat := 4983230072969 + 3 ^ 40 * 2551703 * 2
def baseEnd_2551703 : Nat := 873500084346490122651625

theorem tailTrace_2551703 : CollatzResearch.WordTrace tailWord_2551703 prefixEnd_2551703 873500084346490122651625 := by
  unfold tailWord_2551703
  simp only [CollatzResearch.WordTrace]
  refine ⟨93068254274623302022003763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62045502849748868014669175 93068254274623302022003763)
  ·
    refine ⟨139602381411934953033005645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93068254274623302022003763 139602381411934953033005645)
    ·
      refine ⟨52350893029475607387377117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139602381411934953033005645 52350893029475607387377117)
      ·
        refine ⟨19631584886053352770266419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52350893029475607387377117 19631584886053352770266419)
        ·
          refine ⟨29447377329080029155399629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19631584886053352770266419 29447377329080029155399629)
          ·
            refine ⟨11042766498405010933274861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29447377329080029155399629 11042766498405010933274861)
            ·
              refine ⟨4141037436901879099978073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11042766498405010933274861 4141037436901879099978073)
              ·
                refine ⟨3105778077676409324983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4141037436901879099978073 3105778077676409324983555)
                ·
                  refine ⟨4658667116514613987475333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105778077676409324983555 4658667116514613987475333)
                  ·
                    refine ⟨873500084346490122651625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658667116514613987475333 873500084346490122651625)
                    ·
                      rfl

theorem cell22_2551703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2551703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551703 prefixEnd_2551703 := by exact prefixLift 2551703
  have htrace : WordTrace (prefixWord ++ tailWord_2551703) baseStart_2551703 baseEnd_2551703 := by
    simpa [prefixWord, tailWord_2551703, baseEnd_2551703] using wordTrace_append hprefix tailTrace_2551703
  have hstable : (prefixWord ++ tailWord_2551703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551703).length < 2 ^ (prefixWord ++ tailWord_2551703).sum := by decide
  have hdescent : baseEnd_2551703 < baseStart_2551703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551716 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2551716 : Nat := 118140960795 + 2551716 * 2 ^ 59
def prefixEnd_2551716 : Nat := 4983230072969 + 3 ^ 40 * 2551716 * 2
def baseEnd_2551716 : Nat := 873504534512162422076585

theorem tailTrace_2551716 : CollatzResearch.WordTrace tailWord_2551716 prefixEnd_2551716 873504534512162422076585 := by
  unfold tailWord_2551716
  simp only [CollatzResearch.WordTrace]
  refine ⟨46534364211788102621113501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62045818949050803494818001 46534364211788102621113501)
  ·
    refine ⟨17450386579420538482917563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46534364211788102621113501 17450386579420538482917563)
    ·
      refine ⟨26175579869130807724376345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17450386579420538482917563 26175579869130807724376345)
      ·
        refine ⟨19631684901848105793282259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26175579869130807724376345 19631684901848105793282259)
        ·
          refine ⟨29447527352772158689923389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19631684901848105793282259 29447527352772158689923389)
          ·
            refine ⟨11042822757289559508721271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29447527352772158689923389 11042822757289559508721271)
            ·
              refine ⟨16564234135934339263081907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11042822757289559508721271 16564234135934339263081907)
              ·
                refine ⟨24846351203901508894622861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16564234135934339263081907 24846351203901508894622861)
                ·
                  refine ⟨9317381701463065835483573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24846351203901508894622861 9317381701463065835483573)
                  ·
                    refine ⟨873504534512162422076585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9317381701463065835483573 873504534512162422076585)
                    ·
                      rfl

theorem cell22_2551716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2551716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551716 prefixEnd_2551716 := by exact prefixLift 2551716
  have htrace : WordTrace (prefixWord ++ tailWord_2551716) baseStart_2551716 baseEnd_2551716 := by
    simpa [prefixWord, tailWord_2551716, baseEnd_2551716] using wordTrace_append hprefix tailTrace_2551716
  have hstable : (prefixWord ++ tailWord_2551716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551716).length < 2 ^ (prefixWord ++ tailWord_2551716).sum := by decide
  have hdescent : baseEnd_2551716 < baseStart_2551716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551731 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_2551731 : Nat := 118140960795 + 2551731 * 2 ^ 59
def prefixEnd_2551731 : Nat := 4983230072969 + 3 ^ 40 * 2551731 * 2
def baseEnd_2551731 : Nat := 873509669318707382951539

theorem tailTrace_2551731 : CollatzResearch.WordTrace tailWord_2551731 prefixEnd_2551731 873509669318707382951539 := by
  unfold tailWord_2551731
  simp only [CollatzResearch.WordTrace]
  refine ⟨93069275518521862804023047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62046183679014575202682031 93069275518521862804023047)
  ·
    refine ⟨139603913277782794206034571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93069275518521862804023047 139603913277782794206034571)
    ·
      refine ⟨209405869916674191309051857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139603913277782794206034571 209405869916674191309051857)
      ·
        refine ⟨157054402437505643481788893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209405869916674191309051857 157054402437505643481788893)
        ·
          refine ⟨58895400914064616305670835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157054402437505643481788893 58895400914064616305670835)
          ·
            refine ⟨88343101371096924458506253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58895400914064616305670835 88343101371096924458506253)
            ·
              refine ⟨33128663014161346671939845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88343101371096924458506253 33128663014161346671939845)
              ·
                refine ⟨6211624315155252500988721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33128663014161346671939845 6211624315155252500988721)
                ·
                  refine ⟨4658718236366439375741541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211624315155252500988721 4658718236366439375741541)
                  ·
                    refine ⟨873509669318707382951539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658718236366439375741541 873509669318707382951539)
                    ·
                      rfl

theorem cell22_2551731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_2551731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551731 prefixEnd_2551731 := by exact prefixLift 2551731
  have htrace : WordTrace (prefixWord ++ tailWord_2551731) baseStart_2551731 baseEnd_2551731 := by
    simpa [prefixWord, tailWord_2551731, baseEnd_2551731] using wordTrace_append hprefix tailTrace_2551731
  have hstable : (prefixWord ++ tailWord_2551731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551731).length < 2 ^ (prefixWord ++ tailWord_2551731).sum := by decide
  have hdescent : baseEnd_2551731 < baseStart_2551731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551765 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2551765 : Nat := 118140960795 + 2551765 * 2 ^ 59
def prefixEnd_2551765 : Nat := 4983230072969 + 3 ^ 40 * 2551765 * 2
def baseEnd_2551765 : Nat := 873521308213542627601435

theorem tailTrace_2551765 : CollatzResearch.WordTrace tailWord_2551765 prefixEnd_2551765 873521308213542627601435 := by
  unfold tailWord_2551765
  simp only [CollatzResearch.WordTrace]
  refine ⟨93070515600398686610760749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62047010400265791073840499 93070515600398686610760749)
  ·
    refine ⟨34901443350149507479035281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93070515600398686610760749 34901443350149507479035281)
    ·
      refine ⟨26176082512612130609276461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34901443350149507479035281 26176082512612130609276461)
      ·
        refine ⟨9816030942229548978478673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26176082512612130609276461 9816030942229548978478673)
        ·
          refine ⟨7362023206672161733859005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9816030942229548978478673 7362023206672161733859005)
          ·
            refine ⟨2760758702502060650197127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7362023206672161733859005 2760758702502060650197127)
            ·
              refine ⟨4141138053753090975295691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760758702502060650197127 4141138053753090975295691)
              ·
                refine ⟨6211707080629636462943537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141138053753090975295691 6211707080629636462943537)
                ·
                  refine ⟨4658780310472227347207653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211707080629636462943537 4658780310472227347207653)
                  ·
                    refine ⟨873521308213542627601435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658780310472227347207653 873521308213542627601435)
                    ·
                      rfl

theorem cell22_2551765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2551765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551765 prefixEnd_2551765 := by exact prefixLift 2551765
  have htrace : WordTrace (prefixWord ++ tailWord_2551765) baseStart_2551765 baseEnd_2551765 := by
    simpa [prefixWord, tailWord_2551765, baseEnd_2551765] using wordTrace_append hprefix tailTrace_2551765
  have hstable : (prefixWord ++ tailWord_2551765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551765).length < 2 ^ (prefixWord ++ tailWord_2551765).sum := by decide
  have hdescent : baseEnd_2551765 < baseStart_2551765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551791 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 7]
def baseStart_2551791 : Nat := 118140960795 + 2551791 * 2 ^ 59
def prefixEnd_2551791 : Nat := 4983230072969 + 3 ^ 40 * 2551791 * 2
def baseEnd_2551791 : Nat := 291176736181629075483785

theorem tailTrace_2551791 : CollatzResearch.WordTrace tailWord_2551791 prefixEnd_2551791 291176736181629075483785 := by
  unfold tailWord_2551791
  simp only [CollatzResearch.WordTrace]
  refine ⟨93071463898304493051207227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62047642598869662034138151 93071463898304493051207227)
  ·
    refine ⟨139607195847456739576810841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93071463898304493051207227 139607195847456739576810841)
    ·
      refine ⟨104705396885592554682608131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139607195847456739576810841 104705396885592554682608131)
      ·
        refine ⟨157058095328388832023912197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104705396885592554682608131 157058095328388832023912197)
        ·
          refine ⟨29448392874072906004483537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157058095328388832023912197 29448392874072906004483537)
          ·
            refine ⟨22086294655554679503362653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29448392874072906004483537 22086294655554679503362653)
            ·
              refine ⟨8282360495833004813760995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22086294655554679503362653 8282360495833004813760995)
              ·
                refine ⟨12423540743749507220641493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8282360495833004813760995 12423540743749507220641493)
                ·
                  refine ⟨291176736181629075483785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12423540743749507220641493 291176736181629075483785)
                  ·
                    rfl

theorem cell22_2551791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_2551791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551791 prefixEnd_2551791 := by exact prefixLift 2551791
  have htrace : WordTrace (prefixWord ++ tailWord_2551791) baseStart_2551791 baseEnd_2551791 := by
    simpa [prefixWord, tailWord_2551791, baseEnd_2551791] using wordTrace_append hprefix tailTrace_2551791
  have hstable : (prefixWord ++ tailWord_2551791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551791).length < 2 ^ (prefixWord ++ tailWord_2551791).sum := by decide
  have hdescent : baseEnd_2551791 < baseStart_2551791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551814 : List Nat := [6, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2551814 : Nat := 118140960795 + 2551814 * 2 ^ 59
def prefixEnd_2551814 : Nat := 4983230072969 + 3 ^ 40 * 2551814 * 2
def baseEnd_2551814 : Nat := 97059786879435870347365

theorem tailTrace_2551814 : CollatzResearch.WordTrace tailWord_2551814 prefixEnd_2551814 97059786879435870347365 := by
  unfold tailWord_2551814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908509461788161499352953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62048201851480778652862997 2908509461788161499352953)
  ·
    refine ⟨2181382096341121124514715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2908509461788161499352953 2181382096341121124514715)
    ·
      refine ⟨3272073144511681686772073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181382096341121124514715 3272073144511681686772073)
      ·
        refine ⟨2454054858383761265079055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3272073144511681686772073 2454054858383761265079055)
        ·
          refine ⟨3681082287575641897618583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454054858383761265079055 3681082287575641897618583)
          ·
            refine ⟨5521623431363462846427875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681082287575641897618583 5521623431363462846427875)
            ·
              refine ⟨8282435147045194269641813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5521623431363462846427875 8282435147045194269641813)
              ·
                refine ⟨97059786879435870347365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8282435147045194269641813 97059786879435870347365)
                ·
                  rfl

theorem cell22_2551814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2551814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551814 prefixEnd_2551814 := by exact prefixLift 2551814
  have htrace : WordTrace (prefixWord ++ tailWord_2551814) baseStart_2551814 baseEnd_2551814 := by
    simpa [prefixWord, tailWord_2551814, baseEnd_2551814] using wordTrace_append hprefix tailTrace_2551814
  have hstable : (prefixWord ++ tailWord_2551814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551814).length < 2 ^ (prefixWord ++ tailWord_2551814).sum := by decide
  have hdescent : baseEnd_2551814 < baseStart_2551814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551829 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_2551829 : Nat := 118140960795 + 2551829 * 2 ^ 59
def prefixEnd_2551829 : Nat := 4983230072969 + 3 ^ 40 * 2551829 * 2
def baseEnd_2551829 : Nat := 873543216721467794001239

theorem tailTrace_2551829 : CollatzResearch.WordTrace tailWord_2551829 prefixEnd_2551829 873543216721467794001239 := by
  unfold tailWord_2551829
  simp only [CollatzResearch.WordTrace]
  refine ⟨93072849872166825541090541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62048566581444550360727027 93072849872166825541090541)
  ·
    refine ⟨34902318702062559577908953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93072849872166825541090541 34902318702062559577908953)
    ·
      refine ⟨26176739026546919683431715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34902318702062559577908953 26176739026546919683431715)
      ·
        refine ⟨39265108539820379525147573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26176739026546919683431715 39265108539820379525147573)
        ·
          refine ⟨3681103925608160580482585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39265108539820379525147573 3681103925608160580482585)
          ·
            refine ⟨2760827944206120435361939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3681103925608160580482585 2760827944206120435361939)
            ·
              refine ⟨4141241916309180653042909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760827944206120435361939 4141241916309180653042909)
              ·
                refine ⟨1552965718615942744891091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4141241916309180653042909 1552965718615942744891091)
                ·
                  refine ⟨2329448577923914117336637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552965718615942744891091 2329448577923914117336637)
                  ·
                    refine ⟨873543216721467794001239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329448577923914117336637 873543216721467794001239)
                    ·
                      rfl

theorem cell22_2551829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_2551829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551829 prefixEnd_2551829 := by exact prefixLift 2551829
  have htrace : WordTrace (prefixWord ++ tailWord_2551829) baseStart_2551829 baseEnd_2551829 := by
    simpa [prefixWord, tailWord_2551829, baseEnd_2551829] using wordTrace_append hprefix tailTrace_2551829
  have hstable : (prefixWord ++ tailWord_2551829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551829).length < 2 ^ (prefixWord ++ tailWord_2551829).sum := by decide
  have hdescent : baseEnd_2551829 < baseStart_2551829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551851 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_2551851 : Nat := 118140960795 + 2551851 * 2 ^ 59
def prefixEnd_2551851 : Nat := 4983230072969 + 3 ^ 40 * 2551851 * 2
def baseEnd_2551851 : Nat := 873550747771067069951171

theorem tailTrace_2551851 : CollatzResearch.WordTrace tailWord_2551851 prefixEnd_2551851 873550747771067069951171 := by
  unfold tailWord_2551851
  simp only [CollatzResearch.WordTrace]
  refine ⟨93073652278087123298391407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62049101518724748865594271 93073652278087123298391407)
  ·
    refine ⟨139610478417130684947587111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93073652278087123298391407 139610478417130684947587111)
    ·
      refine ⟨209415717625696027421380667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139610478417130684947587111 209415717625696027421380667)
      ·
        refine ⟨314123576438544041132071001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209415717625696027421380667 314123576438544041132071001)
        ·
          refine ⟨235592682328908030849053251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314123576438544041132071001 235592682328908030849053251)
          ·
            refine ⟨353389023493362046273579877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235592682328908030849053251 353389023493362046273579877)
            ·
              refine ⟨66260441905005383676296227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353389023493362046273579877 66260441905005383676296227)
              ·
                refine ⟨99390662857508075514444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66260441905005383676296227 99390662857508075514444341)
                ·
                  refine ⟨9317874642891382079479157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99390662857508075514444341 9317874642891382079479157)
                  ·
                    refine ⟨873550747771067069951171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9317874642891382079479157 873550747771067069951171)
                    ·
                      rfl

theorem cell22_2551851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_2551851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551851 prefixEnd_2551851 := by exact prefixLift 2551851
  have htrace : WordTrace (prefixWord ++ tailWord_2551851) baseStart_2551851 baseEnd_2551851 := by
    simpa [prefixWord, tailWord_2551851, baseEnd_2551851] using wordTrace_append hprefix tailTrace_2551851
  have hstable : (prefixWord ++ tailWord_2551851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551851).length < 2 ^ (prefixWord ++ tailWord_2551851).sum := by decide
  have hdescent : baseEnd_2551851 < baseStart_2551851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551868 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_2551868 : Nat := 118140960795 + 2551868 * 2 ^ 59
def prefixEnd_2551868 : Nat := 4983230072969 + 3 ^ 40 * 2551868 * 2
def baseEnd_2551868 : Nat := 873556567218484692276119

theorem tailTrace_2551868 : CollatzResearch.WordTrace tailWord_2551868 prefixEnd_2551868 873556567218484692276119 := by
  unfold tailWord_2551868
  simp only [CollatzResearch.WordTrace]
  refine ⟨46537136159512767600880129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62049514879350356801173505 46537136159512767600880129)
  ·
    refine ⟨34902852119634575700660097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46537136159512767600880129 34902852119634575700660097)
    ·
      refine ⟨26177139089725931775495073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34902852119634575700660097 26177139089725931775495073)
      ·
        refine ⟨19632854317294448831621305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26177139089725931775495073 19632854317294448831621305)
        ·
          refine ⟨14724640737970836623715979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19632854317294448831621305 14724640737970836623715979)
          ·
            refine ⟨22086961106956254935573969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14724640737970836623715979 22086961106956254935573969)
            ·
              refine ⟨16565220830217191201680477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22086961106956254935573969 16565220830217191201680477)
              ·
                refine ⟨6211957811331446700630179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16565220830217191201680477 6211957811331446700630179)
                ·
                  refine ⟨9317936716997170050945269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6211957811331446700630179 9317936716997170050945269)
                  ·
                    refine ⟨873556567218484692276119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9317936716997170050945269 873556567218484692276119)
                    ·
                      rfl

theorem cell22_2551868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_2551868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551868 prefixEnd_2551868 := by exact prefixLift 2551868
  have htrace : WordTrace (prefixWord ++ tailWord_2551868) baseStart_2551868 baseEnd_2551868 := by
    simpa [prefixWord, tailWord_2551868, baseEnd_2551868] using wordTrace_append hprefix tailTrace_2551868
  have hstable : (prefixWord ++ tailWord_2551868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551868).length < 2 ^ (prefixWord ++ tailWord_2551868).sum := by decide
  have hdescent : baseEnd_2551868 < baseStart_2551868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551881 : List Nat := [1, 2, 1, 1, 2, 2, 3, 10]
def baseStart_2551881 : Nat := 118140960795 + 2551881 * 2 ^ 59
def prefixEnd_2551881 : Nat := 4983230072969 + 3 ^ 40 * 2551881 * 2
def baseEnd_2551881 : Nat := 97062335264906332411231

theorem tailTrace_2551881 : CollatzResearch.WordTrace tailWord_2551881 prefixEnd_2551881 97062335264906332411231 := by
  unfold tailWord_2551881
  simp only [CollatzResearch.WordTrace]
  refine ⟨93074746467978438421983497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62049830978652292281322331 93074746467978438421983497)
  ·
    refine ⟨69806059850983828816487623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93074746467978438421983497 69806059850983828816487623)
    ·
      refine ⟨104709089776475743224731435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69806059850983828816487623 104709089776475743224731435)
      ·
        refine ⟨157063634664713614837097153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104709089776475743224731435 157063634664713614837097153)
        ·
          refine ⟨117797725998535211127822865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157063634664713614837097153 117797725998535211127822865)
          ·
            refine ⟨88348294498901408345867149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117797725998535211127822865 88348294498901408345867149)
            ·
              refine ⟨33130610437088028129700181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88348294498901408345867149 33130610437088028129700181)
              ·
                refine ⟨97062335264906332411231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33130610437088028129700181 97062335264906332411231)
                ·
                  rfl

theorem cell22_2551881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 10].length) (baseStart_2551881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551881 prefixEnd_2551881 := by exact prefixLift 2551881
  have htrace : WordTrace (prefixWord ++ tailWord_2551881) baseStart_2551881 baseEnd_2551881 := by
    simpa [prefixWord, tailWord_2551881, baseEnd_2551881] using wordTrace_append hprefix tailTrace_2551881
  have hstable : (prefixWord ++ tailWord_2551881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551881).length < 2 ^ (prefixWord ++ tailWord_2551881).sum := by decide
  have hdescent : baseEnd_2551881 < baseStart_2551881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551885 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2551885 : Nat := 118140960795 + 2551885 * 2 ^ 59
def prefixEnd_2551885 : Nat := 4983230072969 + 3 ^ 40 * 2551885 * 2
def baseEnd_2551885 : Nat := 873562386665902314601067

theorem tailTrace_2551885 : CollatzResearch.WordTrace tailWord_2551885 prefixEnd_2551885 873562386665902314601067 := by
  unfold tailWord_2551885
  simp only [CollatzResearch.WordTrace]
  refine ⟨93074892359963947105129109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62049928239975964736752739 93074892359963947105129109)
  ·
    refine ⟨4362885579373310020552927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93074892359963947105129109 4362885579373310020552927)
    ·
      refine ⟨6544328369059965030829391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362885579373310020552927 6544328369059965030829391)
      ·
        refine ⟨9816492553589947546244087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544328369059965030829391 9816492553589947546244087)
        ·
          refine ⟨14724738830384921319366131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816492553589947546244087 14724738830384921319366131)
          ·
            refine ⟨22087108245577381979049197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14724738830384921319366131 22087108245577381979049197)
            ·
              refine ⟨8282665592091518242143449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22087108245577381979049197 8282665592091518242143449)
              ·
                refine ⟨6211999194068638681607587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8282665592091518242143449 6211999194068638681607587)
                ·
                  refine ⟨9317998791102958022411381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6211999194068638681607587 9317998791102958022411381)
                  ·
                    refine ⟨873562386665902314601067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9317998791102958022411381 873562386665902314601067)
                    ·
                      rfl

theorem cell22_2551885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2551885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551885 prefixEnd_2551885 := by exact prefixLift 2551885
  have htrace : WordTrace (prefixWord ++ tailWord_2551885) baseStart_2551885 baseEnd_2551885 := by
    simpa [prefixWord, tailWord_2551885, baseEnd_2551885] using wordTrace_append hprefix tailTrace_2551885
  have hstable : (prefixWord ++ tailWord_2551885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551885).length < 2 ^ (prefixWord ++ tailWord_2551885).sum := by decide
  have hdescent : baseEnd_2551885 < baseStart_2551885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551900 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2551900 : Nat := 118140960795 + 2551900 * 2 ^ 59
def prefixEnd_2551900 : Nat := 4983230072969 + 3 ^ 40 * 2551900 * 2
def baseEnd_2551900 : Nat := 873567521472447275476021

theorem tailTrace_2551900 : CollatzResearch.WordTrace tailWord_2551900 prefixEnd_2551900 873567521472447275476021 := by
  unfold tailWord_2551900
  simp only [CollatzResearch.WordTrace]
  refine ⟨46537719727454802333462577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62050292969939736444616769 46537719727454802333462577)
  ·
    refine ⟨34903289795591101750096933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46537719727454802333462577 34903289795591101750096933)
    ·
      refine ⟨6544366836673331578143175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34903289795591101750096933 6544366836673331578143175)
      ·
        refine ⟨9816550255009997367214763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544366836673331578143175 9816550255009997367214763)
        ·
          refine ⟨14724825382514996050822145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816550255009997367214763 14724825382514996050822145)
          ·
            refine ⟨11043619036886247038116609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14724825382514996050822145 11043619036886247038116609)
            ·
              refine ⟨8282714277664685278587457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11043619036886247038116609 8282714277664685278587457)
              ·
                refine ⟨6212035708248513958940593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8282714277664685278587457 6212035708248513958940593)
                ·
                  refine ⟨4659026781186385469205445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212035708248513958940593 4659026781186385469205445)
                  ·
                    refine ⟨873567521472447275476021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659026781186385469205445 873567521472447275476021)
                    ·
                      rfl

theorem cell22_2551900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2551900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551900 prefixEnd_2551900 := by exact prefixLift 2551900
  have htrace : WordTrace (prefixWord ++ tailWord_2551900) baseStart_2551900 baseEnd_2551900 := by
    simpa [prefixWord, tailWord_2551900, baseEnd_2551900] using wordTrace_append hprefix tailTrace_2551900
  have hstable : (prefixWord ++ tailWord_2551900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551900).length < 2 ^ (prefixWord ++ tailWord_2551900).sum := by decide
  have hdescent : baseEnd_2551900 < baseStart_2551900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551960 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_2551960 : Nat := 118140960795 + 2551960 * 2 ^ 59
def prefixEnd_2551960 : Nat := 4983230072969 + 3 ^ 40 * 2551960 * 2
def baseEnd_2551960 : Nat := 291196020232875706325279

theorem tailTrace_2551960 : CollatzResearch.WordTrace tailWord_2551960 prefixEnd_2551960 291196020232875706325279 := by
  unfold tailWord_2551960
  simp only [CollatzResearch.WordTrace]
  refine ⟨46538813917346117457054667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62051751889794823276072889 46538813917346117457054667)
  ·
    refine ⟨69808220876019176185582001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46538813917346117457054667 69808220876019176185582001)
    ·
      refine ⟨52356165657014382139186501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69808220876019176185582001 52356165657014382139186501)
      ·
        refine ⟨9816781060690196651097469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52356165657014382139186501 9816781060690196651097469)
        ·
          refine ⟨3681292897758823744161551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9816781060690196651097469 3681292897758823744161551)
          ·
            refine ⟨5521939346638235616242327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681292897758823744161551 5521939346638235616242327)
            ·
              refine ⟨8282909019957353424363491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5521939346638235616242327 8282909019957353424363491)
              ·
                refine ⟨12424363529936030136545237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8282909019957353424363491 12424363529936030136545237)
                ·
                  refine ⟨291196020232875706325279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12424363529936030136545237 291196020232875706325279)
                  ·
                    rfl

theorem cell22_2551960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_2551960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551960 prefixEnd_2551960 := by exact prefixLift 2551960
  have htrace : WordTrace (prefixWord ++ tailWord_2551960) baseStart_2551960 baseEnd_2551960 := by
    simpa [prefixWord, tailWord_2551960, baseEnd_2551960] using wordTrace_append hprefix tailTrace_2551960
  have hstable : (prefixWord ++ tailWord_2551960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551960).length < 2 ^ (prefixWord ++ tailWord_2551960).sum := by decide
  have hdescent : baseEnd_2551960 < baseStart_2551960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2551998 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_2551998 : Nat := 118140960795 + 2551998 * 2 ^ 59
def prefixEnd_2551998 : Nat := 4983230072969 + 3 ^ 40 * 2551998 * 2
def baseEnd_2551998 : Nat := 873601068875207686525721

theorem tailTrace_2551998 : CollatzResearch.WordTrace tailWord_2551998 prefixEnd_2551998 873601068875207686525721 := by
  unfold tailWord_2551998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634876726069320925499081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62052675872369711602661765 11634876726069320925499081)
  ·
    refine ⟨8726157544551990694124311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11634876726069320925499081 8726157544551990694124311)
    ·
      refine ⟨13089236316827986041186467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8726157544551990694124311 13089236316827986041186467)
      ·
        refine ⟨19633854475241979061779701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13089236316827986041186467 19633854475241979061779701)
        ·
          refine ⟨1840673857053935537041847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19633854475241979061779701 1840673857053935537041847)
          ·
            refine ⟨2761010785580903305562771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840673857053935537041847 2761010785580903305562771)
            ·
              refine ⟨4141516178371354958344157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761010785580903305562771 4141516178371354958344157)
              ·
                refine ⟨1553068566889258109379059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4141516178371354958344157 1553068566889258109379059)
                ·
                  refine ⟨2329602850333887164068589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553068566889258109379059 2329602850333887164068589)
                  ·
                    refine ⟨873601068875207686525721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329602850333887164068589 873601068875207686525721)
                    ·
                      rfl

theorem cell22_2551998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_2551998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2551998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2551998 prefixEnd_2551998 := by exact prefixLift 2551998
  have htrace : WordTrace (prefixWord ++ tailWord_2551998) baseStart_2551998 baseEnd_2551998 := by
    simpa [prefixWord, tailWord_2551998, baseEnd_2551998] using wordTrace_append hprefix tailTrace_2551998
  have hstable : (prefixWord ++ tailWord_2551998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2551998).length < 2 ^ (prefixWord ++ tailWord_2551998).sum := by decide
  have hdescent : baseEnd_2551998 < baseStart_2551998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2551998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552028 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_2552028 : Nat := 118140960795 + 2552028 * 2 ^ 59
def prefixEnd_2552028 : Nat := 4983230072969 + 3 ^ 40 * 2552028 * 2
def baseEnd_2552028 : Nat := 291203779496099202758543

theorem tailTrace_2552028 : CollatzResearch.WordTrace tailWord_2552028 prefixEnd_2552028 291203779496099202758543 := by
  unfold tailWord_2552028
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540053999222941263792369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62053405332297255018389825 46540053999222941263792369)
  ·
    refine ⟨34905040499417205947844277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46540053999222941263792369 34905040499417205947844277)
    ·
      refine ⟨3272347546820363057610401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34905040499417205947844277 3272347546820363057610401)
      ·
        refine ⟨2454260660115272293207801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3272347546820363057610401 2454260660115272293207801)
        ·
          refine ⟨1840695495086454219905851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2454260660115272293207801 1840695495086454219905851)
          ·
            refine ⟨2761043242629681329858777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840695495086454219905851 2761043242629681329858777)
            ·
              refine ⟨2070782431972260997394083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761043242629681329858777 2070782431972260997394083)
              ·
                refine ⟨3106173647958391496091125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070782431972260997394083 3106173647958391496091125)
                ·
                  refine ⟨291203779496099202758543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106173647958391496091125 291203779496099202758543)
                  ·
                    rfl

theorem cell22_2552028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_2552028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552028 prefixEnd_2552028 := by exact prefixLift 2552028
  have htrace : WordTrace (prefixWord ++ tailWord_2552028) baseStart_2552028 baseEnd_2552028 := by
    simpa [prefixWord, tailWord_2552028, baseEnd_2552028] using wordTrace_append hprefix tailTrace_2552028
  have hstable : (prefixWord ++ tailWord_2552028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552028).length < 2 ^ (prefixWord ++ tailWord_2552028).sum := by decide
  have hdescent : baseEnd_2552028 < baseStart_2552028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552048 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_2552048 : Nat := 118140960795 + 2552048 * 2 ^ 59
def prefixEnd_2552048 : Nat := 4983230072969 + 3 ^ 40 * 2552048 * 2
def baseEnd_2552048 : Nat := 873618184897024222775567

theorem tailTrace_2552048 : CollatzResearch.WordTrace tailWord_2552048 prefixEnd_2552048 873618184897024222775567 := by
  unfold tailWord_2552048
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540418729186712971656399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62053891638915617295541865 46540418729186712971656399)
  ·
    refine ⟨69810628093780069457484599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46540418729186712971656399 69810628093780069457484599)
    ·
      refine ⟨104715942140670104186226899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69810628093780069457484599 104715942140670104186226899)
      ·
        refine ⟨157073913211005156279340349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104715942140670104186226899 157073913211005156279340349)
        ·
          refine ⟨58902717454126933604752631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157073913211005156279340349 58902717454126933604752631)
          ·
            refine ⟨88354076181190400407128947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58902717454126933604752631 88354076181190400407128947)
            ·
              refine ⟨132531114271785600610693421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88354076181190400407128947 132531114271785600610693421)
              ·
                refine ⟨49699167851919600229010033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132531114271785600610693421 49699167851919600229010033)
                ·
                  refine ⟨37274375888939700171757525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49699167851919600229010033 37274375888939700171757525)
                  ·
                    refine ⟨873618184897024222775567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37274375888939700171757525 873618184897024222775567)
                    ·
                      rfl

theorem cell22_2552048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_2552048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552048 prefixEnd_2552048 := by exact prefixLift 2552048
  have htrace : WordTrace (prefixWord ++ tailWord_2552048) baseStart_2552048 baseEnd_2552048 := by
    simpa [prefixWord, tailWord_2552048, baseEnd_2552048] using wordTrace_append hprefix tailTrace_2552048
  have hstable : (prefixWord ++ tailWord_2552048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552048).length < 2 ^ (prefixWord ++ tailWord_2552048).sum := by decide
  have hdescent : baseEnd_2552048 < baseStart_2552048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552050 : List Nat := [3, 2, 1, 3, 2, 1, 2, 8]
def baseStart_2552050 : Nat := 118140960795 + 2552050 * 2 ^ 59
def prefixEnd_2552050 : Nat := 4983230072969 + 3 ^ 40 * 2552050 * 2
def baseEnd_2552050 : Nat := 97068763281988542691729

theorem tailTrace_2552050 : CollatzResearch.WordTrace tailWord_2552050 prefixEnd_2552050 97068763281988542691729 := by
  unfold tailWord_2552050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270227601091545071221401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62053940269577453523257069 23270227601091545071221401)
  ·
    refine ⟨17452670700818658803416051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23270227601091545071221401 17452670700818658803416051)
    ·
      refine ⟨26179006051227988205124077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17452670700818658803416051 26179006051227988205124077)
      ·
        refine ⟨9817127269210495576921529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26179006051227988205124077 9817127269210495576921529)
        ·
          refine ⟨7362845451907871682691147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9817127269210495576921529 7362845451907871682691147)
          ·
            refine ⟨11044268177861807524036721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362845451907871682691147 11044268177861807524036721)
            ·
              refine ⟨8283201133396355643027541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11044268177861807524036721 8283201133396355643027541)
              ·
                refine ⟨97068763281988542691729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8283201133396355643027541 97068763281988542691729)
                ·
                  rfl

theorem cell22_2552050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_2552050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552050 prefixEnd_2552050 := by exact prefixLift 2552050
  have htrace : WordTrace (prefixWord ++ tailWord_2552050) baseStart_2552050 baseEnd_2552050 := by
    simpa [prefixWord, tailWord_2552050, baseEnd_2552050] using wordTrace_append hprefix tailTrace_2552050
  have hstable : (prefixWord ++ tailWord_2552050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552050).length < 2 ^ (prefixWord ++ tailWord_2552050).sum := by decide
  have hdescent : baseEnd_2552050 < baseStart_2552050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552071 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2552071 : Nat := 118140960795 + 2552071 * 2 ^ 59
def prefixEnd_2552071 : Nat := 4983230072969 + 3 ^ 40 * 2552071 * 2
def baseEnd_2552071 : Nat := 873626058267059829450497

theorem tailTrace_2552071 : CollatzResearch.WordTrace tailWord_2552071 prefixEnd_2552071 873626058267059829450497 := by
  unfold tailWord_2552071
  simp only [CollatzResearch.WordTrace]
  refine ⟨93081676337290100871400067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62054450891526733914266711 93081676337290100871400067)
  ·
    refine ⟨139622514505935151307100101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93081676337290100871400067 139622514505935151307100101)
    ·
      refine ⟨26179221469862840870081269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139622514505935151307100101 26179221469862840870081269)
      ·
        refine ⟨2454302012799641331570119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26179221469862840870081269 2454302012799641331570119)
        ·
          refine ⟨3681453019199461997355179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454302012799641331570119 3681453019199461997355179)
          ·
            refine ⟨5522179528799192996032769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681453019199461997355179 5522179528799192996032769)
            ·
              refine ⟨4141634646599394747024577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5522179528799192996032769 4141634646599394747024577)
              ·
                refine ⟨3106225984949546060268433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4141634646599394747024577 3106225984949546060268433)
                ·
                  refine ⟨2329669488712159545201325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106225984949546060268433 2329669488712159545201325)
                  ·
                    refine ⟨873626058267059829450497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329669488712159545201325 873626058267059829450497)
                    ·
                      rfl

theorem cell22_2552071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2552071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552071 prefixEnd_2552071 := by exact prefixLift 2552071
  have htrace : WordTrace (prefixWord ++ tailWord_2552071) baseStart_2552071 baseEnd_2552071 := by
    simpa [prefixWord, tailWord_2552071, baseEnd_2552071] using wordTrace_append hprefix tailTrace_2552071
  have hstable : (prefixWord ++ tailWord_2552071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552071).length < 2 ^ (prefixWord ++ tailWord_2552071).sum := by decide
  have hdescent : baseEnd_2552071 < baseStart_2552071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552103 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2552103 : Nat := 118140960795 + 2552103 * 2 ^ 59
def prefixEnd_2552103 : Nat := 4983230072969 + 3 ^ 40 * 2552103 * 2
def baseEnd_2552103 : Nat := 873637012521022412650399

theorem tailTrace_2552103 : CollatzResearch.WordTrace tailWord_2552103 prefixEnd_2552103 873637012521022412650399 := by
  unfold tailWord_2552103
  simp only [CollatzResearch.WordTrace]
  refine ⟨93082843473174170336564963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62055228982116113557709975 93082843473174170336564963)
  ·
    refine ⟨139624265209761255504847445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93082843473174170336564963 139624265209761255504847445)
    ·
      refine ⟨1636221857926889712947431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 139624265209761255504847445 1636221857926889712947431)
      ·
        refine ⟨2454332786890334569421147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636221857926889712947431 2454332786890334569421147)
        ·
          refine ⟨3681499180335501854131721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454332786890334569421147 3681499180335501854131721)
          ·
            refine ⟨2761124385251626390598791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3681499180335501854131721 2761124385251626390598791)
            ·
              refine ⟨4141686577877439585898187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761124385251626390598791 4141686577877439585898187)
              ·
                refine ⟨6212529866816159378847281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141686577877439585898187 6212529866816159378847281)
                ·
                  refine ⟨4659397400112119534135461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212529866816159378847281 4659397400112119534135461)
                  ·
                    refine ⟨873637012521022412650399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659397400112119534135461 873637012521022412650399)
                    ·
                      rfl

theorem cell22_2552103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2552103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552103 prefixEnd_2552103 := by exact prefixLift 2552103
  have htrace : WordTrace (prefixWord ++ tailWord_2552103) baseStart_2552103 baseEnd_2552103 := by
    simpa [prefixWord, tailWord_2552103, baseEnd_2552103] using wordTrace_append hprefix tailTrace_2552103
  have hstable : (prefixWord ++ tailWord_2552103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552103).length < 2 ^ (prefixWord ++ tailWord_2552103).sum := by decide
  have hdescent : baseEnd_2552103 < baseStart_2552103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552116 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2552116 : Nat := 118140960795 + 2552116 * 2 ^ 59
def prefixEnd_2552116 : Nat := 4983230072969 + 3 ^ 40 * 2552116 * 2
def baseEnd_2552116 : Nat := 873641462686694712075359

theorem tailTrace_2552116 : CollatzResearch.WordTrace tailWord_2552116 prefixEnd_2552116 873641462686694712075359 := by
  unfold tailWord_2552116
  simp only [CollatzResearch.WordTrace]
  refine ⟨46541658811063536778394101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62055545081418049037858801 46541658811063536778394101)
  ·
    refine ⟨4363280513537206572974447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46541658811063536778394101 4363280513537206572974447)
    ·
      refine ⟨6544920770305809859461671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363280513537206572974447 6544920770305809859461671)
      ·
        refine ⟨9817381155458714789192507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544920770305809859461671 9817381155458714789192507)
        ·
          refine ⟨14726071733188072183788761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9817381155458714789192507 14726071733188072183788761)
          ·
            refine ⟨11044553799891054137841571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14726071733188072183788761 11044553799891054137841571)
            ·
              refine ⟨16566830699836581206762357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11044553799891054137841571 16566830699836581206762357)
              ·
                refine ⟨1553140378109679488133971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16566830699836581206762357 1553140378109679488133971)
                ·
                  refine ⟨2329710567164519232200957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553140378109679488133971 2329710567164519232200957)
                  ·
                    refine ⟨873641462686694712075359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329710567164519232200957 873641462686694712075359)
                    ·
                      rfl

theorem cell22_2552116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2552116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552116 prefixEnd_2552116 := by exact prefixLift 2552116
  have htrace : WordTrace (prefixWord ++ tailWord_2552116) baseStart_2552116 baseEnd_2552116 := by
    simpa [prefixWord, tailWord_2552116, baseEnd_2552116] using wordTrace_append hprefix tailTrace_2552116
  have hstable : (prefixWord ++ tailWord_2552116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552116).length < 2 ^ (prefixWord ++ tailWord_2552116).sum := by decide
  have hdescent : baseEnd_2552116 < baseStart_2552116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552187 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_2552187 : Nat := 118140960795 + 2552187 * 2 ^ 59
def prefixEnd_2552187 : Nat := 4983230072969 + 3 ^ 40 * 2552187 * 2
def baseEnd_2552187 : Nat := 873665767437674193550141

theorem tailTrace_2552187 : CollatzResearch.WordTrace tailWord_2552187 prefixEnd_2552187 873665767437674193550141 := by
  unfold tailWord_2552187
  simp only [CollatzResearch.WordTrace]
  refine ⟨93085907204869852682622815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62057271469913235121748543 93085907204869852682622815)
  ·
    refine ⟨139628860807304779023934223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93085907204869852682622815 139628860807304779023934223)
    ·
      refine ⟨209443291210957168535901335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139628860807304779023934223 209443291210957168535901335)
      ·
        refine ⟨314164936816435752803852003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209443291210957168535901335 314164936816435752803852003)
        ·
          refine ⟨471247405224653629205778005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314164936816435752803852003 471247405224653629205778005)
          ·
            refine ⟨5522430529976409717255211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 471247405224653629205778005 5522430529976409717255211)
            ·
              refine ⟨8283645794964614575882817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522430529976409717255211 8283645794964614575882817)
              ·
                refine ⟨6212734346223460931912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283645794964614575882817 6212734346223460931912113)
                ·
                  refine ⟨4659550759667595698934085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212734346223460931912113 4659550759667595698934085)
                  ·
                    refine ⟨873665767437674193550141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659550759667595698934085 873665767437674193550141)
                    ·
                      rfl

theorem cell22_2552187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_2552187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552187 prefixEnd_2552187 := by exact prefixLift 2552187
  have htrace : WordTrace (prefixWord ++ tailWord_2552187) baseStart_2552187 baseEnd_2552187 := by
    simpa [prefixWord, tailWord_2552187, baseEnd_2552187] using wordTrace_append hprefix tailTrace_2552187
  have hstable : (prefixWord ++ tailWord_2552187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552187).length < 2 ^ (prefixWord ++ tailWord_2552187).sum := by decide
  have hdescent : baseEnd_2552187 < baseStart_2552187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552206 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2552206 : Nat := 118140960795 + 2552206 * 2 ^ 59
def prefixEnd_2552206 : Nat := 4983230072969 + 3 ^ 40 * 2552206 * 2
def baseEnd_2552206 : Nat := 873672271525964477325083

theorem tailTrace_2552206 : CollatzResearch.WordTrace tailWord_2552206 prefixEnd_2552206 873672271525964477325083 := by
  unfold tailWord_2552206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635825023975127365945559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62057733461200679285042981 11635825023975127365945559)
  ·
    refine ⟨17453737535962691048918339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11635825023975127365945559 17453737535962691048918339)
    ·
      refine ⟨26180606303944036573377509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17453737535962691048918339 26180606303944036573377509)
      ·
        refine ⟨4908863681989506857508283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26180606303944036573377509 4908863681989506857508283)
        ·
          refine ⟨7363295522984260286262425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908863681989506857508283 7363295522984260286262425)
          ·
            refine ⟨5522471642238195214696819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7363295522984260286262425 5522471642238195214696819)
            ·
              refine ⟨8283707463357292822045229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522471642238195214696819 8283707463357292822045229)
              ·
                refine ⟨3106390298758984808266961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8283707463357292822045229 3106390298758984808266961)
                ·
                  refine ⟨2329792724069238606200221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106390298758984808266961 2329792724069238606200221)
                  ·
                    refine ⟨873672271525964477325083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329792724069238606200221 873672271525964477325083)
                    ·
                      rfl

theorem cell22_2552206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2552206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552206 prefixEnd_2552206 := by exact prefixLift 2552206
  have htrace : WordTrace (prefixWord ++ tailWord_2552206) baseStart_2552206 baseEnd_2552206 := by
    simpa [prefixWord, tailWord_2552206, baseEnd_2552206] using wordTrace_append hprefix tailTrace_2552206
  have hstable : (prefixWord ++ tailWord_2552206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552206).length < 2 ^ (prefixWord ++ tailWord_2552206).sum := by decide
  have hdescent : baseEnd_2552206 < baseStart_2552206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552217 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_2552217 : Nat := 118140960795 + 2552217 * 2 ^ 59
def prefixEnd_2552217 : Nat := 4983230072969 + 3 ^ 40 * 2552217 * 2
def baseEnd_2552217 : Nat := 873676037050764115300049

theorem tailTrace_2552217 : CollatzResearch.WordTrace tailWord_2552217 prefixEnd_2552217 873676037050764115300049 := by
  unfold tailWord_2552217
  simp only [CollatzResearch.WordTrace]
  refine ⟨93087001394761167806214905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62058000929840778537476603 93087001394761167806214905)
  ·
    refine ⟨69815251046070875854661179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93087001394761167806214905 69815251046070875854661179)
    ·
      refine ⟨104722876569106313781991769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69815251046070875854661179 104722876569106313781991769)
      ·
        refine ⟨78542157426829735336493827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104722876569106313781991769 78542157426829735336493827)
        ·
          refine ⟨117813236140244603004740741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78542157426829735336493827 117813236140244603004740741)
          ·
            refine ⟨22089981776295863063388889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117813236140244603004740741 22089981776295863063388889)
            ·
              refine ⟨16567486332221897297541667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22089981776295863063388889 16567486332221897297541667)
              ·
                refine ⟨24851229498332845946312501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16567486332221897297541667 24851229498332845946312501)
                ·
                  refine ⟨2329802765468704307466797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24851229498332845946312501 2329802765468704307466797)
                  ·
                    refine ⟨873676037050764115300049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329802765468704307466797 873676037050764115300049)
                    ·
                      rfl

theorem cell22_2552217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_2552217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552217 prefixEnd_2552217 := by exact prefixLift 2552217
  have htrace : WordTrace (prefixWord ++ tailWord_2552217) baseStart_2552217 baseEnd_2552217 := by
    simpa [prefixWord, tailWord_2552217, baseEnd_2552217] using wordTrace_append hprefix tailTrace_2552217
  have hstable : (prefixWord ++ tailWord_2552217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552217).length < 2 ^ (prefixWord ++ tailWord_2552217).sum := by decide
  have hdescent : baseEnd_2552217 < baseStart_2552217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552247 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 5]
def baseStart_2552247 : Nat := 118140960795 + 2552247 * 2 ^ 59
def prefixEnd_2552247 : Nat := 4983230072969 + 3 ^ 40 * 2552247 * 2
def baseEnd_2552247 : Nat := 291228768887951345683319

theorem tailTrace_2552247 : CollatzResearch.WordTrace tailWord_2552247 prefixEnd_2552247 291228768887951345683319 := by
  unfold tailWord_2552247
  simp only [CollatzResearch.WordTrace]
  refine ⟨93088095584652482929806995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62058730389768321953204663 93088095584652482929806995)
  ·
    refine ⟨139632143376978724394710493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93088095584652482929806995 139632143376978724394710493)
    ·
      refine ⟨52362053766367021648016435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139632143376978724394710493 52362053766367021648016435)
      ·
        refine ⟨78543080649550532472024653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52362053766367021648016435 78543080649550532472024653)
        ·
          refine ⟨29453655243581449677009245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78543080649550532472024653 29453655243581449677009245)
          ·
            refine ⟨11045120716343043628878467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29453655243581449677009245 11045120716343043628878467)
            ·
              refine ⟨16567681074514565443317701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045120716343043628878467 16567681074514565443317701)
              ·
                refine ⟨3106440201471481020622069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16567681074514565443317701 3106440201471481020622069)
                ·
                  refine ⟨291228768887951345683319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106440201471481020622069 291228768887951345683319)
                  ·
                    rfl

theorem cell22_2552247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 5].length) (baseStart_2552247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552247 prefixEnd_2552247 := by exact prefixLift 2552247
  have htrace : WordTrace (prefixWord ++ tailWord_2552247) baseStart_2552247 baseEnd_2552247 := by
    simpa [prefixWord, tailWord_2552247, baseEnd_2552247] using wordTrace_append hprefix tailTrace_2552247
  have hstable : (prefixWord ++ tailWord_2552247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552247).length < 2 ^ (prefixWord ++ tailWord_2552247).sum := by decide
  have hdescent : baseEnd_2552247 < baseStart_2552247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552478 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2552478 : Nat := 118140960795 + 2552478 * 2 ^ 59
def prefixEnd_2552478 : Nat := 4983230072969 + 3 ^ 40 * 2552478 * 2
def baseEnd_2552478 : Nat := 291255127561548811508083

theorem tailTrace_2552478 : CollatzResearch.WordTrace tailWord_2552478 prefixEnd_2552478 291255127561548811508083 := by
  unfold tailWord_2552478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11637065105851951172683261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62064347231210406254310725 11637065105851951172683261)
  ·
    refine ⟨4363899414694481689756223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11637065105851951172683261 4363899414694481689756223)
    ·
      refine ⟨6545849122041722534634335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363899414694481689756223 6545849122041722534634335)
      ·
        refine ⟨9818773683062583801951503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545849122041722534634335 9818773683062583801951503)
        ·
          refine ⟨14728160524593875702927255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9818773683062583801951503 14728160524593875702927255)
          ·
            refine ⟨22092240786890813554390883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14728160524593875702927255 22092240786890813554390883)
            ·
              refine ⟨33138361180336220331586325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22092240786890813554390883 33138361180336220331586325)
              ·
                refine ⟨1553360680328260328043109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33138361180336220331586325 1553360680328260328043109)
                ·
                  refine ⟨291255127561548811508083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553360680328260328043109 291255127561548811508083)
                  ·
                    rfl

theorem cell22_2552478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2552478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552478 prefixEnd_2552478 := by exact prefixLift 2552478
  have htrace : WordTrace (prefixWord ++ tailWord_2552478) baseStart_2552478 baseEnd_2552478 := by
    simpa [prefixWord, tailWord_2552478, baseEnd_2552478] using wordTrace_append hprefix tailTrace_2552478
  have hstable : (prefixWord ++ tailWord_2552478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552478).length < 2 ^ (prefixWord ++ tailWord_2552478).sum := by decide
  have hdescent : baseEnd_2552478 < baseStart_2552478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552493 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2552493 : Nat := 118140960795 + 2552493 * 2 ^ 59
def prefixEnd_2552493 : Nat := 4983230072969 + 3 ^ 40 * 2552493 * 2
def baseEnd_2552493 : Nat := 873770517491191395399203

theorem tailTrace_2552493 : CollatzResearch.WordTrace tailWord_2552493 prefixEnd_2552493 873770517491191395399203 := by
  unfold tailWord_2552493
  simp only [CollatzResearch.WordTrace]
  refine ⟨93097067941761266943262133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62064711961174177962174755 93097067941761266943262133)
  ·
    refine ⟨8727850119540118775930825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93097067941761266943262133 8727850119540118775930825)
    ·
      refine ⟨6545887589655089081948119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8727850119540118775930825 6545887589655089081948119)
      ·
        refine ⟨9818831384482633622922179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545887589655089081948119 9818831384482633622922179)
        ·
          refine ⟨14728247076723950434383269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9818831384482633622922179 14728247076723950434383269)
          ·
            refine ⟨2761546326885740706446863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14728247076723950434383269 2761546326885740706446863)
            ·
              refine ⟨4142319490328611059670295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761546326885740706446863 4142319490328611059670295)
              ·
                refine ⟨6213479235492916589505443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142319490328611059670295 6213479235492916589505443)
                ·
                  refine ⟨9320218853239374884258165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213479235492916589505443 9320218853239374884258165)
                  ·
                    refine ⟨873770517491191395399203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9320218853239374884258165 873770517491191395399203)
                    ·
                      rfl

theorem cell22_2552493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2552493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552493 prefixEnd_2552493 := by exact prefixLift 2552493
  have htrace : WordTrace (prefixWord ++ tailWord_2552493) baseStart_2552493 baseEnd_2552493 := by
    simpa [prefixWord, tailWord_2552493, baseEnd_2552493] using wordTrace_append hprefix tailTrace_2552493
  have hstable : (prefixWord ++ tailWord_2552493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552493).length < 2 ^ (prefixWord ++ tailWord_2552493).sum := by decide
  have hdescent : baseEnd_2552493 < baseStart_2552493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552525 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2552525 : Nat := 118140960795 + 2552525 * 2 ^ 59
def prefixEnd_2552525 : Nat := 4983230072969 + 3 ^ 40 * 2552525 * 2
def baseEnd_2552525 : Nat := 873781471745153978599105

theorem tailTrace_2552525 : CollatzResearch.WordTrace tailWord_2552525 prefixEnd_2552525 873781471745153978599105 := by
  unfold tailWord_2552525
  simp only [CollatzResearch.WordTrace]
  refine ⟨93098235077645336408427029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62065490051763557605618019 93098235077645336408427029)
  ·
    refine ⟨4363979769264625144145017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93098235077645336408427029 4363979769264625144145017)
    ·
      refine ⟨3272984826948468858108763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4363979769264625144145017 3272984826948468858108763)
      ·
        refine ⟨4909477240422703287163145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272984826948468858108763 4909477240422703287163145)
        ·
          refine ⟨3682107930317027465372359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4909477240422703287163145 3682107930317027465372359)
          ·
            refine ⟨5523161895475541198058539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682107930317027465372359 5523161895475541198058539)
            ·
              refine ⟨8284742843213311797087809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523161895475541198058539 8284742843213311797087809)
              ·
                refine ⟨6213557132409983847815857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8284742843213311797087809 6213557132409983847815857)
                ·
                  refine ⟨4660167849307487885861893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6213557132409983847815857 4660167849307487885861893)
                  ·
                    refine ⟨873781471745153978599105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660167849307487885861893 873781471745153978599105)
                    ·
                      rfl

theorem cell22_2552525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2552525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552525 prefixEnd_2552525 := by exact prefixLift 2552525
  have htrace : WordTrace (prefixWord ++ tailWord_2552525) baseStart_2552525 baseEnd_2552525 := by
    simpa [prefixWord, tailWord_2552525, baseEnd_2552525] using wordTrace_append hprefix tailTrace_2552525
  have hstable : (prefixWord ++ tailWord_2552525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552525).length < 2 ^ (prefixWord ++ tailWord_2552525).sum := by decide
  have hdescent : baseEnd_2552525 < baseStart_2552525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552581 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2552581 : Nat := 118140960795 + 2552581 * 2 ^ 59
def prefixEnd_2552581 : Nat := 4983230072969 + 3 ^ 40 * 2552581 * 2
def baseEnd_2552581 : Nat := 873800641689588499198933

theorem tailTrace_2552581 : CollatzResearch.WordTrace tailWord_2552581 prefixEnd_2552581 873800641689588499198933 := by
  unfold tailWord_2552581
  simp only [CollatzResearch.WordTrace]
  refine ⟨93100277565442457972465597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62066851710294971981643731 93100277565442457972465597)
  ·
    refine ⟨34912604087040921739674599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93100277565442457972465597 34912604087040921739674599)
    ·
      refine ⟨52368906130561382609511899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34912604087040921739674599 52368906130561382609511899)
      ·
        refine ⟨78553359195842073914267849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52368906130561382609511899 78553359195842073914267849)
        ·
          refine ⟨58915019396881555435700887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78553359195842073914267849 58915019396881555435700887)
          ·
            refine ⟨88372529095322333153551331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58915019396881555435700887 88372529095322333153551331)
            ·
              refine ⟨132558793642983499730326997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88372529095322333153551331 132558793642983499730326997)
              ·
                refine ⟨3106846726007425774929539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132558793642983499730326997 3106846726007425774929539)
                ·
                  refine ⟨4660270089011138662394309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106846726007425774929539 4660270089011138662394309)
                  ·
                    refine ⟨873800641689588499198933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660270089011138662394309 873800641689588499198933)
                    ·
                      rfl

theorem cell22_2552581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2552581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552581 prefixEnd_2552581 := by exact prefixLift 2552581
  have htrace : WordTrace (prefixWord ++ tailWord_2552581) baseStart_2552581 baseEnd_2552581 := by
    simpa [prefixWord, tailWord_2552581, baseEnd_2552581] using wordTrace_append hprefix tailTrace_2552581
  have hstable : (prefixWord ++ tailWord_2552581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552581).length < 2 ^ (prefixWord ++ tailWord_2552581).sum := by decide
  have hdescent : baseEnd_2552581 < baseStart_2552581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552611 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 6, 3]
def baseStart_2552611 : Nat := 118140960795 + 2552611 * 2 ^ 59
def prefixEnd_2552611 : Nat := 4983230072969 + 3 ^ 40 * 2552611 * 2
def baseEnd_2552611 : Nat := 873810911302678420948841

theorem tailTrace_2552611 : CollatzResearch.WordTrace tailWord_2552611 prefixEnd_2552611 873810911302678420948841 := by
  unfold tailWord_2552611
  simp only [CollatzResearch.WordTrace]
  refine ⟨93101371755333773096057687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62067581170222515397371791 93101371755333773096057687)
  ·
    refine ⟨139652057633000659644086531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93101371755333773096057687 139652057633000659644086531)
    ·
      refine ⟨209478086449500989466129797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139652057633000659644086531 209478086449500989466129797)
      ·
        refine ⟨39277141209281435524899337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209478086449500989466129797 39277141209281435524899337)
        ·
          refine ⟨29457855906961076643674503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39277141209281435524899337 29457855906961076643674503)
          ·
            refine ⟨44186783860441614965511755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29457855906961076643674503 44186783860441614965511755)
            ·
              refine ⟨66280175790662422448267633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44186783860441614965511755 66280175790662422448267633)
              ·
                refine ⟨49710131842996816836200725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66280175790662422448267633 49710131842996816836200725)
                ·
                  refine ⟨2330162430140475789196909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49710131842996816836200725 2330162430140475789196909)
                  ·
                    refine ⟨873810911302678420948841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330162430140475789196909 873810911302678420948841)
                    ·
                      rfl

theorem cell22_2552611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3].length) (baseStart_2552611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552611 prefixEnd_2552611 := by exact prefixLift 2552611
  have htrace : WordTrace (prefixWord ++ tailWord_2552611) baseStart_2552611 baseEnd_2552611 := by
    simpa [prefixWord, tailWord_2552611, baseEnd_2552611] using wordTrace_append hprefix tailTrace_2552611
  have hstable : (prefixWord ++ tailWord_2552611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552611).length < 2 ^ (prefixWord ++ tailWord_2552611).sum := by decide
  have hdescent : baseEnd_2552611 < baseStart_2552611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552624 : List Nat := [2, 1, 1, 1, 2, 2, 1, 12]
def baseStart_2552624 : Nat := 118140960795 + 2552624 * 2 ^ 59
def prefixEnd_2552624 : Nat := 4983230072969 + 3 ^ 40 * 2552624 * 2
def baseEnd_2552624 : Nat := 97090595718705635597089

theorem tailTrace_2552624 : CollatzResearch.WordTrace tailWord_2552624 prefixEnd_2552624 97090595718705635597089 := by
  unfold tailWord_2552624
  simp only [CollatzResearch.WordTrace]
  refine ⟨46550922952143338158140463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62067897269524450877520617 46550922952143338158140463)
  ·
    refine ⟨69826384428215007237210695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46550922952143338158140463 69826384428215007237210695)
    ·
      refine ⟨104739576642322510855816043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69826384428215007237210695 104739576642322510855816043)
      ·
        refine ⟨157109364963483766283724065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104739576642322510855816043 157109364963483766283724065)
        ·
          refine ⟨117832023722612824712793049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157109364963483766283724065 117832023722612824712793049)
          ·
            refine ⟨88374017791959618534594787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117832023722612824712793049 88374017791959618534594787)
            ·
              refine ⟨132561026687939427801892181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88374017791959618534594787 132561026687939427801892181)
              ·
                refine ⟨97090595718705635597089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 132561026687939427801892181 97090595718705635597089)
                ·
                  rfl

theorem cell22_2552624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_2552624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552624 prefixEnd_2552624 := by exact prefixLift 2552624
  have htrace : WordTrace (prefixWord ++ tailWord_2552624) baseStart_2552624 baseEnd_2552624 := by
    simpa [prefixWord, tailWord_2552624, baseEnd_2552624] using wordTrace_append hprefix tailTrace_2552624
  have hstable : (prefixWord ++ tailWord_2552624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552624).length < 2 ^ (prefixWord ++ tailWord_2552624).sum := by decide
  have hdescent : baseEnd_2552624 < baseStart_2552624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552626 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2552626 : Nat := 118140960795 + 2552626 * 2 ^ 59
def prefixEnd_2552626 : Nat := 4983230072969 + 3 ^ 40 * 2552626 * 2
def baseEnd_2552626 : Nat := 873816046109223381823795

theorem tailTrace_2552626 : CollatzResearch.WordTrace tailWord_2552626 prefixEnd_2552626 873816046109223381823795 := by
  unfold tailWord_2552626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275479712569857664463433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62067945900186287105235821 23275479712569857664463433)
  ·
    refine ⟨17456609784427393248347575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23275479712569857664463433 17456609784427393248347575)
    ·
      refine ⟨26184914676641089872521363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17456609784427393248347575 26184914676641089872521363)
      ·
        refine ⟨39277372014961634808782045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26184914676641089872521363 39277372014961634808782045)
        ·
          refine ⟨14729014505610613053293267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39277372014961634808782045 14729014505610613053293267)
          ·
            refine ⟨22093521758415919579939901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729014505610613053293267 22093521758415919579939901)
            ·
              refine ⟨8285070659405969842477463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22093521758415919579939901 8285070659405969842477463)
              ·
                refine ⟨12427605989108954763716195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285070659405969842477463 12427605989108954763716195)
                ·
                  refine ⟨18641408983663432145574293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12427605989108954763716195 18641408983663432145574293)
                  ·
                    refine ⟨873816046109223381823795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18641408983663432145574293 873816046109223381823795)
                    ·
                      rfl

theorem cell22_2552626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2552626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552626 prefixEnd_2552626 := by exact prefixLift 2552626
  have htrace : WordTrace (prefixWord ++ tailWord_2552626) baseStart_2552626 baseEnd_2552626 := by
    simpa [prefixWord, tailWord_2552626, baseEnd_2552626] using wordTrace_append hprefix tailTrace_2552626
  have hstable : (prefixWord ++ tailWord_2552626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552626).length < 2 ^ (prefixWord ++ tailWord_2552626).sum := by decide
  have hdescent : baseEnd_2552626 < baseStart_2552626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552701 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2552701 : Nat := 118140960795 + 2552701 * 2 ^ 59
def prefixEnd_2552701 : Nat := 4983230072969 + 3 ^ 40 * 2552701 * 2
def baseEnd_2552701 : Nat := 873841720141948186198565

theorem tailTrace_2552701 : CollatzResearch.WordTrace tailWord_2552701 prefixEnd_2552701 873841720141948186198565 := by
  unfold tailWord_2552701
  simp only [CollatzResearch.WordTrace]
  refine ⟨93104654325007718466833957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62069769550005145644555971 93104654325007718466833957)
  ·
    refine ⟨17457122685938947212531367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93104654325007718466833957 17457122685938947212531367)
    ·
      refine ⟨26185684028908420818797051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17457122685938947212531367 26185684028908420818797051)
      ·
        refine ⟨39278526043362631228195577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26185684028908420818797051 39278526043362631228195577)
        ·
          refine ⟨29458894532521973421146683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39278526043362631228195577 29458894532521973421146683)
          ·
            refine ⟨44188341798782960131720025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29458894532521973421146683 44188341798782960131720025)
            ·
              refine ⟨33141256349087220098790019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44188341798782960131720025 33141256349087220098790019)
              ·
                refine ⟨49711884523630830148185029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33141256349087220098790019 49711884523630830148185029)
                ·
                  refine ⟨9320978348180780652784693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49711884523630830148185029 9320978348180780652784693)
                  ·
                    refine ⟨873841720141948186198565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9320978348180780652784693 873841720141948186198565)
                    ·
                      rfl

theorem cell22_2552701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2552701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552701 prefixEnd_2552701 := by exact prefixLift 2552701
  have htrace : WordTrace (prefixWord ++ tailWord_2552701) baseStart_2552701 baseEnd_2552701 := by
    simpa [prefixWord, tailWord_2552701, baseEnd_2552701] using wordTrace_append hprefix tailTrace_2552701
  have hstable : (prefixWord ++ tailWord_2552701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552701).length < 2 ^ (prefixWord ++ tailWord_2552701).sum := by decide
  have hdescent : baseEnd_2552701 < baseStart_2552701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552707 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 1, 3]
def baseStart_2552707 : Nat := 118140960795 + 2552707 * 2 ^ 59
def prefixEnd_2552707 : Nat := 4983230072969 + 3 ^ 40 * 2552707 * 2
def baseEnd_2552707 : Nat := 873843774064566170548547

theorem tailTrace_2552707 : CollatzResearch.WordTrace tailWord_2552707 prefixEnd_2552707 873843774064566170548547 := by
  unfold tailWord_2552707
  simp only [CollatzResearch.WordTrace]
  refine ⟨93104873162985981491552375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62069915441990654327701583 93104873162985981491552375)
  ·
    refine ⟨139657309744478972237328563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93104873162985981491552375 139657309744478972237328563)
    ·
      refine ⟨209485964616718458355992845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139657309744478972237328563 209485964616718458355992845)
      ·
        refine ⟨78557236731269421883497317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209485964616718458355992845 78557236731269421883497317)
        ·
          refine ⟨14729481887113016603155747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78557236731269421883497317 14729481887113016603155747)
          ·
            refine ⟨22094222830669524904733621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729481887113016603155747 22094222830669524904733621)
            ·
              refine ⟨2071333390375267959818777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22094222830669524904733621 2071333390375267959818777)
              ·
                refine ⟨1553500042781450969864083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071333390375267959818777 1553500042781450969864083)
                ·
                  refine ⟨2330250064172176454796125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553500042781450969864083 2330250064172176454796125)
                  ·
                    refine ⟨873843774064566170548547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330250064172176454796125 873843774064566170548547)
                    ·
                      rfl

theorem cell22_2552707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 3].length) (baseStart_2552707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552707 prefixEnd_2552707 := by exact prefixLift 2552707
  have htrace : WordTrace (prefixWord ++ tailWord_2552707) baseStart_2552707 baseEnd_2552707 := by
    simpa [prefixWord, tailWord_2552707, baseEnd_2552707] using wordTrace_append hprefix tailTrace_2552707
  have hstable : (prefixWord ++ tailWord_2552707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552707).length < 2 ^ (prefixWord ++ tailWord_2552707).sum := by decide
  have hdescent : baseEnd_2552707 < baseStart_2552707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552733 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2552733 : Nat := 118140960795 + 2552733 * 2 ^ 59
def prefixEnd_2552733 : Nat := 4983230072969 + 3 ^ 40 * 2552733 * 2
def baseEnd_2552733 : Nat := 873852674395910769398467

theorem tailTrace_2552733 : CollatzResearch.WordTrace tailWord_2552733 prefixEnd_2552733 873852674395910769398467 := by
  unfold tailWord_2552733
  simp only [CollatzResearch.WordTrace]
  refine ⟨93105821460891787931998853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62070547640594525287999235 93105821460891787931998853)
  ·
    refine ⟨17457341523917210237249785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93105821460891787931998853 17457341523917210237249785)
    ·
      refine ⟨13093006142937907677937339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17457341523917210237249785 13093006142937907677937339)
      ·
        refine ⟨19639509214406861516906009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13093006142937907677937339 19639509214406861516906009)
        ·
          refine ⟨14729631910805146137679507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19639509214406861516906009 14729631910805146137679507)
          ·
            refine ⟨22094447866207719206519261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729631910805146137679507 22094447866207719206519261)
            ·
              refine ⟨8285417949827894702444723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22094447866207719206519261 8285417949827894702444723)
              ·
                refine ⟨12428126924741842053667085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285417949827894702444723 12428126924741842053667085)
                ·
                  refine ⟨4660547596778190770125157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12428126924741842053667085 4660547596778190770125157)
                  ·
                    refine ⟨873852674395910769398467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660547596778190770125157 873852674395910769398467)
                    ·
                      rfl

theorem cell22_2552733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2552733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552733 prefixEnd_2552733 := by exact prefixLift 2552733
  have htrace : WordTrace (prefixWord ++ tailWord_2552733) baseStart_2552733 baseEnd_2552733 := by
    simpa [prefixWord, tailWord_2552733, baseEnd_2552733] using wordTrace_append hprefix tailTrace_2552733
  have hstable : (prefixWord ++ tailWord_2552733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552733).length < 2 ^ (prefixWord ++ tailWord_2552733).sum := by decide
  have hdescent : baseEnd_2552733 < baseStart_2552733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552758 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2552758 : Nat := 118140960795 + 2552758 * 2 ^ 59
def prefixEnd_2552758 : Nat := 4983230072969 + 3 ^ 40 * 2552758 * 2
def baseEnd_2552758 : Nat := 873861232406819037523391

theorem tailTrace_2552758 : CollatzResearch.WordTrace tailWord_2552758 prefixEnd_2552758 873861232406819037523391 := by
  unfold tailWord_2552758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819170830362576075103683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62071155523867478134439285 5819170830362576075103683)
  ·
    refine ⟨8728756245543864112655525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5819170830362576075103683 8728756245543864112655525)
    ·
      refine ⟨1636641796039474521122911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8728756245543864112655525 1636641796039474521122911)
      ·
        refine ⟨2454962694059211781684367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636641796039474521122911 2454962694059211781684367)
        ·
          refine ⟨3682444041088817672526551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454962694059211781684367 3682444041088817672526551)
          ·
            refine ⟨5523666061633226508789827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682444041088817672526551 5523666061633226508789827)
            ·
              refine ⟨8285499092449839763184741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523666061633226508789827 8285499092449839763184741)
              ·
                refine ⟨1553531079834344955597139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8285499092449839763184741 1553531079834344955597139)
                ·
                  refine ⟨2330296619751517433395709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553531079834344955597139 2330296619751517433395709)
                  ·
                    refine ⟨873861232406819037523391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330296619751517433395709 873861232406819037523391)
                    ·
                      rfl

theorem cell22_2552758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2552758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552758 prefixEnd_2552758 := by exact prefixLift 2552758
  have htrace : WordTrace (prefixWord ++ tailWord_2552758) baseStart_2552758 baseEnd_2552758 := by
    simpa [prefixWord, tailWord_2552758, baseEnd_2552758] using wordTrace_append hprefix tailTrace_2552758
  have hstable : (prefixWord ++ tailWord_2552758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552758).length < 2 ^ (prefixWord ++ tailWord_2552758).sum := by decide
  have hdescent : baseEnd_2552758 < baseStart_2552758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552780 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_2552780 : Nat := 118140960795 + 2552780 * 2 ^ 59
def prefixEnd_2552780 : Nat := 4983230072969 + 3 ^ 40 * 2552780 * 2
def baseEnd_2552780 : Nat := 873868763456418313473323

theorem tailTrace_2552780 : CollatzResearch.WordTrace tailWord_2552780 prefixEnd_2552780 873868763456418313473323 := by
  unfold tailWord_2552780
  simp only [CollatzResearch.WordTrace]
  refine ⟨46553767845860757479479897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62071690461147676639306529 46553767845860757479479897)
  ·
    refine ⟨34915325884395568109609923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46553767845860757479479897 34915325884395568109609923)
    ·
      refine ⟨52372988826593352164414885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34915325884395568109609923 52372988826593352164414885)
      ·
        refine ⟨9819935404986253530827791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52372988826593352164414885 9819935404986253530827791)
        ·
          refine ⟨14729903107479380296241687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9819935404986253530827791 14729903107479380296241687)
          ·
            refine ⟨22094854661219070444362531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729903107479380296241687 22094854661219070444362531)
            ·
              refine ⟨33142281991828605666543797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22094854661219070444362531 33142281991828605666543797)
              ·
                refine ⟨3107088936733931781238481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33142281991828605666543797 3107088936733931781238481)
                ·
                  refine ⟨2330316702550448835928861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3107088936733931781238481 2330316702550448835928861)
                  ·
                    refine ⟨873868763456418313473323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330316702550448835928861 873868763456418313473323)
                    ·
                      rfl

theorem cell22_2552780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_2552780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552780 prefixEnd_2552780 := by exact prefixLift 2552780
  have htrace : WordTrace (prefixWord ++ tailWord_2552780) baseStart_2552780 baseEnd_2552780 := by
    simpa [prefixWord, tailWord_2552780, baseEnd_2552780] using wordTrace_append hprefix tailTrace_2552780
  have hstable : (prefixWord ++ tailWord_2552780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552780).length < 2 ^ (prefixWord ++ tailWord_2552780).sum := by decide
  have hdescent : baseEnd_2552780 < baseStart_2552780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552791 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2552791 : Nat := 118140960795 + 2552791 * 2 ^ 59
def prefixEnd_2552791 : Nat := 4983230072969 + 3 ^ 40 * 2552791 * 2
def baseEnd_2552791 : Nat := 873872528981217951448289

theorem tailTrace_2552791 : CollatzResearch.WordTrace tailWord_2552791 prefixEnd_2552791 873872528981217951448289 := by
  unfold tailWord_2552791
  simp only [CollatzResearch.WordTrace]
  refine ⟨93107936894681663837610227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62071957929787775891740151 93107936894681663837610227)
  ·
    refine ⟨139661905342022495756415341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93107936894681663837610227 139661905342022495756415341)
    ·
      refine ⟨52373214503258435908655753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139661905342022495756415341 52373214503258435908655753)
      ·
        refine ⟨39279910877443826931491815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52373214503258435908655753 39279910877443826931491815)
        ·
          refine ⟨58919866316165740397237723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39279910877443826931491815 58919866316165740397237723)
          ·
            refine ⟨88379799474248610595856585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58919866316165740397237723 88379799474248610595856585)
            ·
              refine ⟨66284849605686457946892439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88379799474248610595856585 66284849605686457946892439)
              ·
                refine ⟨99427274408529686920338659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66284849605686457946892439 99427274408529686920338659)
                ·
                  refine ⟨149140911612794530380507989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99427274408529686920338659 149140911612794530380507989)
                  ·
                    refine ⟨873872528981217951448289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 149140911612794530380507989 873872528981217951448289)
                    ·
                      rfl

theorem cell22_2552791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2552791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552791 prefixEnd_2552791 := by exact prefixLift 2552791
  have htrace : WordTrace (prefixWord ++ tailWord_2552791) baseStart_2552791 baseEnd_2552791 := by
    simpa [prefixWord, tailWord_2552791, baseEnd_2552791] using wordTrace_append hprefix tailTrace_2552791
  have hstable : (prefixWord ++ tailWord_2552791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552791).length < 2 ^ (prefixWord ++ tailWord_2552791).sum := by decide
  have hdescent : baseEnd_2552791 < baseStart_2552791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552814 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_2552814 : Nat := 118140960795 + 2552814 * 2 ^ 59
def prefixEnd_2552814 : Nat := 4983230072969 + 3 ^ 40 * 2552814 * 2
def baseEnd_2552814 : Nat := 873880402351253558123219

theorem tailTrace_2552814 : CollatzResearch.WordTrace tailWord_2552814 prefixEnd_2552814 873880402351253558123219 := by
  unfold tailWord_2552814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638596971699792345712187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62072517182398892510464997 11638596971699792345712187)
  ·
    refine ⟨17457895457549688518568281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11638596971699792345712187 17457895457549688518568281)
    ·
      refine ⟨13093421593162266388926211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17457895457549688518568281 13093421593162266388926211)
      ·
        refine ⟨19640132389743399583389317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13093421593162266388926211 19640132389743399583389317)
        ·
          refine ⟨3682524823076887421885497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19640132389743399583389317 3682524823076887421885497)
          ·
            refine ⟨2761893617307665566414123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3682524823076887421885497 2761893617307665566414123)
            ·
              refine ⟨4142840425961498349621185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761893617307665566414123 4142840425961498349621185)
              ·
                refine ⟨3107130319471123762215889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4142840425961498349621185 3107130319471123762215889)
                ·
                  refine ⟨2330347739603342821661917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3107130319471123762215889 2330347739603342821661917)
                  ·
                    refine ⟨873880402351253558123219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330347739603342821661917 873880402351253558123219)
                    ·
                      rfl

theorem cell22_2552814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_2552814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552814 prefixEnd_2552814 := by exact prefixLift 2552814
  have htrace : WordTrace (prefixWord ++ tailWord_2552814) baseStart_2552814 baseEnd_2552814 := by
    simpa [prefixWord, tailWord_2552814, baseEnd_2552814] using wordTrace_append hprefix tailTrace_2552814
  have hstable : (prefixWord ++ tailWord_2552814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552814).length < 2 ^ (prefixWord ++ tailWord_2552814).sum := by decide
  have hdescent : baseEnd_2552814 < baseStart_2552814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552825 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_2552825 : Nat := 118140960795 + 2552825 * 2 ^ 59
def prefixEnd_2552825 : Nat := 4983230072969 + 3 ^ 40 * 2552825 * 2
def baseEnd_2552825 : Nat := 873884167876053196098185

theorem tailTrace_2552825 : CollatzResearch.WordTrace tailWord_2552825 prefixEnd_2552825 873884167876053196098185 := by
  unfold tailWord_2552825
  simp only [CollatzResearch.WordTrace]
  refine ⟨93109176976558487644347929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62072784651038991762898619 93109176976558487644347929)
  ·
    refine ⟨69831882732418865733260947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93109176976558487644347929 69831882732418865733260947)
    ·
      refine ⟨104747824098628298599891421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69831882732418865733260947 104747824098628298599891421)
      ·
        refine ⟨39280434036985611974959283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104747824098628298599891421 39280434036985611974959283)
        ·
          refine ⟨58920651055478417962438925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39280434036985611974959283 58920651055478417962438925)
          ·
            refine ⟨22095244145804406735914597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58920651055478417962438925 22095244145804406735914597)
            ·
              refine ⟨4142858277338326262983987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22095244145804406735914597 4142858277338326262983987)
              ·
                refine ⟨6214287416007489394475981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142858277338326262983987 6214287416007489394475981)
                ·
                  refine ⟨2330357781002808522928493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6214287416007489394475981 2330357781002808522928493)
                  ·
                    refine ⟨873884167876053196098185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330357781002808522928493 873884167876053196098185)
                    ·
                      rfl

theorem cell22_2552825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_2552825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552825 prefixEnd_2552825 := by exact prefixLift 2552825
  have htrace : WordTrace (prefixWord ++ tailWord_2552825) baseStart_2552825 baseEnd_2552825 := by
    simpa [prefixWord, tailWord_2552825, baseEnd_2552825] using wordTrace_append hprefix tailTrace_2552825
  have hstable : (prefixWord ++ tailWord_2552825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552825).length < 2 ^ (prefixWord ++ tailWord_2552825).sum := by decide
  have hdescent : baseEnd_2552825 < baseStart_2552825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552913 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2552913 : Nat := 118140960795 + 2552913 * 2 ^ 59
def prefixEnd_2552913 : Nat := 4983230072969 + 3 ^ 40 * 2552913 * 2
def baseEnd_2552913 : Nat := 873914292074450299897915

theorem tailTrace_2552913 : CollatzResearch.WordTrace tailWord_2552913 prefixEnd_2552913 873914292074450299897915 := by
  unfold tailWord_2552913
  simp only [CollatzResearch.WordTrace]
  refine ⟨93112386600239678673551393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62074924400159785782367595 93112386600239678673551393)
  ·
    refine ⟨69834289950179759005163545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93112386600239678673551393 69834289950179759005163545)
    ·
      refine ⟨52375717462634819253872659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69834289950179759005163545 52375717462634819253872659)
      ·
        refine ⟨78563576193952228880808989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52375717462634819253872659 78563576193952228880808989)
        ·
          refine ⟨29461341072732085830303371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78563576193952228880808989 29461341072732085830303371)
          ·
            refine ⟨44192011609098128745455057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29461341072732085830303371 44192011609098128745455057)
            ·
              refine ⟨33144008706823596559091293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44192011609098128745455057 33144008706823596559091293)
              ·
                refine ⟨12429003265058848709659235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33144008706823596559091293 12429003265058848709659235)
                ·
                  refine ⟨18643504897588273064488853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12429003265058848709659235 18643504897588273064488853)
                  ·
                    refine ⟨873914292074450299897915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18643504897588273064488853 873914292074450299897915)
                    ·
                      rfl

theorem cell22_2552913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2552913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552913 prefixEnd_2552913 := by exact prefixLift 2552913
  have htrace : WordTrace (prefixWord ++ tailWord_2552913) baseStart_2552913 baseEnd_2552913 := by
    simpa [prefixWord, tailWord_2552913, baseEnd_2552913] using wordTrace_append hprefix tailTrace_2552913
  have hstable : (prefixWord ++ tailWord_2552913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552913).length < 2 ^ (prefixWord ++ tailWord_2552913).sum := by decide
  have hdescent : baseEnd_2552913 < baseStart_2552913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552949 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2552949 : Nat := 118140960795 + 2552949 * 2 ^ 59
def prefixEnd_2552949 : Nat := 4983230072969 + 3 ^ 40 * 2552949 * 2
def baseEnd_2552949 : Nat := 873926615610158205997805

theorem tailTrace_2552949 : CollatzResearch.WordTrace tailWord_2552949 prefixEnd_2552949 873926615610158205997805 := by
  unfold tailWord_2552949
  simp only [CollatzResearch.WordTrace]
  refine ⟨93113699628109256821861901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62075799752072837881241267 93113699628109256821861901)
  ·
    refine ⟨34917637360540971308198213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93113699628109256821861901 34917637360540971308198213)
    ·
      refine ⟨6547057005101432120287165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34917637360540971308198213 6547057005101432120287165)
      ·
        refine ⟨2455146376913037045107687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6547057005101432120287165 2455146376913037045107687)
        ·
          refine ⟨3682719565369555567661531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455146376913037045107687 3682719565369555567661531)
          ·
            refine ⟨5524079348054333351492297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682719565369555567661531 5524079348054333351492297)
            ·
              refine ⟨4143059511040750013619223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5524079348054333351492297 4143059511040750013619223)
              ·
                refine ⟨6214589266561125020428835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143059511040750013619223 6214589266561125020428835)
                ·
                  refine ⟨9321883899841687530643253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6214589266561125020428835 9321883899841687530643253)
                  ·
                    refine ⟨873926615610158205997805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9321883899841687530643253 873926615610158205997805)
                    ·
                      rfl

theorem cell22_2552949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2552949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552949 prefixEnd_2552949 := by exact prefixLift 2552949
  have htrace : WordTrace (prefixWord ++ tailWord_2552949) baseStart_2552949 baseEnd_2552949 := by
    simpa [prefixWord, tailWord_2552949, baseEnd_2552949] using wordTrace_append hprefix tailTrace_2552949
  have hstable : (prefixWord ++ tailWord_2552949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552949).length < 2 ^ (prefixWord ++ tailWord_2552949).sum := by decide
  have hdescent : baseEnd_2552949 < baseStart_2552949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2552960 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_2552960 : Nat := 118140960795 + 2552960 * 2 ^ 59
def prefixEnd_2552960 : Nat := 4983230072969 + 3 ^ 40 * 2552960 * 2
def baseEnd_2552960 : Nat := 873930381134957843972771

theorem tailTrace_2552960 : CollatzResearch.WordTrace tailWord_2552960 prefixEnd_2552960 873930381134957843972771 := by
  unfold tailWord_2552960
  simp only [CollatzResearch.WordTrace]
  refine ⟨46557050415534702850256167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62076067220712937133674889 46557050415534702850256167)
  ·
    refine ⟨69835575623302054275384251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46557050415534702850256167 69835575623302054275384251)
    ·
      refine ⟨104753363434953081413076377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69835575623302054275384251 104753363434953081413076377)
      ·
        refine ⟨78565022576214811059807283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104753363434953081413076377 78565022576214811059807283)
        ·
          refine ⟨117847533864322216589710925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78565022576214811059807283 117847533864322216589710925)
          ·
            refine ⟨44192825199120831221141597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117847533864322216589710925 44192825199120831221141597)
            ·
              refine ⟨16572309449670311707928099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44192825199120831221141597 16572309449670311707928099)
              ·
                refine ⟨24858464174505467561892149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16572309449670311707928099 24858464174505467561892149)
                ·
                  refine ⟨2330481016359887583927389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24858464174505467561892149 2330481016359887583927389)
                  ·
                    refine ⟨873930381134957843972771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330481016359887583927389 873930381134957843972771)
                    ·
                      rfl

theorem cell22_2552960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_2552960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2552960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2552960 prefixEnd_2552960 := by exact prefixLift 2552960
  have htrace : WordTrace (prefixWord ++ tailWord_2552960) baseStart_2552960 baseEnd_2552960 := by
    simpa [prefixWord, tailWord_2552960, baseEnd_2552960] using wordTrace_append hprefix tailTrace_2552960
  have hstable : (prefixWord ++ tailWord_2552960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2552960).length < 2 ^ (prefixWord ++ tailWord_2552960).sum := by decide
  have hdescent : baseEnd_2552960 < baseStart_2552960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2552960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553028 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2553028 : Nat := 118140960795 + 2553028 * 2 ^ 59
def prefixEnd_2553028 : Nat := 4983230072969 + 3 ^ 40 * 2553028 * 2
def baseEnd_2553028 : Nat := 873953658924628333272563

theorem tailTrace_2553028 : CollatzResearch.WordTrace tailWord_2553028 prefixEnd_2553028 873953658924628333272563 := by
  unfold tailWord_2553028
  simp only [CollatzResearch.WordTrace]
  refine ⟨46558290497411526656993869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62077720663215368875991825 46558290497411526656993869)
  ·
    refine ⟨17459358936529322496372701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46558290497411526656993869 17459358936529322496372701)
    ·
      refine ⟨6547259601198495936139763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17459358936529322496372701 6547259601198495936139763)
      ·
        refine ⟨9820889401797743904209645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6547259601198495936139763 9820889401797743904209645)
        ·
          refine ⟨3682833525674153964078617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9820889401797743904209645 3682833525674153964078617)
          ·
            refine ⟨2762125144255615473058963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3682833525674153964078617 2762125144255615473058963)
            ·
              refine ⟨4143187716383423209588445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762125144255615473058963 4143187716383423209588445)
              ·
                refine ⟨1553695393643783703595667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4143187716383423209588445 1553695393643783703595667)
                ·
                  refine ⟨2330543090465675555393501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553695393643783703595667 2330543090465675555393501)
                  ·
                    refine ⟨873953658924628333272563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330543090465675555393501 873953658924628333272563)
                    ·
                      rfl

theorem cell22_2553028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2553028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553028 prefixEnd_2553028 := by exact prefixLift 2553028
  have htrace : WordTrace (prefixWord ++ tailWord_2553028) baseStart_2553028 baseEnd_2553028 := by
    simpa [prefixWord, tailWord_2553028, baseEnd_2553028] using wordTrace_append hprefix tailTrace_2553028
  have hstable : (prefixWord ++ tailWord_2553028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553028).length < 2 ^ (prefixWord ++ tailWord_2553028).sum := by decide
  have hdescent : baseEnd_2553028 < baseStart_2553028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553071 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 1, 4]
def baseStart_2553071 : Nat := 118140960795 + 2553071 * 2 ^ 59
def prefixEnd_2553071 : Nat := 4983230072969 + 3 ^ 40 * 2553071 * 2
def baseEnd_2553071 : Nat := 873968378703390554447431

theorem tailTrace_2553071 : CollatzResearch.WordTrace tailWord_2553071 prefixEnd_2553071 873968378703390554447431 := by
  unfold tailWord_2553071
  simp only [CollatzResearch.WordTrace]
  refine ⟨93118149333667271657803067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62078766222444847771868711 93118149333667271657803067)
  ·
    refine ⟨139677224000500907486704601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93118149333667271657803067 139677224000500907486704601)
    ·
      refine ⟨104757918000375680615028451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139677224000500907486704601 104757918000375680615028451)
      ·
        refine ⟨157136877000563520922542677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104757918000375680615028451 157136877000563520922542677)
        ·
          refine ⟨1841447777350353760811047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 157136877000563520922542677 1841447777350353760811047)
          ·
            refine ⟨2762171666025530641216571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841447777350353760811047 2762171666025530641216571)
            ·
              refine ⟨4143257499038295961824857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762171666025530641216571 4143257499038295961824857)
              ·
                refine ⟨3107443124278721971368643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143257499038295961824857 3107443124278721971368643)
                ·
                  refine ⟨4661164686418082957052965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107443124278721971368643 4661164686418082957052965)
                  ·
                    refine ⟨873968378703390554447431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661164686418082957052965 873968378703390554447431)
                    ·
                      rfl

theorem cell22_2553071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_2553071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553071 prefixEnd_2553071 := by exact prefixLift 2553071
  have htrace : WordTrace (prefixWord ++ tailWord_2553071) baseStart_2553071 baseEnd_2553071 := by
    simpa [prefixWord, tailWord_2553071, baseEnd_2553071] using wordTrace_append hprefix tailTrace_2553071
  have hstable : (prefixWord ++ tailWord_2553071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553071).length < 2 ^ (prefixWord ++ tailWord_2553071).sum := by decide
  have hdescent : baseEnd_2553071 < baseStart_2553071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553082 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_2553082 : Nat := 118140960795 + 2553082 * 2 ^ 59
def prefixEnd_2553082 : Nat := 4983230072969 + 3 ^ 40 * 2553082 * 2
def baseEnd_2553082 : Nat := 873972144228190192422397

theorem tailTrace_2553082 : CollatzResearch.WordTrace tailWord_2553082 prefixEnd_2553082 873972144228190192422397 := by
  unfold tailWord_2553082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23279637634156855134113375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62079033691084947024302333 23279637634156855134113375)
  ·
    refine ⟨34919456451235282701170063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23279637634156855134113375 34919456451235282701170063)
    ·
      refine ⟨52379184676852924051755095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34919456451235282701170063 52379184676852924051755095)
      ·
        refine ⟨78568777015279386077632643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52379184676852924051755095 78568777015279386077632643)
        ·
          refine ⟨117853165522919079116448965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78568777015279386077632643 117853165522919079116448965)
          ·
            refine ⟨22097468535547327334334181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117853165522919079116448965 22097468535547327334334181)
            ·
              refine ⟨4143275350415123875187659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22097468535547327334334181 4143275350415123875187659)
              ·
                refine ⟨6214913025622685812781489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143275350415123875187659 6214913025622685812781489)
                ·
                  refine ⟨4661184769217014359586117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6214913025622685812781489 4661184769217014359586117)
                  ·
                    refine ⟨873972144228190192422397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661184769217014359586117 873972144228190192422397)
                    ·
                      rfl

theorem cell22_2553082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_2553082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553082 prefixEnd_2553082 := by exact prefixLift 2553082
  have htrace : WordTrace (prefixWord ++ tailWord_2553082) baseStart_2553082 baseEnd_2553082 := by
    simpa [prefixWord, tailWord_2553082, baseEnd_2553082] using wordTrace_append hprefix tailTrace_2553082
  have hstable : (prefixWord ++ tailWord_2553082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553082).length < 2 ^ (prefixWord ++ tailWord_2553082).sum := by decide
  have hdescent : baseEnd_2553082 < baseStart_2553082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553146 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_2553146 : Nat := 118140960795 + 2553146 * 2 ^ 59
def prefixEnd_2553146 : Nat := 4983230072969 + 3 ^ 40 * 2553146 * 2
def baseEnd_2553146 : Nat := 873994052736115358822201

theorem tailTrace_2553146 : CollatzResearch.WordTrace tailWord_2553146 prefixEnd_2553146 873994052736115358822201 := by
  unfold tailWord_2553146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23280221202098889866695823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62080589872263706311188861 23280221202098889866695823)
  ·
    refine ⟨34920331803148334800043735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23280221202098889866695823 34920331803148334800043735)
    ·
      refine ⟨52380497704722502200065603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34920331803148334800043735 52380497704722502200065603)
      ·
        refine ⟨78570746557083753300098405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52380497704722502200065603 78570746557083753300098405)
        ·
          refine ⟨14732014979453203743768451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78570746557083753300098405 14732014979453203743768451)
          ·
            refine ⟨22098022469179805615652677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14732014979453203743768451 22098022469179805615652677)
            ·
              refine ⟨4143379212971213552934877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22098022469179805615652677 4143379212971213552934877)
              ·
                refine ⟨1553767204864205082350579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4143379212971213552934877 1553767204864205082350579)
                ·
                  refine ⟨2330650807296307623525869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553767204864205082350579 2330650807296307623525869)
                  ·
                    refine ⟨873994052736115358822201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330650807296307623525869 873994052736115358822201)
                    ·
                      rfl

theorem cell22_2553146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_2553146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553146 prefixEnd_2553146 := by exact prefixLift 2553146
  have htrace : WordTrace (prefixWord ++ tailWord_2553146) baseStart_2553146 baseEnd_2553146 := by
    simpa [prefixWord, tailWord_2553146, baseEnd_2553146] using wordTrace_append hprefix tailTrace_2553146
  have hstable : (prefixWord ++ tailWord_2553146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553146).length < 2 ^ (prefixWord ++ tailWord_2553146).sum := by decide
  have hdescent : baseEnd_2553146 < baseStart_2553146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553159 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 5]
def baseStart_2553159 : Nat := 118140960795 + 2553159 * 2 ^ 59
def prefixEnd_2553159 : Nat := 4983230072969 + 3 ^ 40 * 2553159 * 2
def baseEnd_2553159 : Nat := 291332834300595886082387

theorem tailTrace_2553159 : CollatzResearch.WordTrace tailWord_2553159 prefixEnd_2553159 291332834300595886082387 := by
  unfold tailWord_2553159
  simp only [CollatzResearch.WordTrace]
  refine ⟨93121358957348462687006531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62080905971565641791337687 93121358957348462687006531)
  ·
    refine ⟨139682038436022694030509797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93121358957348462687006531 139682038436022694030509797)
    ·
      refine ⟨26190382206754255130720587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139682038436022694030509797 26190382206754255130720587)
      ·
        refine ⟨39285573310131382696080881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26190382206754255130720587 39285573310131382696080881)
        ·
          refine ⟨29464179982598537022060661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39285573310131382696080881 29464179982598537022060661)
          ·
            refine ⟨2762266873368612845818187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29464179982598537022060661 2762266873368612845818187)
            ·
              refine ⟨4143400310052919268727281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762266873368612845818187 4143400310052919268727281)
              ·
                refine ⟨3107550232539689451545461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143400310052919268727281 3107550232539689451545461)
                ·
                  refine ⟨291332834300595886082387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3107550232539689451545461 291332834300595886082387)
                  ·
                    rfl

theorem cell22_2553159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 5].length) (baseStart_2553159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553159 prefixEnd_2553159 := by exact prefixLift 2553159
  have htrace : WordTrace (prefixWord ++ tailWord_2553159) baseStart_2553159 baseEnd_2553159 := by
    simpa [prefixWord, tailWord_2553159, baseEnd_2553159] using wordTrace_append hprefix tailTrace_2553159
  have hstable : (prefixWord ++ tailWord_2553159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553159).length < 2 ^ (prefixWord ++ tailWord_2553159).sum := by decide
  have hdescent : baseEnd_2553159 < baseStart_2553159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553187 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 6]
def baseStart_2553187 : Nat := 118140960795 + 2553187 * 2 ^ 59
def prefixEnd_2553187 : Nat := 4983230072969 + 3 ^ 40 * 2553187 * 2
def baseEnd_2553187 : Nat := 291336029291334972849025

theorem tailTrace_2553187 : CollatzResearch.WordTrace tailWord_2553187 prefixEnd_2553187 291336029291334972849025 := by
  unfold tailWord_2553187
  simp only [CollatzResearch.WordTrace]
  refine ⟨93122380201247023469025815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62081586800831348979350543 93122380201247023469025815)
  ·
    refine ⟨139683570301870535203538723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93122380201247023469025815 139683570301870535203538723)
    ·
      refine ⟨209525355452805802805308085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139683570301870535203538723 209525355452805802805308085)
      ·
        refine ⟨19643002073700544012997633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209525355452805802805308085 19643002073700544012997633)
        ·
          refine ⟨14732251555275408009748225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19643002073700544012997633 14732251555275408009748225)
          ·
            refine ⟨11049188666456556007311169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14732251555275408009748225 11049188666456556007311169)
            ·
              refine ⟨8286891499842417005483377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11049188666456556007311169 8286891499842417005483377)
              ·
                refine ⟨6215168624881812754112533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8286891499842417005483377 6215168624881812754112533)
                ·
                  refine ⟨291336029291334972849025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6215168624881812754112533 291336029291334972849025)
                  ·
                    rfl

theorem cell22_2553187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_2553187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553187 prefixEnd_2553187 := by exact prefixLift 2553187
  have htrace : WordTrace (prefixWord ++ tailWord_2553187) baseStart_2553187 baseEnd_2553187 := by
    simpa [prefixWord, tailWord_2553187, baseEnd_2553187] using wordTrace_append hprefix tailTrace_2553187
  have hstable : (prefixWord ++ tailWord_2553187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553187).length < 2 ^ (prefixWord ++ tailWord_2553187).sum := by decide
  have hdescent : baseEnd_2553187 < baseStart_2553187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553189 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2553189 : Nat := 118140960795 + 2553189 * 2 ^ 59
def prefixEnd_2553189 : Nat := 4983230072969 + 3 ^ 40 * 2553189 * 2
def baseEnd_2553189 : Nat := 874008772514877579997069

theorem tailTrace_2553189 : CollatzResearch.WordTrace tailWord_2553189 prefixEnd_2553189 874008772514877579997069 := by
  unfold tailWord_2553189
  simp only [CollatzResearch.WordTrace]
  refine ⟨93122453147239777810598621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62081635431493185207065747 93122453147239777810598621)
  ·
    refine ⟨34920919930214916678974483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93122453147239777810598621 34920919930214916678974483)
    ·
      refine ⟨52381379895322375018461725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34920919930214916678974483 52381379895322375018461725)
      ·
        refine ⟨19643017460745890631923147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52381379895322375018461725 19643017460745890631923147)
        ·
          refine ⟨29464526191118835947884721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19643017460745890631923147 29464526191118835947884721)
          ·
            refine ⟨22098394643339126960913541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29464526191118835947884721 22098394643339126960913541)
            ·
              refine ⟨4143448995626086305171289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22098394643339126960913541 4143448995626086305171289)
              ·
                refine ⟨3107586746719564728878467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143448995626086305171289 3107586746719564728878467)
                ·
                  refine ⟨4661380120079347093317701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107586746719564728878467 4661380120079347093317701)
                  ·
                    refine ⟨874008772514877579997069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661380120079347093317701 874008772514877579997069)
                    ·
                      rfl

theorem cell22_2553189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2553189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553189 prefixEnd_2553189 := by exact prefixLift 2553189
  have htrace : WordTrace (prefixWord ++ tailWord_2553189) baseStart_2553189 baseEnd_2553189 := by
    simpa [prefixWord, tailWord_2553189, baseEnd_2553189] using wordTrace_append hprefix tailTrace_2553189
  have hstable : (prefixWord ++ tailWord_2553189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553189).length < 2 ^ (prefixWord ++ tailWord_2553189).sum := by decide
  have hdescent : baseEnd_2553189 < baseStart_2553189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553202 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2553202 : Nat := 118140960795 + 2553202 * 2 ^ 59
def prefixEnd_2553202 : Nat := 4983230072969 + 3 ^ 40 * 2553202 * 2
def baseEnd_2553202 : Nat := 874013222680549879422029

theorem tailTrace_2553202 : CollatzResearch.WordTrace tailWord_2553202 prefixEnd_2553202 874013222680549879422029 := by
  unfold tailWord_2553202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23280731824048170257705465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62081951530795120687214573 23280731824048170257705465)
  ·
    refine ⟨17460548868036127693279099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23280731824048170257705465 17460548868036127693279099)
    ·
      refine ⟨26190823302054191539918649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17460548868036127693279099 26190823302054191539918649)
      ·
        refine ⟨19643117476540643654938987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26190823302054191539918649 19643117476540643654938987)
        ·
          refine ⟨29464676214810965482408481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19643117476540643654938987 29464676214810965482408481)
          ·
            refine ⟨22098507161108224111806361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29464676214810965482408481 22098507161108224111806361)
            ·
              refine ⟨16573880370831168083854771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22098507161108224111806361 16573880370831168083854771)
              ·
                refine ⟨24860820556246752125782157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16573880370831168083854771 24860820556246752125782157)
                ·
                  refine ⟨9322807708592532047168309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24860820556246752125782157 9322807708592532047168309)
                  ·
                    refine ⟨874013222680549879422029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9322807708592532047168309 874013222680549879422029)
                    ·
                      rfl

theorem cell22_2553202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2553202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553202 prefixEnd_2553202 := by exact prefixLift 2553202
  have htrace : WordTrace (prefixWord ++ tailWord_2553202) baseStart_2553202 baseEnd_2553202 := by
    simpa [prefixWord, tailWord_2553202, baseEnd_2553202] using wordTrace_append hprefix tailTrace_2553202
  have hstable : (prefixWord ++ tailWord_2553202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553202).length < 2 ^ (prefixWord ++ tailWord_2553202).sum := by decide
  have hdescent : baseEnd_2553202 < baseStart_2553202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553219 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 4, 3]
def baseStart_2553219 : Nat := 118140960795 + 2553219 * 2 ^ 59
def prefixEnd_2553219 : Nat := 4983230072969 + 3 ^ 40 * 2553219 * 2
def baseEnd_2553219 : Nat := 874019042127967501746977

theorem tailTrace_2553219 : CollatzResearch.WordTrace tailWord_2553219 prefixEnd_2553219 874019042127967501746977 := by
  unfold tailWord_2553219
  simp only [CollatzResearch.WordTrace]
  refine ⟨93123547337131092934190711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62082364891420728622793807 93123547337131092934190711)
  ·
    refine ⟨139685321005696639401286067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93123547337131092934190711 139685321005696639401286067)
    ·
      refine ⟨209527981508544959101929101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139685321005696639401286067 209527981508544959101929101)
      ·
        refine ⟨78572993065704359663223413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209527981508544959101929101 78572993065704359663223413)
        ·
          refine ⟨7366218099909783718427195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78572993065704359663223413 7366218099909783718427195)
          ·
            refine ⟨11049327149864675577640793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366218099909783718427195 11049327149864675577640793)
            ·
              refine ⟨8286995362398506683230595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11049327149864675577640793 8286995362398506683230595)
              ·
                refine ⟨12430493043597760024845893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8286995362398506683230595 12430493043597760024845893)
                ·
                  refine ⟨2330717445674580004658605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12430493043597760024845893 2330717445674580004658605)
                  ·
                    refine ⟨874019042127967501746977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330717445674580004658605 874019042127967501746977)
                    ·
                      rfl

theorem cell22_2553219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3].length) (baseStart_2553219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553219 prefixEnd_2553219 := by exact prefixLift 2553219
  have htrace : WordTrace (prefixWord ++ tailWord_2553219) baseStart_2553219 baseEnd_2553219 := by
    simpa [prefixWord, tailWord_2553219, baseEnd_2553219] using wordTrace_append hprefix tailTrace_2553219
  have hstable : (prefixWord ++ tailWord_2553219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553219).length < 2 ^ (prefixWord ++ tailWord_2553219).sum := by decide
  have hdescent : baseEnd_2553219 < baseStart_2553219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553294 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_2553294 : Nat := 118140960795 + 2553294 * 2 ^ 59
def prefixEnd_2553294 : Nat := 4983230072969 + 3 ^ 40 * 2553294 * 2
def baseEnd_2553294 : Nat := 291348238720230768707249

theorem tailTrace_2553294 : CollatzResearch.WordTrace tailWord_2553294 prefixEnd_2553294 291348238720230768707249 := by
  unfold tailWord_2553294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11640785351482422592896367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62084188541239587162113957 11640785351482422592896367)
  ·
    refine ⟨17461178027223633889344551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11640785351482422592896367 17461178027223633889344551)
    ·
      refine ⟨26191767040835450834016827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461178027223633889344551 26191767040835450834016827)
      ·
        refine ⟨39287650561253176251025241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26191767040835450834016827 39287650561253176251025241)
        ·
          refine ⟨29465737920939882188268931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39287650561253176251025241 29465737920939882188268931)
          ·
            refine ⟨44198606881409823282403397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29465737920939882188268931 44198606881409823282403397)
            ·
              refine ⟨8287238790264341865450637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44198606881409823282403397 8287238790264341865450637)
              ·
                refine ⟨3107714546349128199543989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8287238790264341865450637 3107714546349128199543989)
                ·
                  refine ⟨291348238720230768707249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3107714546349128199543989 291348238720230768707249)
                  ·
                    rfl

theorem cell22_2553294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_2553294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553294 prefixEnd_2553294 := by exact prefixLift 2553294
  have htrace : WordTrace (prefixWord ++ tailWord_2553294) baseStart_2553294 baseEnd_2553294 := by
    simpa [prefixWord, tailWord_2553294, baseEnd_2553294] using wordTrace_append hprefix tailTrace_2553294
  have hstable : (prefixWord ++ tailWord_2553294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553294).length < 2 ^ (prefixWord ++ tailWord_2553294).sum := by decide
  have hdescent : baseEnd_2553294 < baseStart_2553294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553358 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2553358 : Nat := 118140960795 + 2553358 * 2 ^ 59
def prefixEnd_2553358 : Nat := 4983230072969 + 3 ^ 40 * 2553358 * 2
def baseEnd_2553358 : Nat := 874066624668617472521551

theorem tailTrace_2553358 : CollatzResearch.WordTrace tailWord_2553358 prefixEnd_2553358 874066624668617472521551 := by
  unfold tailWord_2553358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641077135453439959187591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62085744722418346449000485 11641077135453439959187591)
  ·
    refine ⟨17461615703180159938781387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641077135453439959187591 17461615703180159938781387)
    ·
      refine ⟨26192423554770239908172081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461615703180159938781387 26192423554770239908172081)
      ·
        refine ⟨19644317666077679931129061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26192423554770239908172081 19644317666077679931129061)
        ·
          refine ⟨3683309562389564987086699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19644317666077679931129061 3683309562389564987086699)
          ·
            refine ⟨5524964343584347480630049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683309562389564987086699 5524964343584347480630049)
            ·
              refine ⟨4143723257688260610472537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5524964343584347480630049 4143723257688260610472537)
              ·
                refine ⟨3107792443266195457854403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143723257688260610472537 3107792443266195457854403)
                ·
                  refine ⟨4661688664899293186781605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107792443266195457854403 4661688664899293186781605)
                  ·
                    refine ⟨874066624668617472521551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661688664899293186781605 874066624668617472521551)
                    ·
                      rfl

theorem cell22_2553358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2553358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553358 prefixEnd_2553358 := by exact prefixLift 2553358
  have htrace : WordTrace (prefixWord ++ tailWord_2553358) baseStart_2553358 baseEnd_2553358 := by
    simpa [prefixWord, tailWord_2553358, baseEnd_2553358] using wordTrace_append hprefix tailTrace_2553358
  have hstable : (prefixWord ++ tailWord_2553358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553358).length < 2 ^ (prefixWord ++ tailWord_2553358).sum := by decide
  have hdescent : baseEnd_2553358 < baseStart_2553358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553386 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2553386 : Nat := 118140960795 + 2553386 * 2 ^ 59
def prefixEnd_2553386 : Nat := 4983230072969 + 3 ^ 40 * 2553386 * 2
def baseEnd_2553386 : Nat := 874076209640834732821465

theorem tailTrace_2553386 : CollatzResearch.WordTrace tailWord_2553386 prefixEnd_2553386 874076209640834732821465 := by
  unfold tailWord_2553386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23282409581881520113880003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62086425551684053637013341 23282409581881520113880003)
  ·
    refine ⟨34923614372822280170820005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23282409581881520113880003 34923614372822280170820005)
    ·
      refine ⟨6548177694904177532028751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34923614372822280170820005 6548177694904177532028751)
      ·
        refine ⟨9822266542356266298043127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548177694904177532028751 9822266542356266298043127)
        ·
          refine ⟨14733399813534399447064691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9822266542356266298043127 14733399813534399447064691)
          ·
            refine ⟨22100099720301599170597037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14733399813534399447064691 22100099720301599170597037)
            ·
              refine ⟨8287537395113099688973889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22100099720301599170597037 8287537395113099688973889)
              ·
                refine ⟨6215653046334824766730417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8287537395113099688973889 6215653046334824766730417)
                ·
                  refine ⟨4661739784751118575047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215653046334824766730417 4661739784751118575047813)
                  ·
                    refine ⟨874076209640834732821465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661739784751118575047813 874076209640834732821465)
                    ·
                      rfl

theorem cell22_2553386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2553386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553386 prefixEnd_2553386 := by exact prefixLift 2553386
  have htrace : WordTrace (prefixWord ++ tailWord_2553386) baseStart_2553386 baseEnd_2553386 := by
    simpa [prefixWord, tailWord_2553386, baseEnd_2553386] using wordTrace_append hprefix tailTrace_2553386
  have hstable : (prefixWord ++ tailWord_2553386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553386).length < 2 ^ (prefixWord ++ tailWord_2553386).sum := by decide
  have hdescent : baseEnd_2553386 < baseStart_2553386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553390 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_2553390 : Nat := 118140960795 + 2553390 * 2 ^ 59
def prefixEnd_2553390 : Nat := 4983230072969 + 3 ^ 40 * 2553390 * 2
def baseEnd_2553390 : Nat := 291359192974193351907151

theorem tailTrace_2553390 : CollatzResearch.WordTrace tailWord_2553390 prefixEnd_2553390 291359192974193351907151 := by
  unfold tailWord_2553390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641223027438948642333203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62086522813007726092443749 11641223027438948642333203)
  ·
    refine ⟨17461834541158422963499805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641223027438948642333203 17461834541158422963499805)
    ·
      refine ⟨6548187952934408611312427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17461834541158422963499805 6548187952934408611312427)
      ·
        refine ⟨9822281929401612916968641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548187952934408611312427 9822281929401612916968641)
        ·
          refine ⟨7366711447051209687726481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9822281929401612916968641 7366711447051209687726481)
          ·
            refine ⟨5525033585288407265794861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7366711447051209687726481 5525033585288407265794861)
            ·
              refine ⟨2071887594483152724673073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5525033585288407265794861 2071887594483152724673073)
              ·
                refine ⟨1553915695862364543504805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071887594483152724673073 1553915695862364543504805)
                ·
                  refine ⟨291359192974193351907151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553915695862364543504805 291359192974193351907151)
                  ·
                    rfl

theorem cell22_2553390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_2553390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553390 prefixEnd_2553390 := by exact prefixLift 2553390
  have htrace : WordTrace (prefixWord ++ tailWord_2553390) baseStart_2553390 baseEnd_2553390 := by
    simpa [prefixWord, tailWord_2553390, baseEnd_2553390] using wordTrace_append hprefix tailTrace_2553390
  have hstable : (prefixWord ++ tailWord_2553390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553390).length < 2 ^ (prefixWord ++ tailWord_2553390).sum := by decide
  have hdescent : baseEnd_2553390 < baseStart_2553390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553450 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2553450 : Nat := 118140960795 + 2553450 * 2 ^ 59
def prefixEnd_2553450 : Nat := 4983230072969 + 3 ^ 40 * 2553450 * 2
def baseEnd_2553450 : Nat := 874098118148759899221269

theorem tailTrace_2553450 : CollatzResearch.WordTrace tailWord_2553450 prefixEnd_2553450 874098118148759899221269 := by
  unfold tailWord_2553450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23282993149823554846462451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62087981732862812923899869 23282993149823554846462451)
  ·
    refine ⟨34924489724735332269693677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23282993149823554846462451 34924489724735332269693677)
    ·
      refine ⟨13096683646775749601135129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34924489724735332269693677 13096683646775749601135129)
      ·
        refine ⟨9822512735081812200851347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13096683646775749601135129 9822512735081812200851347)
        ·
          refine ⟨14733769102622718301277021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9822512735081812200851347 14733769102622718301277021)
          ·
            refine ⟨5525163413483519362978883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14733769102622718301277021 5525163413483519362978883)
            ·
              refine ⟨8287745120225279044468325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525163413483519362978883 8287745120225279044468325)
              ·
                refine ⟨1553952210042239820837811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8287745120225279044468325 1553952210042239820837811)
                ·
                  refine ⟨2330928315063359731256717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553952210042239820837811 2330928315063359731256717)
                  ·
                    refine ⟨874098118148759899221269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2330928315063359731256717 874098118148759899221269)
                    ·
                      rfl

theorem cell22_2553450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2553450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553450 prefixEnd_2553450 := by exact prefixLift 2553450
  have htrace : WordTrace (prefixWord ++ tailWord_2553450) baseStart_2553450 baseEnd_2553450 := by
    simpa [prefixWord, tailWord_2553450, baseEnd_2553450] using wordTrace_append hprefix tailTrace_2553450
  have hstable : (prefixWord ++ tailWord_2553450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553450).length < 2 ^ (prefixWord ++ tailWord_2553450).sum := by decide
  have hdescent : baseEnd_2553450 < baseStart_2553450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553461 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2553461 : Nat := 118140960795 + 2553461 * 2 ^ 59
def prefixEnd_2553461 : Nat := 4983230072969 + 3 ^ 40 * 2553461 * 2
def baseEnd_2553461 : Nat := 874101883673559537196235

theorem tailTrace_2553461 : CollatzResearch.WordTrace tailWord_2553461 prefixEnd_2553461 874101883673559537196235 := by
  unfold tailWord_2553461
  simp only [CollatzResearch.WordTrace]
  refine ⟨93132373802254368264500237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62088249201502912176333491 93132373802254368264500237)
  ·
    refine ⟨34924640175845388099187589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93132373802254368264500237 34924640175845388099187589)
    ·
      refine ⟨6548370032971010268597673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34924640175845388099187589 6548370032971010268597673)
      ·
        refine ⟨4911277524728257701448255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548370032971010268597673 4911277524728257701448255)
        ·
          refine ⟨7366916287092386552172383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911277524728257701448255 7366916287092386552172383)
          ·
            refine ⟨11050374430638579828258575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366916287092386552172383 11050374430638579828258575)
            ·
              refine ⟨16575561645957869742387863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11050374430638579828258575 16575561645957869742387863)
              ·
                refine ⟨24863342468936804613581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16575561645957869742387863 24863342468936804613581795)
                ·
                  refine ⟨37295013703405206920372693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24863342468936804613581795 37295013703405206920372693)
                  ·
                    refine ⟨874101883673559537196235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37295013703405206920372693 874101883673559537196235)
                    ·
                      rfl

theorem cell22_2553461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2553461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553461 prefixEnd_2553461 := by exact prefixLift 2553461
  have htrace : WordTrace (prefixWord ++ tailWord_2553461) baseStart_2553461 baseEnd_2553461 := by
    simpa [prefixWord, tailWord_2553461, baseEnd_2553461] using wordTrace_append hprefix tailTrace_2553461
  have hstable : (prefixWord ++ tailWord_2553461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553461).length < 2 ^ (prefixWord ++ tailWord_2553461).sum := by decide
  have hdescent : baseEnd_2553461 < baseStart_2553461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553489 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2553489 : Nat := 118140960795 + 2553489 * 2 ^ 59
def prefixEnd_2553489 : Nat := 4983230072969 + 3 ^ 40 * 2553489 * 2
def baseEnd_2553489 : Nat := 874111468645776797496149

theorem tailTrace_2553489 : CollatzResearch.WordTrace tailWord_2553489 prefixEnd_2553489 874111468645776797496149 := by
  unfold tailWord_2553489
  simp only [CollatzResearch.WordTrace]
  refine ⟨93133395046152929046519521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62088930030768619364346347 93133395046152929046519521)
  ·
    refine ⟨69850046284614696784889641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93133395046152929046519521 69850046284614696784889641)
    ·
      refine ⟨52387534713461022588667231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69850046284614696784889641 52387534713461022588667231)
      ·
        refine ⟨78581302070191533883000847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52387534713461022588667231 78581302070191533883000847)
        ·
          refine ⟨117871953105287300824501271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78581302070191533883000847 117871953105287300824501271)
          ·
            refine ⟨176807929657930951236751907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117871953105287300824501271 176807929657930951236751907)
            ·
              refine ⟨265211894486896426855127861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176807929657930951236751907 265211894486896426855127861)
              ·
                refine ⟨24863615108146540017668237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265211894486896426855127861 24863615108146540017668237)
                ·
                  refine ⟨9323855665554952506625589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24863615108146540017668237 9323855665554952506625589)
                  ·
                    refine ⟨874111468645776797496149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9323855665554952506625589 874111468645776797496149)
                    ·
                      rfl

theorem cell22_2553489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2553489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553489 prefixEnd_2553489 := by exact prefixLift 2553489
  have htrace : WordTrace (prefixWord ++ tailWord_2553489) baseStart_2553489 baseEnd_2553489 := by
    simpa [prefixWord, tailWord_2553489, baseEnd_2553489] using wordTrace_append hprefix tailTrace_2553489
  have hstable : (prefixWord ++ tailWord_2553489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553489).length < 2 ^ (prefixWord ++ tailWord_2553489).sum := by decide
  have hdescent : baseEnd_2553489 < baseStart_2553489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553508 : List Nat := [2, 3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_2553508 : Nat := 118140960795 + 2553508 * 2 ^ 59
def prefixEnd_2553508 : Nat := 4983230072969 + 3 ^ 40 * 2553508 * 2
def baseEnd_2553508 : Nat := 291372657578022360423697

theorem tailTrace_2553508 : CollatzResearch.WordTrace tailWord_2553508 prefixEnd_2553508 291372657578022360423697 := by
  unfold tailWord_2553508
  simp only [CollatzResearch.WordTrace]
  refine ⟨46567044016542047645730589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62089392022056063527640785 46567044016542047645730589)
  ·
    refine ⟨17462641506203267867148971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46567044016542047645730589 17462641506203267867148971)
    ·
      refine ⟨26193962259304901800723457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17462641506203267867148971 26193962259304901800723457)
      ·
        refine ⟨19645471694478676350542593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26193962259304901800723457 19645471694478676350542593)
        ·
          refine ⟨14734103770859007262906945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19645471694478676350542593 14734103770859007262906945)
          ·
            refine ⟨11050577828144255447180209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14734103770859007262906945 11050577828144255447180209)
            ·
              refine ⟨8287933371108191585385157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11050577828144255447180209 8287933371108191585385157)
              ·
                refine ⟨1553987507082785922259717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8287933371108191585385157 1553987507082785922259717)
                ·
                  refine ⟨291372657578022360423697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553987507082785922259717 291372657578022360423697)
                  ·
                    rfl

theorem cell22_2553508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_2553508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553508 prefixEnd_2553508 := by exact prefixLift 2553508
  have htrace : WordTrace (prefixWord ++ tailWord_2553508) baseStart_2553508 baseEnd_2553508 := by
    simpa [prefixWord, tailWord_2553508, baseEnd_2553508] using wordTrace_append hprefix tailTrace_2553508
  have hstable : (prefixWord ++ tailWord_2553508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553508).length < 2 ^ (prefixWord ++ tailWord_2553508).sum := by decide
  have hdescent : baseEnd_2553508 < baseStart_2553508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553519 : List Nat := [1, 1, 2, 1, 2, 4, 2, 9]
def baseStart_2553519 : Nat := 118140960795 + 2553519 * 2 ^ 59
def prefixEnd_2553519 : Nat := 4983230072969 + 3 ^ 40 * 2553519 * 2
def baseEnd_2553519 : Nat := 97124637584318524360673

theorem tailTrace_2553519 : CollatzResearch.WordTrace tailWord_2553519 prefixEnd_2553519 97124637584318524360673 := by
  unfold tailWord_2553519
  simp only [CollatzResearch.WordTrace]
  refine ⟨93134489236044244170111611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62089659490696162780074407 93134489236044244170111611)
  ·
    refine ⟨139701733854066366255167417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93134489236044244170111611 139701733854066366255167417)
    ·
      refine ⟨104776300390549774691375563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139701733854066366255167417 104776300390549774691375563)
      ·
        refine ⟨157164450585824662037063345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104776300390549774691375563 157164450585824662037063345)
        ·
          refine ⟨117873337939368496527797509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157164450585824662037063345 117873337939368496527797509)
          ·
            refine ⟨22101250863631593098962033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117873337939368496527797509 22101250863631593098962033)
            ·
              refine ⟨16575938147723694824221525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22101250863631593098962033 16575938147723694824221525)
              ·
                refine ⟨97124637584318524360673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16575938147723694824221525 97124637584318524360673)
                ·
                  rfl

theorem cell22_2553519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 9].length) (baseStart_2553519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553519 prefixEnd_2553519 := by exact prefixLift 2553519
  have htrace : WordTrace (prefixWord ++ tailWord_2553519) baseStart_2553519 baseEnd_2553519 := by
    simpa [prefixWord, tailWord_2553519, baseEnd_2553519] using wordTrace_append hprefix tailTrace_2553519
  have hstable : (prefixWord ++ tailWord_2553519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553519).length < 2 ^ (prefixWord ++ tailWord_2553519).sum := by decide
  have hdescent : baseEnd_2553519 < baseStart_2553519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553551 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 5, 3]
def baseStart_2553551 : Nat := 118140960795 + 2553551 * 2 ^ 59
def prefixEnd_2553551 : Nat := 4983230072969 + 3 ^ 40 * 2553551 * 2
def baseEnd_2553551 : Nat := 874132692512829302445959

theorem tailTrace_2553551 : CollatzResearch.WordTrace tailWord_2553551 prefixEnd_2553551 874132692512829302445959 := by
  unfold tailWord_2553551
  simp only [CollatzResearch.WordTrace]
  refine ⟨93135656371928313635276507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62090437581285542423517671 93135656371928313635276507)
  ·
    refine ⟨139703484557892470452914761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93135656371928313635276507 139703484557892470452914761)
    ·
      refine ⟨104777613418419352839686071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139703484557892470452914761 104777613418419352839686071)
      ·
        refine ⟨157166420127629029259529107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104777613418419352839686071 157166420127629029259529107)
        ·
          refine ⟨235749630191443543889293661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157166420127629029259529107 235749630191443543889293661)
          ·
            refine ⟨88406111321791328958485123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235749630191443543889293661 88406111321791328958485123)
            ·
              refine ⟨132609166982686993437727685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88406111321791328958485123 132609166982686993437727685)
              ·
                refine ⟨24864218809253811269573941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132609166982686993437727685 24864218809253811269573941)
                ·
                  refine ⟨2331020513367544806522557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24864218809253811269573941 2331020513367544806522557)
                  ·
                    refine ⟨874132692512829302445959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331020513367544806522557 874132692512829302445959)
                    ·
                      rfl

theorem cell22_2553551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_2553551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553551 prefixEnd_2553551 := by exact prefixLift 2553551
  have htrace : WordTrace (prefixWord ++ tailWord_2553551) baseStart_2553551 baseEnd_2553551 := by
    simpa [prefixWord, tailWord_2553551, baseEnd_2553551] using wordTrace_append hprefix tailTrace_2553551
  have hstable : (prefixWord ++ tailWord_2553551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553551).length < 2 ^ (prefixWord ++ tailWord_2553551).sum := by decide
  have hdescent : baseEnd_2553551 < baseStart_2553551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553568 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_2553568 : Nat := 118140960795 + 2553568 * 2 ^ 59
def prefixEnd_2553568 : Nat := 4983230072969 + 3 ^ 40 * 2553568 * 2
def baseEnd_2553568 : Nat := 874138511960246924770907

theorem tailTrace_2553568 : CollatzResearch.WordTrace tailWord_2553568 prefixEnd_2553568 874138511960246924770907 := by
  unfold tailWord_2553568
  simp only [CollatzResearch.WordTrace]
  refine ⟨46568138206433362769322679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62090850941911150359096905 46568138206433362769322679)
  ·
    refine ⟨69852207309650044153984019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46568138206433362769322679 69852207309650044153984019)
    ·
      refine ⟨104778310964475066230976029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69852207309650044153984019 104778310964475066230976029)
      ·
        refine ⟨39291866611678149836616011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104778310964475066230976029 39291866611678149836616011)
        ·
          refine ⟨58937799917517224754924017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39291866611678149836616011 58937799917517224754924017)
          ·
            refine ⟨44203349938137918566193013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58937799917517224754924017 44203349938137918566193013)
            ·
              refine ⟨4144064056700429865580595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44203349938137918566193013 4144064056700429865580595)
              ·
                refine ⟨6216096085050644798370893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144064056700429865580595 6216096085050644798370893)
                ·
                  refine ⟨2331036031893991799389085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6216096085050644798370893 2331036031893991799389085)
                  ·
                    refine ⟨874138511960246924770907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331036031893991799389085 874138511960246924770907)
                    ·
                      rfl

theorem cell22_2553568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_2553568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553568 prefixEnd_2553568 := by exact prefixLift 2553568
  have htrace : WordTrace (prefixWord ++ tailWord_2553568) baseStart_2553568 baseEnd_2553568 := by
    simpa [prefixWord, tailWord_2553568, baseEnd_2553568] using wordTrace_append hprefix tailTrace_2553568
  have hstable : (prefixWord ++ tailWord_2553568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553568).length < 2 ^ (prefixWord ++ tailWord_2553568).sum := by decide
  have hdescent : baseEnd_2553568 < baseStart_2553568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553602 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2553602 : Nat := 118140960795 + 2553602 * 2 ^ 59
def prefixEnd_2553602 : Nat := 4983230072969 + 3 ^ 40 * 2553602 * 2
def baseEnd_2553602 : Nat := 874150150855082169420803

theorem tailTrace_2553602 : CollatzResearch.WordTrace tailWord_2553602 prefixEnd_2553602 874150150855082169420803 := by
  unfold tailWord_2553602
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284379123685887336345765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62091677663162366230255373 23284379123685887336345765)
  ·
    refine ⟨4365821085691103875564831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23284379123685887336345765 4365821085691103875564831)
    ·
      refine ⟨6548731628536655813347247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4365821085691103875564831 6548731628536655813347247)
      ·
        refine ⟨9823097442804983720020871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548731628536655813347247 9823097442804983720020871)
        ·
          refine ⟨14734646164207475580031307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9823097442804983720020871 14734646164207475580031307)
          ·
            refine ⟨22101969246311213370046961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14734646164207475580031307 22101969246311213370046961)
            ·
              refine ⟨16576476934733410027535221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22101969246311213370046961 16576476934733410027535221)
              ·
                refine ⟨1554044712631257190081427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16576476934733410027535221 1554044712631257190081427)
                ·
                  refine ⟨2331067068946885785122141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554044712631257190081427 2331067068946885785122141)
                  ·
                    refine ⟨874150150855082169420803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331067068946885785122141 874150150855082169420803)
                    ·
                      rfl

theorem cell22_2553602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2553602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553602 prefixEnd_2553602 := by exact prefixLift 2553602
  have htrace : WordTrace (prefixWord ++ tailWord_2553602) baseStart_2553602 baseEnd_2553602 := by
    simpa [prefixWord, tailWord_2553602, baseEnd_2553602] using wordTrace_append hprefix tailTrace_2553602
  have hstable : (prefixWord ++ tailWord_2553602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553602).length < 2 ^ (prefixWord ++ tailWord_2553602).sum := by decide
  have hdescent : baseEnd_2553602 < baseStart_2553602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553658 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_2553658 : Nat := 118140960795 + 2553658 * 2 ^ 59
def prefixEnd_2553658 : Nat := 4983230072969 + 3 ^ 40 * 2553658 * 2
def baseEnd_2553658 : Nat := 874169320799516690020631

theorem tailTrace_2553658 : CollatzResearch.WordTrace tailWord_2553658 prefixEnd_2553658 874169320799516690020631 := by
  unfold tailWord_2553658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284889745635167727355407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62093039321693780606281085 23284889745635167727355407)
  ·
    refine ⟨34927334618452751591033111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23284889745635167727355407 34927334618452751591033111)
    ·
      refine ⟨52391001927679127386549667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34927334618452751591033111 52391001927679127386549667)
      ·
        refine ⟨78586502891518691079824501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52391001927679127386549667 78586502891518691079824501)
        ·
          refine ⟨7367484646079877288733547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78586502891518691079824501 7367484646079877288733547)
          ·
            refine ⟨11051226969119815933100321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367484646079877288733547 11051226969119815933100321)
            ·
              refine ⟨8288420226839861949825241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11051226969119815933100321 8288420226839861949825241)
              ·
                refine ⟨6216315170129896462368931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288420226839861949825241 6216315170129896462368931)
                ·
                  refine ⟨9324472755194844693553397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216315170129896462368931 9324472755194844693553397)
                  ·
                    refine ⟨874169320799516690020631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9324472755194844693553397 874169320799516690020631)
                    ·
                      rfl

theorem cell22_2553658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_2553658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553658 prefixEnd_2553658 := by exact prefixLift 2553658
  have htrace : WordTrace (prefixWord ++ tailWord_2553658) baseStart_2553658 baseEnd_2553658 := by
    simpa [prefixWord, tailWord_2553658, baseEnd_2553658] using wordTrace_append hprefix tailTrace_2553658
  have hstable : (prefixWord ++ tailWord_2553658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553658).length < 2 ^ (prefixWord ++ tailWord_2553658).sum := by decide
  have hdescent : baseEnd_2553658 < baseStart_2553658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553662 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2553662 : Nat := 118140960795 + 2553662 * 2 ^ 59
def prefixEnd_2553662 : Nat := 4983230072969 + 3 ^ 40 * 2553662 * 2
def baseEnd_2553662 : Nat := 874170690081262012920619

theorem tailTrace_2553662 : CollatzResearch.WordTrace tailWord_2553662 prefixEnd_2553662 874170690081262012920619 := by
  unfold tailWord_2553662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642463109315772449070905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62093136583017453061711493 11642463109315772449070905)
  ·
    refine ⟨8731847331986829336803179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11642463109315772449070905 8731847331986829336803179)
    ·
      refine ⟨13097770997980244005204769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8731847331986829336803179 13097770997980244005204769)
      ·
        refine ⟨9823328248485183003903577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13097770997980244005204769 9823328248485183003903577)
        ·
          refine ⟨7367496186363887252927683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9823328248485183003903577 7367496186363887252927683)
          ·
            refine ⟨11051244279545830879391525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367496186363887252927683 11051244279545830879391525)
            ·
              refine ⟨2072108302414843289885911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11051244279545830879391525 2072108302414843289885911)
              ·
                refine ⟨3108162453622264934828867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072108302414843289885911 3108162453622264934828867)
                ·
                  refine ⟨4662243680433397402243301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108162453622264934828867 4662243680433397402243301)
                  ·
                    refine ⟨874170690081262012920619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662243680433397402243301 874170690081262012920619)
                    ·
                      rfl

theorem cell22_2553662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2553662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553662 prefixEnd_2553662 := by exact prefixLift 2553662
  have htrace : WordTrace (prefixWord ++ tailWord_2553662) baseStart_2553662 baseEnd_2553662 := by
    simpa [prefixWord, tailWord_2553662, baseEnd_2553662] using wordTrace_append hprefix tailTrace_2553662
  have hstable : (prefixWord ++ tailWord_2553662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553662).length < 2 ^ (prefixWord ++ tailWord_2553662).sum := by decide
  have hdescent : baseEnd_2553662 < baseStart_2553662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553677 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2553677 : Nat := 118140960795 + 2553677 * 2 ^ 59
def prefixEnd_2553677 : Nat := 4983230072969 + 3 ^ 40 * 2553677 * 2
def baseEnd_2553677 : Nat := 291391941629268991265191

theorem tailTrace_2553677 : CollatzResearch.WordTrace tailWord_2553677 prefixEnd_2553677 291391941629268991265191 := by
  unfold tailWord_2553677
  simp only [CollatzResearch.WordTrace]
  refine ⟨93140251969471837154363285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62093501312981224769575523 93140251969471837154363285)
  ·
    refine ⟨4365949311068992366610779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93140251969471837154363285 4365949311068992366610779)
    ·
      refine ⟨6548923966603488549916169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4365949311068992366610779 6548923966603488549916169)
      ·
        refine ⟨4911692974952616412437127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548923966603488549916169 4911692974952616412437127)
        ·
          refine ⟨7367539462428924618655691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911692974952616412437127 7367539462428924618655691)
          ·
            refine ⟨11051309193643386927983537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367539462428924618655691 11051309193643386927983537)
            ·
              refine ⟨8288481895232540195987653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11051309193643386927983537 8288481895232540195987653)
              ·
                refine ⟨1554090355356101286747685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8288481895232540195987653 1554090355356101286747685)
                ·
                  refine ⟨291391941629268991265191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554090355356101286747685 291391941629268991265191)
                  ·
                    rfl

theorem cell22_2553677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2553677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553677 prefixEnd_2553677 := by exact prefixLift 2553677
  have htrace : WordTrace (prefixWord ++ tailWord_2553677) baseStart_2553677 baseEnd_2553677 := by
    simpa [prefixWord, tailWord_2553677, baseEnd_2553677] using wordTrace_append hprefix tailTrace_2553677
  have hstable : (prefixWord ++ tailWord_2553677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553677).length < 2 ^ (prefixWord ++ tailWord_2553677).sum := by decide
  have hdescent : baseEnd_2553677 < baseStart_2553677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553692 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2553692 : Nat := 118140960795 + 2553692 * 2 ^ 59
def prefixEnd_2553692 : Nat := 4983230072969 + 3 ^ 40 * 2553692 * 2
def baseEnd_2553692 : Nat := 874180959694351934670527

theorem tailTrace_2553692 : CollatzResearch.WordTrace tailWord_2553692 prefixEnd_2553692 874180959694351934670527 := by
  unfold tailWord_2553692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46570399532208747358079665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62093866042944996477439553 46570399532208747358079665)
  ·
    refine ⟨34927799649156560518559749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46570399532208747358079665 34927799649156560518559749)
    ·
      refine ⟨6548962434216855097229953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34927799649156560518559749 6548962434216855097229953)
      ·
        refine ⟨4911721825662641322922465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548962434216855097229953 4911721825662641322922465)
        ·
          refine ⟨3683791369246980992191849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4911721825662641322922465 3683791369246980992191849)
          ·
            refine ⟨2762843526935235744143887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683791369246980992191849 2762843526935235744143887)
            ·
              refine ⟨4144265290402853616215831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762843526935235744143887 4144265290402853616215831)
              ·
                refine ⟨6216397935604280424323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144265290402853616215831 6216397935604280424323747)
                ·
                  refine ⟨9324596903406420636485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216397935604280424323747 9324596903406420636485621)
                  ·
                    refine ⟨874180959694351934670527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9324596903406420636485621 874180959694351934670527)
                    ·
                      rfl

theorem cell22_2553692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2553692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553692 prefixEnd_2553692 := by exact prefixLift 2553692
  have htrace : WordTrace (prefixWord ++ tailWord_2553692) baseStart_2553692 baseEnd_2553692 := by
    simpa [prefixWord, tailWord_2553692, baseEnd_2553692] using wordTrace_append hprefix tailTrace_2553692
  have hstable : (prefixWord ++ tailWord_2553692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553692).length < 2 ^ (prefixWord ++ tailWord_2553692).sum := by decide
  have hdescent : baseEnd_2553692 < baseStart_2553692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553733 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 5]
def baseStart_2553733 : Nat := 118140960795 + 2553733 * 2 ^ 59
def prefixEnd_2553733 : Nat := 4983230072969 + 3 ^ 40 * 2553733 * 2
def baseEnd_2553733 : Nat := 291398331610747164798467

theorem tailTrace_2553733 : CollatzResearch.WordTrace tailWord_2553733 prefixEnd_2553733 291398331610747164798467 := by
  unfold tailWord_2553733
  simp only [CollatzResearch.WordTrace]
  refine ⟨93142294457268958718401853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62094862971512639145601235 93142294457268958718401853)
  ·
    refine ⟨34928360421475859519400695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93142294457268958718401853 34928360421475859519400695)
    ·
      refine ⟨52392540632213789279101043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34928360421475859519400695 52392540632213789279101043)
      ·
        refine ⟨78588810948320683918651565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52392540632213789279101043 78588810948320683918651565)
        ·
          refine ⟨29470804105620256469494337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78588810948320683918651565 29470804105620256469494337)
          ·
            refine ⟨22103103079215192352120753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29470804105620256469494337 22103103079215192352120753)
            ·
              refine ⟨16577327309411394264090565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22103103079215192352120753 16577327309411394264090565)
              ·
                refine ⟨3108248870514636424516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16577327309411394264090565 3108248870514636424516981)
                ·
                  refine ⟨291398331610747164798467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108248870514636424516981 291398331610747164798467)
                  ·
                    rfl

theorem cell22_2553733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_2553733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553733 prefixEnd_2553733 := by exact prefixLift 2553733
  have htrace : WordTrace (prefixWord ++ tailWord_2553733) baseStart_2553733 baseEnd_2553733 := by
    simpa [prefixWord, tailWord_2553733, baseEnd_2553733] using wordTrace_append hprefix tailTrace_2553733
  have hstable : (prefixWord ++ tailWord_2553733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553733).length < 2 ^ (prefixWord ++ tailWord_2553733).sum := by decide
  have hdescent : baseEnd_2553733 < baseStart_2553733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553788 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_2553788 : Nat := 118140960795 + 2553788 * 2 ^ 59
def prefixEnd_2553788 : Nat := 4983230072969 + 3 ^ 40 * 2553788 * 2
def baseEnd_2553788 : Nat := 874213822456239684270233

theorem tailTrace_2553788 : CollatzResearch.WordTrace tailWord_2553788 prefixEnd_2553788 874213822456239684270233 := by
  unfold tailWord_2553788
  simp only [CollatzResearch.WordTrace]
  refine ⟨46572150236034851555827009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62096200314713135407769345 46572150236034851555827009)
  ·
    refine ⟨34929112677026138666870257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46572150236034851555827009 34929112677026138666870257)
    ·
      refine ⟨26196834507769604000152693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34929112677026138666870257 26196834507769604000152693)
      ·
        refine ⟨2455953235103400375014315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26196834507769604000152693 2455953235103400375014315)
        ·
          refine ⟨3683929852655100562521473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455953235103400375014315 3683929852655100562521473)
          ·
            refine ⟨2762947389491325421891105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683929852655100562521473 2762947389491325421891105)
            ·
              refine ⟨2072210542118494066418329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762947389491325421891105 2072210542118494066418329)
              ·
                refine ⟨1554157906588870549813747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072210542118494066418329 1554157906588870549813747)
                ·
                  refine ⟨2331236859883305824720621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554157906588870549813747 2331236859883305824720621)
                  ·
                    refine ⟨874213822456239684270233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331236859883305824720621 874213822456239684270233)
                    ·
                      rfl

theorem cell22_2553788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_2553788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553788 prefixEnd_2553788 := by exact prefixLift 2553788
  have htrace : WordTrace (prefixWord ++ tailWord_2553788) baseStart_2553788 baseEnd_2553788 := by
    simpa [prefixWord, tailWord_2553788, baseEnd_2553788] using wordTrace_append hprefix tailTrace_2553788
  have hstable : (prefixWord ++ tailWord_2553788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553788).length < 2 ^ (prefixWord ++ tailWord_2553788).sum := by decide
  have hdescent : baseEnd_2553788 < baseStart_2553788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553808 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_2553808 : Nat := 118140960795 + 2553808 * 2 ^ 59
def prefixEnd_2553808 : Nat := 4983230072969 + 3 ^ 40 * 2553808 * 2
def baseEnd_2553808 : Nat := 874220668864966298770171

theorem tailTrace_2553808 : CollatzResearch.WordTrace tailWord_2553808 prefixEnd_2553808 874220668864966298770171 := by
  unfold tailWord_2553808
  simp only [CollatzResearch.WordTrace]
  refine ⟨46572514965998623263691039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62096686621331497684921385 46572514965998623263691039)
  ·
    refine ⟨69858772448997934895536559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46572514965998623263691039 69858772448997934895536559)
    ·
      refine ⟨104788158673496902343304839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69858772448997934895536559 104788158673496902343304839)
      ·
        refine ⟨157182238010245353514957259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104788158673496902343304839 157182238010245353514957259)
        ·
          refine ⟨235773357015368030272435889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157182238010245353514957259 235773357015368030272435889)
          ·
            refine ⟨176830017761526022704326917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235773357015368030272435889 176830017761526022704326917)
            ·
              refine ⟨33155628330286129257061297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176830017761526022704326917 33155628330286129257061297)
              ·
                refine ⟨24866721247714596942795973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33155628330286129257061297 24866721247714596942795973)
                ·
                  refine ⟨4662510233946486926774245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24866721247714596942795973 4662510233946486926774245)
                  ·
                    refine ⟨874220668864966298770171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662510233946486926774245 874220668864966298770171)
                    ·
                      rfl

theorem cell22_2553808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_2553808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553808 prefixEnd_2553808 := by exact prefixLift 2553808
  have htrace : WordTrace (prefixWord ++ tailWord_2553808) baseStart_2553808 baseEnd_2553808 := by
    simpa [prefixWord, tailWord_2553808, baseEnd_2553808] using wordTrace_append hprefix tailTrace_2553808
  have hstable : (prefixWord ++ tailWord_2553808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553808).length < 2 ^ (prefixWord ++ tailWord_2553808).sum := by decide
  have hdescent : baseEnd_2553808 < baseStart_2553808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553825 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2553825 : Nat := 118140960795 + 2553825 * 2 ^ 59
def prefixEnd_2553825 : Nat := 4983230072969 + 3 ^ 40 * 2553825 * 2
def baseEnd_2553825 : Nat := 874226488312383921095119

theorem tailTrace_2553825 : CollatzResearch.WordTrace tailWord_2553825 prefixEnd_2553825 874226488312383921095119 := by
  unfold tailWord_2553825
  simp only [CollatzResearch.WordTrace]
  refine ⟨93145649972935658430750929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62097099981957105620500619 93145649972935658430750929)
  ·
    refine ⟨69859237479701743823063197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93145649972935658430750929 69859237479701743823063197)
    ·
      refine ⟨26197214054888153933648699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69859237479701743823063197 26197214054888153933648699)
      ·
        refine ⟨39295821082332230900473049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26197214054888153933648699 39295821082332230900473049)
        ·
          refine ⟨29471865811749173175354787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39295821082332230900473049 29471865811749173175354787)
          ·
            refine ⟨44207798717623759763032181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29471865811749173175354787 44207798717623759763032181)
            ·
              refine ⟨4144481129777227477784267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44207798717623759763032181 4144481129777227477784267)
              ·
                refine ⟨6216721694665841216676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144481129777227477784267 6216721694665841216676401)
                ·
                  refine ⟨4662541270999380912507301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6216721694665841216676401 4662541270999380912507301)
                  ·
                    refine ⟨874226488312383921095119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662541270999380912507301 874226488312383921095119)
                    ·
                      rfl

theorem cell22_2553825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2553825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553825 prefixEnd_2553825 := by exact prefixLift 2553825
  have htrace : WordTrace (prefixWord ++ tailWord_2553825) baseStart_2553825 baseEnd_2553825 := by
    simpa [prefixWord, tailWord_2553825, baseEnd_2553825] using wordTrace_append hprefix tailTrace_2553825
  have hstable : (prefixWord ++ tailWord_2553825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553825).length < 2 ^ (prefixWord ++ tailWord_2553825).sum := by decide
  have hdescent : baseEnd_2553825 < baseStart_2553825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553831 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2553831 : Nat := 118140960795 + 2553831 * 2 ^ 59
def prefixEnd_2553831 : Nat := 4983230072969 + 3 ^ 40 * 2553831 * 2
def baseEnd_2553831 : Nat := 874228542235001905445101

theorem tailTrace_2553831 : CollatzResearch.WordTrace tailWord_2553831 prefixEnd_2553831 874228542235001905445101 := by
  unfold tailWord_2553831
  simp only [CollatzResearch.WordTrace]
  refine ⟨93145868810913921455469347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62097245873942614303646231 93145868810913921455469347)
  ·
    refine ⟨139718803216370882183204021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93145868810913921455469347 139718803216370882183204021)
    ·
      refine ⟨13098637801534770204675377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139718803216370882183204021 13098637801534770204675377)
      ·
        refine ⟨9823978351151077653506533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13098637801534770204675377 9823978351151077653506533)
        ·
          refine ⟨1841995940840827060032475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9823978351151077653506533 1841995940840827060032475)
          ·
            refine ⟨2762993911261240590048713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841995940840827060032475 2762993911261240590048713)
            ·
              refine ⟨2072245433445930442536535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762993911261240590048713 2072245433445930442536535)
              ·
                refine ⟨3108368150168895663804803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072245433445930442536535 3108368150168895663804803)
                ·
                  refine ⟨4662552225253343495707205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108368150168895663804803 4662552225253343495707205)
                  ·
                    refine ⟨874228542235001905445101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662552225253343495707205 874228542235001905445101)
                    ·
                      rfl

theorem cell22_2553831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2553831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553831 prefixEnd_2553831 := by exact prefixLift 2553831
  have htrace : WordTrace (prefixWord ++ tailWord_2553831) baseStart_2553831 baseEnd_2553831 := by
    simpa [prefixWord, tailWord_2553831, baseEnd_2553831] using wordTrace_append hprefix tailTrace_2553831
  have hstable : (prefixWord ++ tailWord_2553831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553831).length < 2 ^ (prefixWord ++ tailWord_2553831).sum := by decide
  have hdescent : baseEnd_2553831 < baseStart_2553831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553853 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2553853 : Nat := 118140960795 + 2553853 * 2 ^ 59
def prefixEnd_2553853 : Nat := 4983230072969 + 3 ^ 40 * 2553853 * 2
def baseEnd_2553853 : Nat := 874236073284601181395033

theorem tailTrace_2553853 : CollatzResearch.WordTrace tailWord_2553853 prefixEnd_2553853 874236073284601181395033 := by
  unfold tailWord_2553853
  simp only [CollatzResearch.WordTrace]
  refine ⟨93146671216834219212770213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62097780811222812808513475 93146671216834219212770213)
  ·
    refine ⟨17465000853156416102394415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93146671216834219212770213 17465000853156416102394415)
    ·
      refine ⟨26197501279734624153591623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17465000853156416102394415 26197501279734624153591623)
      ·
        refine ⟨39296251919601936230387435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26197501279734624153591623 39296251919601936230387435)
        ·
          refine ⟨58944377879402904345581153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39296251919601936230387435 58944377879402904345581153)
          ·
            refine ⟨44208283409552178259185865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58944377879402904345581153 44208283409552178259185865)
            ·
              refine ⟨33156212557164133694389399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44208283409552178259185865 33156212557164133694389399)
              ·
                refine ⟨49734318835746200541584099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33156212557164133694389399 49734318835746200541584099)
                ·
                  refine ⟨74601478253619300812376149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49734318835746200541584099 74601478253619300812376149)
                  ·
                    refine ⟨874236073284601181395033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74601478253619300812376149 874236073284601181395033)
                    ·
                      rfl

theorem cell22_2553853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2553853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553853 prefixEnd_2553853 := by exact prefixLift 2553853
  have htrace : WordTrace (prefixWord ++ tailWord_2553853) baseStart_2553853 baseEnd_2553853 := by
    simpa [prefixWord, tailWord_2553853, baseEnd_2553853] using wordTrace_append hprefix tailTrace_2553853
  have hstable : (prefixWord ++ tailWord_2553853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553853).length < 2 ^ (prefixWord ++ tailWord_2553853).sum := by decide
  have hdescent : baseEnd_2553853 < baseStart_2553853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553883 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_2553883 : Nat := 118140960795 + 2553883 * 2 ^ 59
def prefixEnd_2553883 : Nat := 4983230072969 + 3 ^ 40 * 2553883 * 2
def baseEnd_2553883 : Nat := 874246342897691103144941

theorem tailTrace_2553883 : CollatzResearch.WordTrace tailWord_2553883 prefixEnd_2553883 874246342897691103144941 := by
  unfold tailWord_2553883
  simp only [CollatzResearch.WordTrace]
  refine ⟨93147765406725534336362303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62098510271150356224241535 93147765406725534336362303)
  ·
    refine ⟨139721648110088301504543455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93147765406725534336362303 139721648110088301504543455)
    ·
      refine ⟨209582472165132452256815183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139721648110088301504543455 209582472165132452256815183)
      ·
        refine ⟨314373708247698678385222775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209582472165132452256815183 314373708247698678385222775)
        ·
          refine ⟨471560562371548017577834163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314373708247698678385222775 471560562371548017577834163)
          ·
            refine ⟨707340843557322026366751245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471560562371548017577834163 707340843557322026366751245)
            ·
              refine ⟨265252816333995759887531717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 707340843557322026366751245 265252816333995759887531717)
              ·
                refine ⟨49734903062624204978912197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265252816333995759887531717 49734903062624204978912197)
                ·
                  refine ⟨9325294324242038433546037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49734903062624204978912197 9325294324242038433546037)
                  ·
                    refine ⟨874246342897691103144941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9325294324242038433546037 874246342897691103144941)
                    ·
                      rfl

theorem cell22_2553883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_2553883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553883 prefixEnd_2553883 := by exact prefixLift 2553883
  have htrace : WordTrace (prefixWord ++ tailWord_2553883) baseStart_2553883 baseEnd_2553883 := by
    simpa [prefixWord, tailWord_2553883, baseEnd_2553883] using wordTrace_append hprefix tailTrace_2553883
  have hstable : (prefixWord ++ tailWord_2553883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553883).length < 2 ^ (prefixWord ++ tailWord_2553883).sum := by decide
  have hdescent : baseEnd_2553883 < baseStart_2553883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553885 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2553885 : Nat := 118140960795 + 2553885 * 2 ^ 59
def prefixEnd_2553885 : Nat := 4983230072969 + 3 ^ 40 * 2553885 * 2
def baseEnd_2553885 : Nat := 291415675846187921531645

theorem tailTrace_2553885 : CollatzResearch.WordTrace tailWord_2553885 prefixEnd_2553885 291415675846187921531645 := by
  unfold tailWord_2553885
  simp only [CollatzResearch.WordTrace]
  refine ⟨93147838352718288677935109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62098558901812192451956739 93147838352718288677935109)
  ·
    refine ⟨17465219691134679127112833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93147838352718288677935109 17465219691134679127112833)
    ·
      refine ⟨13098914768351009345334625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17465219691134679127112833 13098914768351009345334625)
      ·
        refine ⟨9824186076263257009000969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13098914768351009345334625 9824186076263257009000969)
        ·
          refine ⟨7368139557197442756750727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9824186076263257009000969 7368139557197442756750727)
          ·
            refine ⟨11052209335796164135126091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368139557197442756750727 11052209335796164135126091)
            ·
              refine ⟨16578314003694246202689137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11052209335796164135126091 16578314003694246202689137)
              ·
                refine ⟨12433735502770684652016853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16578314003694246202689137 12433735502770684652016853)
                ·
                  refine ⟨291415675846187921531645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12433735502770684652016853 291415675846187921531645)
                  ·
                    rfl

theorem cell22_2553885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2553885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553885 prefixEnd_2553885 := by exact prefixLift 2553885
  have htrace : WordTrace (prefixWord ++ tailWord_2553885) baseStart_2553885 baseEnd_2553885 := by
    simpa [prefixWord, tailWord_2553885, baseEnd_2553885] using wordTrace_append hprefix tailTrace_2553885
  have hstable : (prefixWord ++ tailWord_2553885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553885).length < 2 ^ (prefixWord ++ tailWord_2553885).sum := by decide
  have hdescent : baseEnd_2553885 < baseStart_2553885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553906 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_2553906 : Nat := 118140960795 + 2553906 * 2 ^ 59
def prefixEnd_2553906 : Nat := 4983230072969 + 3 ^ 40 * 2553906 * 2
def baseEnd_2553906 : Nat := 874254216267726709819871

theorem tailTrace_2553906 : CollatzResearch.WordTrace tailWord_2553906 prefixEnd_2553906 874254216267726709819871 := by
  unfold tailWord_2553906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23287151071410552316112393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62099069523761472842966381 23287151071410552316112393)
  ·
    refine ⟨17465363303557914237084295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23287151071410552316112393 17465363303557914237084295)
    ·
      refine ⟨26198044955336871355626443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17465363303557914237084295 26198044955336871355626443)
      ·
        refine ⟨39297067433005307033439665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26198044955336871355626443 39297067433005307033439665)
        ·
          refine ⟨29472800574753980275079749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39297067433005307033439665 29472800574753980275079749)
          ·
            refine ⟨5526150107766371301577453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29472800574753980275079749 5526150107766371301577453)
            ·
              refine ⟨2072306290412389238091545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5526150107766371301577453 2072306290412389238091545)
              ·
                refine ⟨1554229717809291928568659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072306290412389238091545 1554229717809291928568659)
                ·
                  refine ⟨2331344576713937892852989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554229717809291928568659 2331344576713937892852989)
                  ·
                    refine ⟨874254216267726709819871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331344576713937892852989 874254216267726709819871)
                    ·
                      rfl

theorem cell22_2553906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_2553906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553906 prefixEnd_2553906 := by exact prefixLift 2553906
  have htrace : WordTrace (prefixWord ++ tailWord_2553906) baseStart_2553906 baseEnd_2553906 := by
    simpa [prefixWord, tailWord_2553906, baseEnd_2553906] using wordTrace_append hprefix tailTrace_2553906
  have hstable : (prefixWord ++ tailWord_2553906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553906).length < 2 ^ (prefixWord ++ tailWord_2553906).sum := by decide
  have hdescent : baseEnd_2553906 < baseStart_2553906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553932 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_2553932 : Nat := 118140960795 + 2553932 * 2 ^ 59
def prefixEnd_2553932 : Nat := 4983230072969 + 3 ^ 40 * 2553932 * 2
def baseEnd_2553932 : Nat := 874263116599071308669791

theorem tailTrace_2553932 : CollatzResearch.WordTrace tailWord_2553932 prefixEnd_2553932 874263116599071308669791 := by
  unfold tailWord_2553932
  simp only [CollatzResearch.WordTrace]
  refine ⟨46574776291774007852448025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62099701722365343803264033 46574776291774007852448025)
  ·
    refine ⟨34931082218830505889336019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46574776291774007852448025 34931082218830505889336019)
    ·
      refine ⟨52396623328245758834004029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34931082218830505889336019 52396623328245758834004029)
      ·
        refine ⟨19648733748092159562751511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52396623328245758834004029 19648733748092159562751511)
        ·
          refine ⟨29473100622138239344127267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19648733748092159562751511 29473100622138239344127267)
          ·
            refine ⟨44209650933207359016190901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29473100622138239344127267 44209650933207359016190901)
            ·
              refine ⟨4144654774988189907767897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44209650933207359016190901 4144654774988189907767897)
              ·
                refine ⟨3108491081241142430825923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144654774988189907767897 3108491081241142430825923)
                ·
                  refine ⟨4662736621861713646238885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108491081241142430825923 4662736621861713646238885)
                  ·
                    refine ⟨874263116599071308669791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662736621861713646238885 874263116599071308669791)
                    ·
                      rfl

theorem cell22_2553932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_2553932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553932 prefixEnd_2553932 := by exact prefixLift 2553932
  have htrace : WordTrace (prefixWord ++ tailWord_2553932) baseStart_2553932 baseEnd_2553932 := by
    simpa [prefixWord, tailWord_2553932, baseEnd_2553932] using wordTrace_append hprefix tailTrace_2553932
  have hstable : (prefixWord ++ tailWord_2553932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553932).length < 2 ^ (prefixWord ++ tailWord_2553932).sum := by decide
  have hdescent : baseEnd_2553932 < baseStart_2553932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553945 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_2553945 : Nat := 118140960795 + 2553945 * 2 ^ 59
def prefixEnd_2553945 : Nat := 4983230072969 + 3 ^ 40 * 2553945 * 2
def baseEnd_2553945 : Nat := 874267566764743608094751

theorem tailTrace_2553945 : CollatzResearch.WordTrace tailWord_2553945 prefixEnd_2553945 874267566764743608094751 := by
  unfold tailWord_2553945
  simp only [CollatzResearch.WordTrace]
  refine ⟨93150026732500918925119289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62100017821667279283412859 93150026732500918925119289)
  ·
    refine ⟨69862520049375689193839467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93150026732500918925119289 69862520049375689193839467)
    ·
      refine ⟨104793780074063533790759201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69862520049375689193839467 104793780074063533790759201)
      ·
        refine ⟨78595335055547650343069401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104793780074063533790759201 78595335055547650343069401)
        ·
          refine ⟨58946501291660737757302051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78595335055547650343069401 58946501291660737757302051)
          ·
            refine ⟨88419751937491106635953077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58946501291660737757302051 88419751937491106635953077)
            ·
              refine ⟨8289351744139791247120601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88419751937491106635953077 8289351744139791247120601)
              ·
                refine ⟨6217013808104843435340451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8289351744139791247120601 6217013808104843435340451)
                ·
                  refine ⟨9325520712157265153010677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6217013808104843435340451 9325520712157265153010677)
                  ·
                    refine ⟨874267566764743608094751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9325520712157265153010677 874267566764743608094751)
                    ·
                      rfl

theorem cell22_2553945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_2553945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553945 prefixEnd_2553945 := by exact prefixLift 2553945
  have htrace : WordTrace (prefixWord ++ tailWord_2553945) baseStart_2553945 baseEnd_2553945 := by
    simpa [prefixWord, tailWord_2553945, baseEnd_2553945] using wordTrace_append hprefix tailTrace_2553945
  have hstable : (prefixWord ++ tailWord_2553945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553945).length < 2 ^ (prefixWord ++ tailWord_2553945).sum := by decide
  have hdescent : baseEnd_2553945 < baseStart_2553945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553964 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_2553964 : Nat := 118140960795 + 2553964 * 2 ^ 59
def prefixEnd_2553964 : Nat := 4983230072969 + 3 ^ 40 * 2553964 * 2
def baseEnd_2553964 : Nat := 291424690284344630623231

theorem tailTrace_2553964 : CollatzResearch.WordTrace tailWord_2553964 prefixEnd_2553964 291424690284344630623231 := by
  unfold tailWord_2553964
  simp only [CollatzResearch.WordTrace]
  refine ⟨46575359859716042585030473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62100479812954723446707297 46575359859716042585030473)
  ·
    refine ⟨34931519894787031938772855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46575359859716042585030473 34931519894787031938772855)
    ·
      refine ⟨52397279842180547908159283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34931519894787031938772855 52397279842180547908159283)
      ·
        refine ⟨78595919763270821862238925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52397279842180547908159283 78595919763270821862238925)
        ·
          refine ⟨29473469911226558198339597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78595919763270821862238925 29473469911226558198339597)
          ·
            refine ⟨11052551216709959324377349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29473469911226558198339597 11052551216709959324377349)
            ·
              refine ⟨2072353353133117373320753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11052551216709959324377349 2072353353133117373320753)
              ·
                refine ⟨1554265014849838029990565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072353353133117373320753 1554265014849838029990565)
                ·
                  refine ⟨291424690284344630623231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554265014849838029990565 291424690284344630623231)
                  ·
                    rfl

theorem cell22_2553964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_2553964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553964 prefixEnd_2553964 := by exact prefixLift 2553964
  have htrace : WordTrace (prefixWord ++ tailWord_2553964) baseStart_2553964 baseEnd_2553964 := by
    simpa [prefixWord, tailWord_2553964, baseEnd_2553964] using wordTrace_append hprefix tailTrace_2553964
  have hstable : (prefixWord ++ tailWord_2553964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553964).length < 2 ^ (prefixWord ++ tailWord_2553964).sum := by decide
  have hdescent : baseEnd_2553964 < baseStart_2553964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553975 : List Nat := [1, 1, 3, 1, 1, 5, 3, 7]
def baseStart_2553975 : Nat := 118140960795 + 2553975 * 2 ^ 59
def prefixEnd_2553975 : Nat := 4983230072969 + 3 ^ 40 * 2553975 * 2
def baseEnd_2553975 : Nat := 97141981819759281093851

theorem tailTrace_2553975 : CollatzResearch.WordTrace tailWord_2553975 prefixEnd_2553975 97141981819759281093851 := by
  unfold tailWord_2553975
  simp only [CollatzResearch.WordTrace]
  refine ⟨93151120922392234048711379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62100747281594822699140919 93151120922392234048711379)
  ·
    refine ⟨139726681383588351073067069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93151120922392234048711379 139726681383588351073067069)
    ·
      refine ⟨52397505518845631652400151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139726681383588351073067069 52397505518845631652400151)
      ·
        refine ⟨78596258278268447478600227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52397505518845631652400151 78596258278268447478600227)
        ·
          refine ⟨117894387417402671217900341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78596258278268447478600227 117894387417402671217900341)
          ·
            refine ⟨11052598820381500426678157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117894387417402671217900341 11052598820381500426678157)
            ·
              refine ⟨4144724557643062660004309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11052598820381500426678157 4144724557643062660004309)
              ·
                refine ⟨97141981819759281093851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4144724557643062660004309 97141981819759281093851)
                ·
                  rfl

theorem cell22_2553975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 7].length) (baseStart_2553975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553975 prefixEnd_2553975 := by exact prefixLift 2553975
  have htrace : WordTrace (prefixWord ++ tailWord_2553975) baseStart_2553975 baseEnd_2553975 := by
    simpa [prefixWord, tailWord_2553975, baseEnd_2553975] using wordTrace_append hprefix tailTrace_2553975
  have hstable : (prefixWord ++ tailWord_2553975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553975).length < 2 ^ (prefixWord ++ tailWord_2553975).sum := by decide
  have hdescent : baseEnd_2553975 < baseStart_2553975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2553994 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2553994 : Nat := 118140960795 + 2553994 * 2 ^ 59
def prefixEnd_2553994 : Nat := 4983230072969 + 3 ^ 40 * 2553994 * 2
def baseEnd_2553994 : Nat := 874284340466123813619601

theorem tailTrace_2553994 : CollatzResearch.WordTrace tailWord_2553994 prefixEnd_2553994 874284340466123813619601 := by
  unfold tailWord_2553994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23287953477330850073413259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62101209272882266862435357 23287953477330850073413259)
  ·
    refine ⟨34931930215996275110119889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23287953477330850073413259 34931930215996275110119889)
    ·
      refine ⟨26198947661997206332589917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34931930215996275110119889 26198947661997206332589917)
      ·
        refine ⟨9824605373248952374721219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26198947661997206332589917 9824605373248952374721219)
        ·
          refine ⟨14736908059873428562081829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9824605373248952374721219 14736908059873428562081829)
          ·
            refine ⟨2763170261226267855390343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14736908059873428562081829 2763170261226267855390343)
            ·
              refine ⟨4144755391839401783085515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763170261226267855390343 4144755391839401783085515)
              ·
                refine ⟨6217133087759102674628273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144755391839401783085515 6217133087759102674628273)
                ·
                  refine ⟨4662849815819327005971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6217133087759102674628273 4662849815819327005971205)
                  ·
                    refine ⟨874284340466123813619601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4662849815819327005971205 874284340466123813619601)
                    ·
                      rfl

theorem cell22_2553994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2553994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2553994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2553994 prefixEnd_2553994 := by exact prefixLift 2553994
  have htrace : WordTrace (prefixWord ++ tailWord_2553994) baseStart_2553994 baseEnd_2553994 := by
    simpa [prefixWord, tailWord_2553994, baseEnd_2553994] using wordTrace_append hprefix tailTrace_2553994
  have hstable : (prefixWord ++ tailWord_2553994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2553994).length < 2 ^ (prefixWord ++ tailWord_2553994).sum := by decide
  have hdescent : baseEnd_2553994 < baseStart_2553994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2553994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554030 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2554030 : Nat := 118140960795 + 2554030 * 2 ^ 59
def prefixEnd_2554030 : Nat := 4983230072969 + 3 ^ 40 * 2554030 * 2
def baseEnd_2554030 : Nat := 874296664001831719719491

theorem tailTrace_2554030 : CollatzResearch.WordTrace tailWord_2554030 prefixEnd_2554030 874296664001831719719491 := by
  unfold tailWord_2554030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644140867149122305245443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62102084624795318961309029 11644140867149122305245443)
  ·
    refine ⟨17466211300723683457868165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644140867149122305245443 17466211300723683457868165)
    ·
      refine ⟨3274914618885690648350281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17466211300723683457868165 3274914618885690648350281)
      ·
        refine ⟨2456185964164267986262711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3274914618885690648350281 2456185964164267986262711)
        ·
          refine ⟨3684278946246401979394067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456185964164267986262711 3684278946246401979394067)
          ·
            refine ⟨5526418419369602969091101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684278946246401979394067 5526418419369602969091101)
            ·
              refine ⟨2072406907263601113409163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5526418419369602969091101 2072406907263601113409163)
              ·
                refine ⟨3108610360895401670113745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072406907263601113409163 3108610360895401670113745)
                ·
                  refine ⟨2331457770671551252585309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3108610360895401670113745 2331457770671551252585309)
                  ·
                    refine ⟨874296664001831719719491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331457770671551252585309 874296664001831719719491)
                    ·
                      rfl

theorem cell22_2554030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2554030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554030 prefixEnd_2554030 := by exact prefixLift 2554030
  have htrace : WordTrace (prefixWord ++ tailWord_2554030) baseStart_2554030 baseEnd_2554030 := by
    simpa [prefixWord, tailWord_2554030, baseEnd_2554030] using wordTrace_append hprefix tailTrace_2554030
  have hstable : (prefixWord ++ tailWord_2554030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554030).length < 2 ^ (prefixWord ++ tailWord_2554030).sum := by decide
  have hdescent : baseEnd_2554030 < baseStart_2554030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554065 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 8]
def baseStart_2554065 : Nat := 118140960795 + 2554065 * 2 ^ 59
def prefixEnd_2554065 : Nat := 4983230072969 + 3 ^ 40 * 2554065 * 2
def baseEnd_2554065 : Nat := 291436215072367765031461

theorem tailTrace_2554065 : CollatzResearch.WordTrace tailWord_2554065 prefixEnd_2554065 291436215072367765031461 := by
  unfold tailWord_2554065
  simp only [CollatzResearch.WordTrace]
  refine ⟨93154403492066179419487649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62102935661377452946325099 93154403492066179419487649)
  ·
    refine ⟨69865802619049634564615737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93154403492066179419487649 69865802619049634564615737)
    ·
      refine ⟨52399351964287225923461803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69865802619049634564615737 52399351964287225923461803)
      ·
        refine ⟨78599027946430838885192705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52399351964287225923461803 78599027946430838885192705)
        ·
          refine ⟨58949270959823129163894529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78599027946430838885192705 58949270959823129163894529)
          ·
            refine ⟨44211953219867346872920897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58949270959823129163894529 44211953219867346872920897)
            ·
              refine ⟨33158964914900510154690673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44211953219867346872920897 33158964914900510154690673)
              ·
                refine ⟨24869223686175382616018005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33158964914900510154690673 24869223686175382616018005)
                ·
                  refine ⟨291436215072367765031461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24869223686175382616018005 291436215072367765031461)
                  ·
                    rfl

theorem cell22_2554065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_2554065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554065 prefixEnd_2554065 := by exact prefixLift 2554065
  have htrace : WordTrace (prefixWord ++ tailWord_2554065) baseStart_2554065 baseEnd_2554065 := by
    simpa [prefixWord, tailWord_2554065, baseEnd_2554065] using wordTrace_append hprefix tailTrace_2554065
  have hstable : (prefixWord ++ tailWord_2554065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554065).length < 2 ^ (prefixWord ++ tailWord_2554065).sum := by decide
  have hdescent : baseEnd_2554065 < baseStart_2554065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554112 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_2554112 : Nat := 118140960795 + 2554112 * 2 ^ 59
def prefixEnd_2554112 : Nat := 4983230072969 + 3 ^ 40 * 2554112 * 2
def baseEnd_2554112 : Nat := 874324734277610839169239

theorem tailTrace_2554112 : CollatzResearch.WordTrace tailWord_2554112 prefixEnd_2554112 874324734277610839169239 := by
  unfold tailWord_2554112
  simp only [CollatzResearch.WordTrace]
  refine ⟨46578058861447953223224295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62104078481930604297632393 46578058861447953223224295)
  ·
    refine ⟨69867088292171929834836443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46578058861447953223224295 69867088292171929834836443)
    ·
      refine ⟨104800632438257894752254665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69867088292171929834836443 104800632438257894752254665)
      ·
        refine ⟨78600474328693421064190999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104800632438257894752254665 78600474328693421064190999)
        ·
          refine ⟨117900711493040131596286499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78600474328693421064190999 117900711493040131596286499)
          ·
            refine ⟨176851067239560197394429749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117900711493040131596286499 176851067239560197394429749)
            ·
              refine ⟨16579787553708768505727789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176851067239560197394429749 16579787553708768505727789)
              ·
                refine ⟨6217420332640788189647921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16579787553708768505727789 6217420332640788189647921)
                ·
                  refine ⟨4663065249480591142235941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6217420332640788189647921 4663065249480591142235941)
                  ·
                    refine ⟨874324734277610839169239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663065249480591142235941 874324734277610839169239)
                    ·
                      rfl

theorem cell22_2554112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_2554112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554112 prefixEnd_2554112 := by exact prefixLift 2554112
  have htrace : WordTrace (prefixWord ++ tailWord_2554112) baseStart_2554112 baseEnd_2554112 := by
    simpa [prefixWord, tailWord_2554112, baseEnd_2554112] using wordTrace_append hprefix tailTrace_2554112
  have hstable : (prefixWord ++ tailWord_2554112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554112).length < 2 ^ (prefixWord ++ tailWord_2554112).sum := by decide
  have hdescent : baseEnd_2554112 < baseStart_2554112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554114 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2554114 : Nat := 118140960795 + 2554114 * 2 ^ 59
def prefixEnd_2554114 : Nat := 4983230072969 + 3 ^ 40 * 2554114 * 2
def baseEnd_2554114 : Nat := 874325418918483500619233

theorem tailTrace_2554114 : CollatzResearch.WordTrace tailWord_2554114 prefixEnd_2554114 874325418918483500619233 := by
  unfold tailWord_2554114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23289047667222165197005349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62104127112592440525347597 23289047667222165197005349)
  ·
    refine ⟨4366696437604155974438503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23289047667222165197005349 4366696437604155974438503)
    ·
      refine ⟨6550044656406233961657755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366696437604155974438503 6550044656406233961657755)
      ·
        refine ⟨9825066984609350942486633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550044656406233961657755 9825066984609350942486633)
        ·
          refine ⟨7368800238457013206864975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9825066984609350942486633 7368800238457013206864975)
          ·
            refine ⟨11053200357685519810297463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368800238457013206864975 11053200357685519810297463)
            ·
              refine ⟨16579800536528279715446195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11053200357685519810297463 16579800536528279715446195)
              ·
                refine ⟨24869700804792419573169293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16579800536528279715446195 24869700804792419573169293)
                ·
                  refine ⟨9326137801797157339938485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24869700804792419573169293 9326137801797157339938485)
                  ·
                    refine ⟨874325418918483500619233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9326137801797157339938485 874325418918483500619233)
                    ·
                      rfl

theorem cell22_2554114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2554114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554114 prefixEnd_2554114 := by exact prefixLift 2554114
  have htrace : WordTrace (prefixWord ++ tailWord_2554114) baseStart_2554114 baseEnd_2554114 := by
    simpa [prefixWord, tailWord_2554114, baseEnd_2554114] using wordTrace_append hprefix tailTrace_2554114
  have hstable : (prefixWord ++ tailWord_2554114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554114).length < 2 ^ (prefixWord ++ tailWord_2554114).sum := by decide
  have hdescent : baseEnd_2554114 < baseStart_2554114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554144 : List Nat := [2, 1, 1, 5, 2, 3, 1, 7]
def baseStart_2554144 : Nat := 118140960795 + 2554144 * 2 ^ 59
def prefixEnd_2554144 : Nat := 4983230072969 + 3 ^ 40 * 2554144 * 2
def baseEnd_2554144 : Nat := 97148409836841491374349

theorem tailTrace_2554144 : CollatzResearch.WordTrace tailWord_2554144 prefixEnd_2554144 97148409836841491374349 := by
  unfold tailWord_2554144
  simp only [CollatzResearch.WordTrace]
  refine ⟨46578642429389987955806743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62104856572519983941075657 46578642429389987955806743)
  ·
    refine ⟨69867963644084981933710115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46578642429389987955806743 69867963644084981933710115)
    ·
      refine ⟨104801945466127472900565173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69867963644084981933710115 104801945466127472900565173)
      ·
        refine ⟨9825182387449450584427985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104801945466127472900565173 9825182387449450584427985)
        ·
          refine ⟨7368886790587087938320989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9825182387449450584427985 7368886790587087938320989)
          ·
            refine ⟨2763332546470157976870371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7368886790587087938320989 2763332546470157976870371)
            ·
              refine ⟨4144998819705236965305557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763332546470157976870371 4144998819705236965305557)
              ·
                refine ⟨97148409836841491374349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4144998819705236965305557 97148409836841491374349)
                ·
                  rfl

theorem cell22_2554144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_2554144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554144 prefixEnd_2554144 := by exact prefixLift 2554144
  have htrace : WordTrace (prefixWord ++ tailWord_2554144) baseStart_2554144 baseEnd_2554144 := by
    simpa [prefixWord, tailWord_2554144, baseEnd_2554144] using wordTrace_append hprefix tailTrace_2554144
  have hstable : (prefixWord ++ tailWord_2554144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554144).length < 2 ^ (prefixWord ++ tailWord_2554144).sum := by decide
  have hdescent : baseEnd_2554144 < baseStart_2554144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554172 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_2554172 : Nat := 118140960795 + 2554172 * 2 ^ 59
def prefixEnd_2554172 : Nat := 4983230072969 + 3 ^ 40 * 2554172 * 2
def baseEnd_2554172 : Nat := 291448424501263560889685

theorem tailTrace_2554172 : CollatzResearch.WordTrace tailWord_2554172 prefixEnd_2554172 291448424501263560889685 := by
  unfold tailWord_2554172
  simp only [CollatzResearch.WordTrace]
  refine ⟨46579153051339268346816385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62105537401785691129088513 46579153051339268346816385)
  ·
    refine ⟨34934364788504451260112289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46579153051339268346816385 34934364788504451260112289)
    ·
      refine ⟨26200773591378338445084217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34934364788504451260112289 26200773591378338445084217)
      ·
        refine ⟨19650580193533753833813163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26200773591378338445084217 19650580193533753833813163)
        ·
          refine ⟨29475870290300630750719745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19650580193533753833813163 29475870290300630750719745)
          ·
            refine ⟨22106902717725473063039809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29475870290300630750719745 22106902717725473063039809)
            ·
              refine ⟨16580177038294104797279857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22106902717725473063039809 16580177038294104797279857)
              ·
                refine ⟨12435132778720578597959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16580177038294104797279857 12435132778720578597959893)
                ·
                  refine ⟨291448424501263560889685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12435132778720578597959893 291448424501263560889685)
                  ·
                    rfl

theorem cell22_2554172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_2554172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554172 prefixEnd_2554172 := by exact prefixLift 2554172
  have htrace : WordTrace (prefixWord ++ tailWord_2554172) baseStart_2554172 baseEnd_2554172 := by
    simpa [prefixWord, tailWord_2554172, baseEnd_2554172] using wordTrace_append hprefix tailTrace_2554172
  have hstable : (prefixWord ++ tailWord_2554172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554172).length < 2 ^ (prefixWord ++ tailWord_2554172).sum := by decide
  have hdescent : baseEnd_2554172 < baseStart_2554172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554217 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 6]
def baseStart_2554217 : Nat := 118140960795 + 2554217 * 2 ^ 59
def prefixEnd_2554217 : Nat := 4983230072969 + 3 ^ 40 * 2554217 * 2
def baseEnd_2554217 : Nat := 291453559307808521764639

theorem tailTrace_2554217 : CollatzResearch.WordTrace tailWord_2554217 prefixEnd_2554217 291453559307808521764639 := by
  unfold tailWord_2554217
  simp only [CollatzResearch.WordTrace]
  refine ⟨93159947387515509379020905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62106631591677006252680603 93159947387515509379020905)
  ·
    refine ⟨69869960540636632034265679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93159947387515509379020905 69869960540636632034265679)
    ·
      refine ⟨104804940810954948051398519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69869960540636632034265679 104804940810954948051398519)
      ·
        refine ⟨157207411216432422077097779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104804940810954948051398519 157207411216432422077097779)
        ·
          refine ⟨235811116824648633115646669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157207411216432422077097779 235811116824648633115646669)
          ·
            refine ⟨88429168809243237418367501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235811116824648633115646669 88429168809243237418367501)
            ·
              refine ⟨33160938303466214031887813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88429168809243237418367501 33160938303466214031887813)
              ·
                refine ⟨6217675931899915130978965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33160938303466214031887813 6217675931899915130978965)
                ·
                  refine ⟨291453559307808521764639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6217675931899915130978965 291453559307808521764639)
                  ·
                    rfl

theorem cell22_2554217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_2554217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554217 prefixEnd_2554217 := by exact prefixLift 2554217
  have htrace : WordTrace (prefixWord ++ tailWord_2554217) baseStart_2554217 baseEnd_2554217 := by
    simpa [prefixWord, tailWord_2554217, baseEnd_2554217] using wordTrace_append hprefix tailTrace_2554217
  have hstable : (prefixWord ++ tailWord_2554217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554217).length < 2 ^ (prefixWord ++ tailWord_2554217).sum := by decide
  have hdescent : baseEnd_2554217 < baseStart_2554217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554270 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2554270 : Nat := 118140960795 + 2554270 * 2 ^ 59
def prefixEnd_2554270 : Nat := 4983230072969 + 3 ^ 40 * 2554270 * 2
def baseEnd_2554270 : Nat := 874378820906551093718755

theorem tailTrace_2554270 : CollatzResearch.WordTrace tailWord_2554270 prefixEnd_2554270 874378820906551093718755 := by
  unfold tailWord_2554270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645235057040437428837533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62107920304215666287133509 11645235057040437428837533)
  ·
    refine ⟨4366963146390164035814075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11645235057040437428837533 4366963146390164035814075)
    ·
      refine ⟨6550444719585246053721113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366963146390164035814075 6550444719585246053721113)
      ·
        refine ⟨4912833539688934540290835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6550444719585246053721113 4912833539688934540290835)
        ·
          refine ⟨7369250309533401810436253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912833539688934540290835 7369250309533401810436253)
          ·
            refine ⟨2763468866075025678913595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7369250309533401810436253 2763468866075025678913595)
            ·
              refine ⟨4145203299112538518370393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763468866075025678913595 4145203299112538518370393)
              ·
                refine ⟨3108902474334403888777795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4145203299112538518370393 3108902474334403888777795)
                ·
                  refine ⟨4663353711501605833166693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108902474334403888777795 4663353711501605833166693)
                  ·
                    refine ⟨874378820906551093718755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4663353711501605833166693 874378820906551093718755)
                    ·
                      rfl

theorem cell22_2554270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2554270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554270 prefixEnd_2554270 := by exact prefixLift 2554270
  have htrace : WordTrace (prefixWord ++ tailWord_2554270) baseStart_2554270 baseEnd_2554270 := by
    simpa [prefixWord, tailWord_2554270, baseEnd_2554270] using wordTrace_append hprefix tailTrace_2554270
  have hstable : (prefixWord ++ tailWord_2554270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554270).length < 2 ^ (prefixWord ++ tailWord_2554270).sum := by decide
  have hdescent : baseEnd_2554270 < baseStart_2554270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554279 : List Nat := [1, 1, 6, 1, 1, 2, 2, 8]
def baseStart_2554279 : Nat := 118140960795 + 2554279 * 2 ^ 59
def prefixEnd_2554279 : Nat := 4983230072969 + 3 ^ 40 * 2554279 * 2
def baseEnd_2554279 : Nat := 97153544643386452249303

theorem tailTrace_2554279 : CollatzResearch.WordTrace tailWord_2554279 prefixEnd_2554279 97153544643386452249303 := by
  unfold tailWord_2554279
  simp only [CollatzResearch.WordTrace]
  refine ⟨93162208713290893967777891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62108139142193929311851927 93162208713290893967777891)
  ·
    refine ⟨139743313069936340951666837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93162208713290893967777891 139743313069936340951666837)
    ·
      refine ⟨6550467800153265982109383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139743313069936340951666837 6550467800153265982109383)
      ·
        refine ⟨9825701700229898973164075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550467800153265982109383 9825701700229898973164075)
        ·
          refine ⟨14738552550344848459746113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825701700229898973164075 14738552550344848459746113)
          ·
            refine ⟨11053914412758636344809585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14738552550344848459746113 11053914412758636344809585)
            ·
              refine ⟨8290435809568977258607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11053914412758636344809585 8290435809568977258607189)
              ·
                refine ⟨97153544643386452249303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8290435809568977258607189 97153544643386452249303)
                ·
                  rfl

theorem cell22_2554279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 8].length) (baseStart_2554279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554279 prefixEnd_2554279 := by exact prefixLift 2554279
  have htrace : WordTrace (prefixWord ++ tailWord_2554279) baseStart_2554279 baseEnd_2554279 := by
    simpa [prefixWord, tailWord_2554279, baseEnd_2554279] using wordTrace_append hprefix tailTrace_2554279
  have hstable : (prefixWord ++ tailWord_2554279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554279).length < 2 ^ (prefixWord ++ tailWord_2554279).sum := by decide
  have hdescent : baseEnd_2554279 < baseStart_2554279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554326 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2554326 : Nat := 118140960795 + 2554326 * 2 ^ 59
def prefixEnd_2554326 : Nat := 4983230072969 + 3 ^ 40 * 2554326 * 2
def baseEnd_2554326 : Nat := 874397990850985614318583

theorem tailTrace_2554326 : CollatzResearch.WordTrace tailWord_2554326 prefixEnd_2554326 874397990850985614318583 := by
  unfold tailWord_2554326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822745184007538812171177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62109281962747080663159221 5822745184007538812171177)
  ·
    refine ⟨4367058888005654109128383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5822745184007538812171177 4367058888005654109128383)
    ·
      refine ⟨6550588332008481163692575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4367058888005654109128383 6550588332008481163692575)
      ·
        refine ⟨9825882498012721745538863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550588332008481163692575 9825882498012721745538863)
        ·
          refine ⟨14738823747019082618308295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825882498012721745538863 14738823747019082618308295)
          ·
            refine ⟨22108235620528623927462443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14738823747019082618308295 22108235620528623927462443)
            ·
              refine ⟨33162353430792935891193665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22108235620528623927462443 33162353430792935891193665)
              ·
                refine ⟨24871765073094701918395249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33162353430792935891193665 24871765073094701918395249)
                ·
                  refine ⟨18653823804821026438796437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24871765073094701918395249 18653823804821026438796437)
                  ·
                    refine ⟨874397990850985614318583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18653823804821026438796437 874397990850985614318583)
                    ·
                      rfl

theorem cell22_2554326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2554326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554326 prefixEnd_2554326 := by exact prefixLift 2554326
  have htrace : WordTrace (prefixWord ++ tailWord_2554326) baseStart_2554326 baseEnd_2554326 := by
    simpa [prefixWord, tailWord_2554326, baseEnd_2554326] using wordTrace_append hprefix tailTrace_2554326
  have hstable : (prefixWord ++ tailWord_2554326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554326).length < 2 ^ (prefixWord ++ tailWord_2554326).sum := by decide
  have hdescent : baseEnd_2554326 < baseStart_2554326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554401 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2554401 : Nat := 118140960795 + 2554401 * 2 ^ 59
def prefixEnd_2554401 : Nat := 4983230072969 + 3 ^ 40 * 2554401 * 2
def baseEnd_2554401 : Nat := 874423664883710418693353

theorem tailTrace_2554401 : CollatzResearch.WordTrace tailWord_2554401 prefixEnd_2554401 874423664883710418693353 := by
  unfold tailWord_2554401
  simp only [CollatzResearch.WordTrace]
  refine ⟨93166658418848908803719057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62111105612565939202479371 93166658418848908803719057)
  ·
    refine ⟨69874993814136681602789293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93166658418848908803719057 69874993814136681602789293)
    ·
      refine ⟨26203122680301255601045985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69874993814136681602789293 26203122680301255601045985)
      ·
        refine ⟨19652342010225941700784489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26203122680301255601045985 19652342010225941700784489)
        ·
          refine ⟨14739256507669456275588367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19652342010225941700784489 14739256507669456275588367)
          ·
            refine ⟨22108884761504184413382551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14739256507669456275588367 22108884761504184413382551)
            ·
              refine ⟨33163327142256276620073827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22108884761504184413382551 33163327142256276620073827)
              ·
                refine ⟨49744990713384414930110741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33163327142256276620073827 49744990713384414930110741)
                ·
                  refine ⟨2331796439689894449848941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49744990713384414930110741 2331796439689894449848941)
                  ·
                    refine ⟨874423664883710418693353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331796439689894449848941 874423664883710418693353)
                    ·
                      rfl

theorem cell22_2554401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2554401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554401 prefixEnd_2554401 := by exact prefixLift 2554401
  have htrace : WordTrace (prefixWord ++ tailWord_2554401) baseStart_2554401 baseEnd_2554401 := by
    simpa [prefixWord, tailWord_2554401, baseEnd_2554401] using wordTrace_append hprefix tailTrace_2554401
  have hstable : (prefixWord ++ tailWord_2554401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554401).length < 2 ^ (prefixWord ++ tailWord_2554401).sum := by decide
  have hdescent : baseEnd_2554401 < baseStart_2554401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554403 : List Nat := [1, 1, 1, 4, 4, 1, 3, 3, 4]
def baseStart_2554403 : Nat := 118140960795 + 2554403 * 2 ^ 59
def prefixEnd_2554403 : Nat := 4983230072969 + 3 ^ 40 * 2554403 * 2
def baseEnd_2554403 : Nat := 291474783174861026714449

theorem tailTrace_2554403 : CollatzResearch.WordTrace tailWord_2554403 prefixEnd_2554403 291474783174861026714449 := by
  unfold tailWord_2554403
  simp only [CollatzResearch.WordTrace]
  refine ⟨93166731364841663145291863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62111154243227775430194575 93166731364841663145291863)
  ·
    refine ⟨139750097047262494717937795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93166731364841663145291863 139750097047262494717937795)
    ·
      refine ⟨209625145570893742076906693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139750097047262494717937795 209625145570893742076906693)
      ·
        refine ⟨39304714794542576639420005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209625145570893742076906693 39304714794542576639420005)
        ·
          refine ⟨7369634023976733119891251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39304714794542576639420005 7369634023976733119891251)
          ·
            refine ⟨11054451035965099679836877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7369634023976733119891251 11054451035965099679836877)
            ·
              refine ⟨4145419138486912379938829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11054451035965099679836877 4145419138486912379938829)
              ·
                refine ⟨1554532176932592142477061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145419138486912379938829 1554532176932592142477061)
                ·
                  refine ⟨291474783174861026714449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554532176932592142477061 291474783174861026714449)
                  ·
                    rfl

theorem cell22_2554403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 4].length) (baseStart_2554403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554403 prefixEnd_2554403 := by exact prefixLift 2554403
  have htrace : WordTrace (prefixWord ++ tailWord_2554403) baseStart_2554403 baseEnd_2554403 := by
    simpa [prefixWord, tailWord_2554403, baseEnd_2554403] using wordTrace_append hprefix tailTrace_2554403
  have hstable : (prefixWord ++ tailWord_2554403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554403).length < 2 ^ (prefixWord ++ tailWord_2554403).sum := by decide
  have hdescent : baseEnd_2554403 < baseStart_2554403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554476 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_2554476 : Nat := 118140960795 + 2554476 * 2 ^ 59
def prefixEnd_2554476 : Nat := 4983230072969 + 3 ^ 40 * 2554476 * 2
def baseEnd_2554476 : Nat := 291483112972145074356041

theorem tailTrace_2554476 : CollatzResearch.WordTrace tailWord_2554476 prefixEnd_2554476 291483112972145074356041 := by
  unfold tailWord_2554476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46584696946788598306349641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62112929262384797741799521 46584696946788598306349641)
  ·
    refine ⟨34938522710091448729762231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46584696946788598306349641 34938522710091448729762231)
    ·
      refine ⟨52407784065137173094643347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34938522710091448729762231 52407784065137173094643347)
      ·
        refine ⟨78611676097705759641965021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52407784065137173094643347 78611676097705759641965021)
        ·
          refine ⟨29479378536639659865736883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78611676097705759641965021 29479378536639659865736883)
          ·
            refine ⟨44219067804959489798605325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29479378536639659865736883 44219067804959489798605325)
            ·
              refine ⟨16582150426859808674476997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44219067804959489798605325 16582150426859808674476997)
              ·
                refine ⟨3109153205036214126464437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16582150426859808674476997 3109153205036214126464437)
                ·
                  refine ⟨291483112972145074356041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3109153205036214126464437 291483112972145074356041)
                  ·
                    rfl

theorem cell22_2554476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_2554476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554476 prefixEnd_2554476 := by exact prefixLift 2554476
  have htrace : WordTrace (prefixWord ++ tailWord_2554476) baseStart_2554476 baseEnd_2554476 := by
    simpa [prefixWord, tailWord_2554476, baseEnd_2554476] using wordTrace_append hprefix tailTrace_2554476
  have hstable : (prefixWord ++ tailWord_2554476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554476).length < 2 ^ (prefixWord ++ tailWord_2554476).sum := by decide
  have hdescent : baseEnd_2554476 < baseStart_2554476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554572 : List Nat := [2, 2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_2554572 : Nat := 118140960795 + 2554572 * 2 ^ 59
def prefixEnd_2554572 : Nat := 4983230072969 + 3 ^ 40 * 2554572 * 2
def baseEnd_2554572 : Nat := 291494067226107657555943

theorem tailTrace_2554572 : CollatzResearch.WordTrace tailWord_2554572 prefixEnd_2554572 291494067226107657555943 := by
  unfold tailWord_2554572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46586447650614702504096985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62115263534152936672129313 46586447650614702504096985)
  ·
    refine ⟨34939835737961026878072739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46586447650614702504096985 34939835737961026878072739)
    ·
      refine ⟨52409753606941540317109109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34939835737961026878072739 52409753606941540317109109)
      ·
        refine ⟨4913414400650769404728979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52409753606941540317109109 4913414400650769404728979)
        ·
          refine ⟨7370121600976154107093469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913414400650769404728979 7370121600976154107093469)
          ·
            refine ⟨2763795600366057790160051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7370121600976154107093469 2763795600366057790160051)
            ·
              refine ⟨4145693400549086685240077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763795600366057790160051 4145693400549086685240077)
              ·
                refine ⟨1554635025205907506965029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145693400549086685240077 1554635025205907506965029)
                ·
                  refine ⟨291494067226107657555943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554635025205907506965029 291494067226107657555943)
                  ·
                    rfl

theorem cell22_2554572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_2554572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554572 prefixEnd_2554572 := by exact prefixLift 2554572
  have htrace : WordTrace (prefixWord ++ tailWord_2554572) baseStart_2554572 baseEnd_2554572 := by
    simpa [prefixWord, tailWord_2554572, baseEnd_2554572] using wordTrace_append hprefix tailTrace_2554572
  have hstable : (prefixWord ++ tailWord_2554572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554572).length < 2 ^ (prefixWord ++ tailWord_2554572).sum := by decide
  have hdescent : baseEnd_2554572 < baseStart_2554572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554660 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_2554660 : Nat := 118140960795 + 2554660 * 2 ^ 59
def prefixEnd_2554660 : Nat := 4983230072969 + 3 ^ 40 * 2554660 * 2
def baseEnd_2554660 : Nat := 874512325876720076467559

theorem tailTrace_2554660 : CollatzResearch.WordTrace tailWord_2554660 prefixEnd_2554660 874512325876720076467559 := by
  unfold tailWord_2554660
  simp only [CollatzResearch.WordTrace]
  refine ⟨46588052462455298018698717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62117403283273730691598289 46588052462455298018698717)
  ·
    refine ⟨17470519673420736757012019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46588052462455298018698717 17470519673420736757012019)
    ·
      refine ⟨26205779510131105135518029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17470519673420736757012019 26205779510131105135518029)
      ·
        refine ⟨9827167316299164425819261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26205779510131105135518029 9827167316299164425819261)
        ·
          refine ⟨3685187743612186659682223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9827167316299164425819261 3685187743612186659682223)
          ·
            refine ⟨5527781615418279989523335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685187743612186659682223 5527781615418279989523335)
            ·
              refine ⟨8291672423127419984285003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5527781615418279989523335 8291672423127419984285003)
              ·
                refine ⟨12437508634691129976427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8291672423127419984285003 12437508634691129976427505)
                ·
                  refine ⟨9328131476018347482320629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12437508634691129976427505 9328131476018347482320629)
                  ·
                    refine ⟨874512325876720076467559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9328131476018347482320629 874512325876720076467559)
                    ·
                      rfl

theorem cell22_2554660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_2554660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554660 prefixEnd_2554660 := by exact prefixLift 2554660
  have htrace : WordTrace (prefixWord ++ tailWord_2554660) baseStart_2554660 baseEnd_2554660 := by
    simpa [prefixWord, tailWord_2554660, baseEnd_2554660] using wordTrace_append hprefix tailTrace_2554660
  have hstable : (prefixWord ++ tailWord_2554660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554660).length < 2 ^ (prefixWord ++ tailWord_2554660).sum := by decide
  have hdescent : baseEnd_2554660 < baseStart_2554660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554673 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 6]
def baseStart_2554673 : Nat := 118140960795 + 2554673 * 2 ^ 59
def prefixEnd_2554673 : Nat := 4983230072969 + 3 ^ 40 * 2554673 * 2
def baseEnd_2554673 : Nat := 291505592014130791964173

theorem tailTrace_2554673 : CollatzResearch.WordTrace tailWord_2554673 prefixEnd_2554673 291505592014130791964173 := by
  unfold tailWord_2554673
  simp only [CollatzResearch.WordTrace]
  refine ⟨93176579073863499257620673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62117719382575666171747115 93176579073863499257620673)
  ·
    refine ⟨69882434305397624443215505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93176579073863499257620673 69882434305397624443215505)
    ·
      refine ⟨52411825729048218332411629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69882434305397624443215505 52411825729048218332411629)
      ·
        refine ⟨19654434648393081874654361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52411825729048218332411629 19654434648393081874654361)
        ·
          refine ⟨14740825986294811405990771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19654434648393081874654361 14740825986294811405990771)
          ·
            refine ⟨22111238979442217108986157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14740825986294811405990771 22111238979442217108986157)
            ·
              refine ⟨8291714617290831415869809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22111238979442217108986157 8291714617290831415869809)
              ·
                refine ⟨6218785962968123561902357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8291714617290831415869809 6218785962968123561902357)
                ·
                  refine ⟨291505592014130791964173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6218785962968123561902357 291505592014130791964173)
                  ·
                    rfl

theorem cell22_2554673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_2554673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554673 prefixEnd_2554673 := by exact prefixLift 2554673
  have htrace : WordTrace (prefixWord ++ tailWord_2554673) baseStart_2554673 baseEnd_2554673 := by
    simpa [prefixWord, tailWord_2554673, baseEnd_2554673] using wordTrace_append hprefix tailTrace_2554673
  have hstable : (prefixWord ++ tailWord_2554673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554673).length < 2 ^ (prefixWord ++ tailWord_2554673).sum := by decide
  have hdescent : baseEnd_2554673 < baseStart_2554673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554733 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2554733 : Nat := 118140960795 + 2554733 * 2 ^ 59
def prefixEnd_2554733 : Nat := 4983230072969 + 3 ^ 40 * 2554733 * 2
def baseEnd_2554733 : Nat := 874537315268572219392335

theorem tailTrace_2554733 : CollatzResearch.WordTrace tailWord_2554733 prefixEnd_2554733 874537315268572219392335 := by
  unfold tailWord_2554733
  simp only [CollatzResearch.WordTrace]
  refine ⟨93178767453646129504804853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62119178302430753003203235 93178767453646129504804853)
  ·
    refine ⟨8735509448779324641075455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93178767453646129504804853 8735509448779324641075455)
    ·
      refine ⟨13103264173168986961613183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8735509448779324641075455 13103264173168986961613183)
      ·
        refine ⟨19654896259753480442419775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13103264173168986961613183 19654896259753480442419775)
        ·
          refine ⟨29482344389630220663629663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19654896259753480442419775 29482344389630220663629663)
          ·
            refine ⟨44223516584445330995444495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29482344389630220663629663 44223516584445330995444495)
            ·
              refine ⟨66335274876667996493166743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44223516584445330995444495 66335274876667996493166743)
              ·
                refine ⟨99502912315001994739750115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66335274876667996493166743 99502912315001994739750115)
                ·
                  refine ⟨149254368472502992109625173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99502912315001994739750115 149254368472502992109625173)
                  ·
                    refine ⟨874537315268572219392335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 149254368472502992109625173 874537315268572219392335)
                    ·
                      rfl

theorem cell22_2554733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2554733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554733 prefixEnd_2554733 := by exact prefixLift 2554733
  have htrace : WordTrace (prefixWord ++ tailWord_2554733) baseStart_2554733 baseEnd_2554733 := by
    simpa [prefixWord, tailWord_2554733, baseEnd_2554733] using wordTrace_append hprefix tailTrace_2554733
  have hstable : (prefixWord ++ tailWord_2554733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554733).length < 2 ^ (prefixWord ++ tailWord_2554733).sum := by decide
  have hdescent : baseEnd_2554733 < baseStart_2554733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554763 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 7]
def baseStart_2554763 : Nat := 118140960795 + 2554763 * 2 ^ 59
def prefixEnd_2554763 : Nat := 4983230072969 + 3 ^ 40 * 2554763 * 2
def baseEnd_2554763 : Nat := 291515861627220713714081

theorem tailTrace_2554763 : CollatzResearch.WordTrace tailWord_2554763 prefixEnd_2554763 291515861627220713714081 := by
  unfold tailWord_2554763
  simp only [CollatzResearch.WordTrace]
  refine ⟨93179861643537444628396943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62119907762358296418931295 93179861643537444628396943)
  ·
    refine ⟨139769792465306166942595415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93179861643537444628396943 139769792465306166942595415)
    ·
      refine ⟨209654688697959250413893123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139769792465306166942595415 209654688697959250413893123)
      ·
        refine ⟨314482033046938875620839685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209654688697959250413893123 314482033046938875620839685)
        ·
          refine ⟨58965381196301039178907441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314482033046938875620839685 58965381196301039178907441)
          ·
            refine ⟨44224035897225779384180581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58965381196301039178907441 44224035897225779384180581)
            ·
              refine ⟨8292006730729833634533859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44224035897225779384180581 8292006730729833634533859)
              ·
                refine ⟨12438010096094750451800789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8292006730729833634533859 12438010096094750451800789)
                ·
                  refine ⟨291515861627220713714081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438010096094750451800789 291515861627220713714081)
                  ·
                    rfl

theorem cell22_2554763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_2554763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554763 prefixEnd_2554763 := by exact prefixLift 2554763
  have htrace : WordTrace (prefixWord ++ tailWord_2554763) baseStart_2554763 baseEnd_2554763 := by
    simpa [prefixWord, tailWord_2554763, baseEnd_2554763] using wordTrace_append hprefix tailTrace_2554763
  have hstable : (prefixWord ++ tailWord_2554763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554763).length < 2 ^ (prefixWord ++ tailWord_2554763).sum := by decide
  have hdescent : baseEnd_2554763 < baseStart_2554763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554840 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_2554840 : Nat := 118140960795 + 2554840 * 2 ^ 59
def prefixEnd_2554840 : Nat := 4983230072969 + 3 ^ 40 * 2554840 * 2
def baseEnd_2554840 : Nat := 874573943555259606967007

theorem tailTrace_2554840 : CollatzResearch.WordTrace tailWord_2554840 prefixEnd_2554840 874573943555259606967007 := by
  unfold tailWord_2554840
  simp only [CollatzResearch.WordTrace]
  refine ⟨46591335032129243389474987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62121780042838991185966649 46591335032129243389474987)
  ·
    refine ⟨69887002548193865084212481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46591335032129243389474987 69887002548193865084212481)
    ·
      refine ⟨52415251911145398813159361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69887002548193865084212481 52415251911145398813159361)
      ·
        refine ⟨39311438933359049109869521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52415251911145398813159361 39311438933359049109869521)
        ·
          refine ⟨29483579200019286832402141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39311438933359049109869521 29483579200019286832402141)
          ·
            refine ⟨11056342200007232562150803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29483579200019286832402141 11056342200007232562150803)
            ·
              refine ⟨16584513300010848843226205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056342200007232562150803 16584513300010848843226205)
              ·
                refine ⟨6219192487504068316209827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16584513300010848843226205 6219192487504068316209827)
                ·
                  refine ⟨9328788731256102474314741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219192487504068316209827 9328788731256102474314741)
                  ·
                    refine ⟨874573943555259606967007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9328788731256102474314741 874573943555259606967007)
                    ·
                      rfl

theorem cell22_2554840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_2554840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554840 prefixEnd_2554840 := by exact prefixLift 2554840
  have htrace : WordTrace (prefixWord ++ tailWord_2554840) baseStart_2554840 baseEnd_2554840 := by
    simpa [prefixWord, tailWord_2554840, baseEnd_2554840] using wordTrace_append hprefix tailTrace_2554840
  have hstable : (prefixWord ++ tailWord_2554840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554840).length < 2 ^ (prefixWord ++ tailWord_2554840).sum := by decide
  have hdescent : baseEnd_2554840 < baseStart_2554840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554915 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 7]
def baseStart_2554915 : Nat := 118140960795 + 2554915 * 2 ^ 59
def prefixEnd_2554915 : Nat := 4983230072969 + 3 ^ 40 * 2554915 * 2
def baseEnd_2554915 : Nat := 291533205862661470447259

theorem tailTrace_2554915 : CollatzResearch.WordTrace tailWord_2554915 prefixEnd_2554915 291533205862661470447259 := by
  unfold tailWord_2554915
  simp only [CollatzResearch.WordTrace]
  refine ⟨93185405538986774587930199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62123603692657849725286799 93185405538986774587930199)
  ·
    refine ⟨139778108308480161881895299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93185405538986774587930199 139778108308480161881895299)
    ·
      refine ⟨209667162462720242822842949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139778108308480161881895299 209667162462720242822842949)
      ·
        refine ⟨39312592961760045529283053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209667162462720242822842949 39312592961760045529283053)
        ·
          refine ⟨14742222360660017073481145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39312592961760045529283053 14742222360660017073481145)
          ·
            refine ⟨11056666770495012805110859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14742222360660017073481145 11056666770495012805110859)
            ·
              refine ⟨16585000155742519207666289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056666770495012805110859 16585000155742519207666289)
              ·
                refine ⟨12438750116806889405749717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16585000155742519207666289 12438750116806889405749717)
                ·
                  refine ⟨291533205862661470447259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438750116806889405749717 291533205862661470447259)
                  ·
                    rfl

theorem cell22_2554915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_2554915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554915 prefixEnd_2554915 := by exact prefixLift 2554915
  have htrace : WordTrace (prefixWord ++ tailWord_2554915) baseStart_2554915 baseEnd_2554915 := by
    simpa [prefixWord, tailWord_2554915, baseEnd_2554915] using wordTrace_append hprefix tailTrace_2554915
  have hstable : (prefixWord ++ tailWord_2554915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554915).length < 2 ^ (prefixWord ++ tailWord_2554915).sum := by decide
  have hdescent : baseEnd_2554915 < baseStart_2554915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554960 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_2554960 : Nat := 118140960795 + 2554960 * 2 ^ 59
def prefixEnd_2554960 : Nat := 4983230072969 + 3 ^ 40 * 2554960 * 2
def baseEnd_2554960 : Nat := 291538340669206431322213

theorem tailTrace_2554960 : CollatzResearch.WordTrace tailWord_2554960 prefixEnd_2554960 291538340669206431322213 := by
  unfold tailWord_2554960
  simp only [CollatzResearch.WordTrace]
  refine ⟨46593523411911873636659167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62124697882549164848878889 46593523411911873636659167)
  ·
    refine ⟨69890285117867810454988751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46593523411911873636659167 69890285117867810454988751)
    ·
      refine ⟨104835427676801715682483127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69890285117867810454988751 104835427676801715682483127)
      ·
        refine ⟨157253141515202573523724691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104835427676801715682483127 157253141515202573523724691)
        ·
          refine ⟨235879712272803860285587037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157253141515202573523724691 235879712272803860285587037)
          ·
            refine ⟨88454892102301447607095139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235879712272803860285587037 88454892102301447607095139)
            ·
              refine ⟨132682338153452171410642709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88454892102301447607095139 132682338153452171410642709)
              ·
                refine ⟨6219484600943070534873877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132682338153452171410642709 6219484600943070534873877)
                ·
                  refine ⟨291538340669206431322213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6219484600943070534873877 291538340669206431322213)
                  ·
                    rfl

theorem cell22_2554960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_2554960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554960 prefixEnd_2554960 := by exact prefixLift 2554960
  have htrace : WordTrace (prefixWord ++ tailWord_2554960) baseStart_2554960 baseEnd_2554960 := by
    simpa [prefixWord, tailWord_2554960, baseEnd_2554960] using wordTrace_append hprefix tailTrace_2554960
  have hstable : (prefixWord ++ tailWord_2554960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554960).length < 2 ^ (prefixWord ++ tailWord_2554960).sum := by decide
  have hdescent : baseEnd_2554960 < baseStart_2554960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554994 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_2554994 : Nat := 118140960795 + 2554994 * 2 ^ 59
def prefixEnd_2554994 : Nat := 4983230072969 + 3 ^ 40 * 2554994 * 2
def baseEnd_2554994 : Nat := 291542220300818179538845

theorem tailTrace_2554994 : CollatzResearch.WordTrace tailWord_2554994 prefixEnd_2554994 291542220300818179538845 := by
  unfold tailWord_2554994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23297071726425142770014009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62125524603800380720037357 23297071726425142770014009)
  ·
    refine ⟨17472803794818857077510507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23297071726425142770014009 17472803794818857077510507)
    ·
      refine ⟨26209205692228285616265761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17472803794818857077510507 26209205692228285616265761)
      ·
        refine ⟨19656904269171214212199321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26209205692228285616265761 19656904269171214212199321)
        ·
          refine ⟨14742678201878410659149491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19656904269171214212199321 14742678201878410659149491)
          ·
            refine ⟨22114017302817615988724237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14742678201878410659149491 22114017302817615988724237)
            ·
              refine ⟨8292756488556605995771589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22114017302817615988724237 8292756488556605995771589)
              ·
                refine ⟨1554891841604363624207173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8292756488556605995771589 1554891841604363624207173)
                ·
                  refine ⟨291542220300818179538845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554891841604363624207173 291542220300818179538845)
                  ·
                    rfl

theorem cell22_2554994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_2554994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2554994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2554994 prefixEnd_2554994 := by exact prefixLift 2554994
  have htrace : WordTrace (prefixWord ++ tailWord_2554994) baseStart_2554994 baseEnd_2554994 := by
    simpa [prefixWord, tailWord_2554994, baseEnd_2554994] using wordTrace_append hprefix tailTrace_2554994
  have hstable : (prefixWord ++ tailWord_2554994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554994).length < 2 ^ (prefixWord ++ tailWord_2554994).sum := by decide
  have hdescent : baseEnd_2554994 < baseStart_2554994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555009 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2555009 : Nat := 118140960795 + 2555009 * 2 ^ 59
def prefixEnd_2555009 : Nat := 4983230072969 + 3 ^ 40 * 2555009 * 2
def baseEnd_2555009 : Nat := 874631795708999499491489

theorem tailTrace_2555009 : CollatzResearch.WordTrace tailWord_2555009 prefixEnd_2555009 874631795708999499491489 := by
  unfold tailWord_2555009
  simp only [CollatzResearch.WordTrace]
  refine ⟨93188834000646228641852081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62125889333764152427901387 93188834000646228641852081)
  ·
    refine ⟨69891625500484671481389061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93188834000646228641852081 69891625500484671481389061)
    ·
      refine ⟨13104679781340875902760449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69891625500484671481389061 13104679781340875902760449)
      ·
        refine ⟨9828509836005656927070337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13104679781340875902760449 9828509836005656927070337)
        ·
          refine ⟨7371382377004242695302753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9828509836005656927070337 7371382377004242695302753)
          ·
            refine ⟨5528536782753182021477065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7371382377004242695302753 5528536782753182021477065)
            ·
              refine ⟨4146402587064886516107799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528536782753182021477065 4146402587064886516107799)
              ·
                refine ⟨6219603880597329774161699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146402587064886516107799 6219603880597329774161699)
                ·
                  refine ⟨9329405820895994661242549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219603880597329774161699 9329405820895994661242549)
                  ·
                    refine ⟨874631795708999499491489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9329405820895994661242549 874631795708999499491489)
                    ·
                      rfl

theorem cell22_2555009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2555009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555009 prefixEnd_2555009 := by exact prefixLift 2555009
  have htrace : WordTrace (prefixWord ++ tailWord_2555009) baseStart_2555009 baseEnd_2555009 := by
    simpa [prefixWord, tailWord_2555009, baseEnd_2555009] using wordTrace_append hprefix tailTrace_2555009
  have hstable : (prefixWord ++ tailWord_2555009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555009).length < 2 ^ (prefixWord ++ tailWord_2555009).sum := by decide
  have hdescent : baseEnd_2555009 < baseStart_2555009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555035 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_2555035 : Nat := 118140960795 + 2555035 * 2 ^ 59
def prefixEnd_2555035 : Nat := 4983230072969 + 3 ^ 40 * 2555035 * 2
def baseEnd_2555035 : Nat := 874640696040344098341409

theorem tailTrace_2555035 : CollatzResearch.WordTrace tailWord_2555035 prefixEnd_2555035 874640696040344098341409 := by
  unfold tailWord_2555035
  simp only [CollatzResearch.WordTrace]
  refine ⟨93189782298552035082298559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62126521532368023388199039 93189782298552035082298559)
  ·
    refine ⟨139784673447828052623447839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93189782298552035082298559 139784673447828052623447839)
    ·
      refine ⟨209677010171742078935171759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139784673447828052623447839 209677010171742078935171759)
      ·
        refine ⟨314515515257613118402757639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209677010171742078935171759 314515515257613118402757639)
        ·
          refine ⟨471773272886419677604136459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314515515257613118402757639 471773272886419677604136459)
          ·
            refine ⟨707659909329629516406204689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471773272886419677604136459 707659909329629516406204689)
            ·
              refine ⟨530744931997222137304653517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707659909329629516406204689 530744931997222137304653517)
              ·
                refine ⟨199029349498958301489245069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530744931997222137304653517 199029349498958301489245069)
                ·
                  refine ⟨74636006062109363058466901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199029349498958301489245069 74636006062109363058466901)
                  ·
                    refine ⟨874640696040344098341409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74636006062109363058466901 874640696040344098341409)
                    ·
                      rfl

theorem cell22_2555035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_2555035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555035 prefixEnd_2555035 := by exact prefixLift 2555035
  have htrace : WordTrace (prefixWord ++ tailWord_2555035) baseStart_2555035 baseEnd_2555035 := by
    simpa [prefixWord, tailWord_2555035, baseEnd_2555035] using wordTrace_append hprefix tailTrace_2555035
  have hstable : (prefixWord ++ tailWord_2555035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555035).length < 2 ^ (prefixWord ++ tailWord_2555035).sum := by decide
  have hdescent : baseEnd_2555035 < baseStart_2555035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555097 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_2555097 : Nat := 118140960795 + 2555097 * 2 ^ 59
def prefixEnd_2555097 : Nat := 4983230072969 + 3 ^ 40 * 2555097 * 2
def baseEnd_2555097 : Nat := 874661919907396603291219

theorem tailTrace_2555097 : CollatzResearch.WordTrace tailWord_2555097 prefixEnd_2555097 874661919907396603291219 := by
  unfold tailWord_2555097
  simp only [CollatzResearch.WordTrace]
  refine ⟨93192043624327419671055545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62128029082884946447370363 93192043624327419671055545)
  ·
    refine ⟨69894032718245564753291659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93192043624327419671055545 69894032718245564753291659)
    ·
      refine ⟨104841049077368347129937489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69894032718245564753291659 104841049077368347129937489)
      ·
        refine ⟨78630786808026260347453117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104841049077368347129937489 78630786808026260347453117)
        ·
          refine ⟨29486545053009847630294919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78630786808026260347453117 29486545053009847630294919)
          ·
            refine ⟨44229817579514771445442379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29486545053009847630294919 44229817579514771445442379)
            ·
              refine ⟨66344726369272157168163569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44229817579514771445442379 66344726369272157168163569)
              ·
                refine ⟨49758544776954117876122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66344726369272157168163569 49758544776954117876122677)
                ·
                  refine ⟨4664863572839448550886501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49758544776954117876122677 4664863572839448550886501)
                  ·
                    refine ⟨874661919907396603291219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664863572839448550886501 874661919907396603291219)
                    ·
                      rfl

theorem cell22_2555097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_2555097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555097 prefixEnd_2555097 := by exact prefixLift 2555097
  have htrace : WordTrace (prefixWord ++ tailWord_2555097) baseStart_2555097 baseEnd_2555097 := by
    simpa [prefixWord, tailWord_2555097, baseEnd_2555097] using wordTrace_append hprefix tailTrace_2555097
  have hstable : (prefixWord ++ tailWord_2555097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555097).length < 2 ^ (prefixWord ++ tailWord_2555097).sum := by decide
  have hdescent : baseEnd_2555097 < baseStart_2555097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555159 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2555159 : Nat := 118140960795 + 2555159 * 2 ^ 59
def prefixEnd_2555159 : Nat := 4983230072969 + 3 ^ 40 * 2555159 * 2
def baseEnd_2555159 : Nat := 874683143774449108241029

theorem tailTrace_2555159 : CollatzResearch.WordTrace tailWord_2555159 prefixEnd_2555159 874683143774449108241029 := by
  unfold tailWord_2555159
  simp only [CollatzResearch.WordTrace]
  refine ⟨93194304950102804259812531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62129536633401869506541687 93194304950102804259812531)
  ·
    refine ⟨139791457425154206389718797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93194304950102804259812531 139791457425154206389718797)
    ·
      refine ⟨52421796534432827396144549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139791457425154206389718797 52421796534432827396144549)
      ·
        refine ⟨9829086850206155136777103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52421796534432827396144549 9829086850206155136777103)
        ·
          refine ⟨14743630275309232705165655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829086850206155136777103 14743630275309232705165655)
          ·
            refine ⟨22115445412963849057748483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14743630275309232705165655 22115445412963849057748483)
            ·
              refine ⟨33173168119445773586622725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22115445412963849057748483 33173168119445773586622725)
              ·
                refine ⟨6219969022396082547491761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33173168119445773586622725 6219969022396082547491761)
                ·
                  refine ⟨4664976766797061910618821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219969022396082547491761 4664976766797061910618821)
                  ·
                    refine ⟨874683143774449108241029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4664976766797061910618821 874683143774449108241029)
                    ·
                      rfl

theorem cell22_2555159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2555159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555159 prefixEnd_2555159 := by exact prefixLift 2555159
  have htrace : WordTrace (prefixWord ++ tailWord_2555159) baseStart_2555159 baseEnd_2555159 := by
    simpa [prefixWord, tailWord_2555159, baseEnd_2555159] using wordTrace_append hprefix tailTrace_2555159
  have hstable : (prefixWord ++ tailWord_2555159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555159).length < 2 ^ (prefixWord ++ tailWord_2555159).sum := by decide
  have hdescent : baseEnd_2555159 < baseStart_2555159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555178 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2555178 : Nat := 118140960795 + 2555178 * 2 ^ 59
def prefixEnd_2555178 : Nat := 4983230072969 + 3 ^ 40 * 2555178 * 2
def baseEnd_2555178 : Nat := 874689647862739392015971

theorem tailTrace_2555178 : CollatzResearch.WordTrace tailWord_2555178 prefixEnd_2555178 874689647862739392015971 := by
  unfold tailWord_2555178
  simp only [CollatzResearch.WordTrace]
  refine ⟨23298749484258492626188547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62129998624689313669836125 23298749484258492626188547)
  ·
    refine ⟨34948124226387738939282821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23298749484258492626188547 34948124226387738939282821)
    ·
      refine ⟨6552773292447701051115529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34948124226387738939282821 6552773292447701051115529)
      ·
        refine ⟨4914579969335775788336647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6552773292447701051115529 4914579969335775788336647)
        ·
          refine ⟨7371869954003663682504971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914579969335775788336647 7371869954003663682504971)
          ·
            refine ⟨11057804931005495523757457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371869954003663682504971 11057804931005495523757457)
            ·
              refine ⟨8293353698254121642818093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11057804931005495523757457 8293353698254121642818093)
              ·
                refine ⟨3110007636845295616056785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8293353698254121642818093 3110007636845295616056785)
                ·
                  refine ⟨2332505727633971712042589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110007636845295616056785 2332505727633971712042589)
                  ·
                    refine ⟨874689647862739392015971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2332505727633971712042589 874689647862739392015971)
                    ·
                      rfl

theorem cell22_2555178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2555178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555178 prefixEnd_2555178 := by exact prefixLift 2555178
  have htrace : WordTrace (prefixWord ++ tailWord_2555178) baseStart_2555178 baseEnd_2555178 := by
    simpa [prefixWord, tailWord_2555178, baseEnd_2555178] using wordTrace_append hprefix tailTrace_2555178
  have hstable : (prefixWord ++ tailWord_2555178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555178).length < 2 ^ (prefixWord ++ tailWord_2555178).sum := by decide
  have hdescent : baseEnd_2555178 < baseStart_2555178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555193 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_2555193 : Nat := 118140960795 + 2555193 * 2 ^ 59
def prefixEnd_2555193 : Nat := 4983230072969 + 3 ^ 40 * 2555193 * 2
def baseEnd_2555193 : Nat := 874694782669284352890925

theorem tailTrace_2555193 : CollatzResearch.WordTrace tailWord_2555193 prefixEnd_2555193 874694782669284352890925 := by
  unfold tailWord_2555193
  simp only [CollatzResearch.WordTrace]
  refine ⟨93195545031979628066550233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62130363354653085377700155 93195545031979628066550233)
  ·
    refine ⟨69896658773984721049912675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93195545031979628066550233 69896658773984721049912675)
    ·
      refine ⟨104844988160977081574869013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69896658773984721049912675 104844988160977081574869013)
      ·
        refine ⟨4914608820045800698821985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104844988160977081574869013 4914608820045800698821985)
        ·
          refine ⟨3685956615034350524116489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4914608820045800698821985 3685956615034350524116489)
          ·
            refine ⟨2764467461275762893087367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3685956615034350524116489 2764467461275762893087367)
            ·
              refine ⟨4146701191913644339631051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764467461275762893087367 4146701191913644339631051)
              ·
                refine ⟨6220051787870466509446577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146701191913644339631051 6220051787870466509446577)
                ·
                  refine ⟨4665038840902849882084933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6220051787870466509446577 4665038840902849882084933)
                  ·
                    refine ⟨874694782669284352890925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665038840902849882084933 874694782669284352890925)
                    ·
                      rfl

theorem cell22_2555193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_2555193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555193 prefixEnd_2555193 := by exact prefixLift 2555193
  have htrace : WordTrace (prefixWord ++ tailWord_2555193) baseStart_2555193 baseEnd_2555193 := by
    simpa [prefixWord, tailWord_2555193, baseEnd_2555193] using wordTrace_append hprefix tailTrace_2555193
  have hstable : (prefixWord ++ tailWord_2555193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555193).length < 2 ^ (prefixWord ++ tailWord_2555193).sum := by decide
  have hdescent : baseEnd_2555193 < baseStart_2555193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555223 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 1, 3]
def baseStart_2555223 : Nat := 118140960795 + 2555223 * 2 ^ 59
def prefixEnd_2555223 : Nat := 4983230072969 + 3 ^ 40 * 2555223 * 2
def baseEnd_2555223 : Nat := 874705052282374274640833

theorem tailTrace_2555223 : CollatzResearch.WordTrace tailWord_2555223 prefixEnd_2555223 874705052282374274640833 := by
  unfold tailWord_2555223
  simp only [CollatzResearch.WordTrace]
  refine ⟨93196639221870943190142323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62131092814580628793428215 93196639221870943190142323)
  ·
    refine ⟨139794958832806414785213485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93196639221870943190142323 139794958832806414785213485)
    ·
      refine ⟨52423109562302405544455057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139794958832806414785213485 52423109562302405544455057)
      ·
        refine ⟨39317332171726804158341293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52423109562302405544455057 39317332171726804158341293)
        ·
          refine ⟨14743999564397551559377985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39317332171726804158341293 14743999564397551559377985)
          ·
            refine ⟨11057999673298163669533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14743999564397551559377985 11057999673298163669533489)
            ·
              refine ⟨8293499754973622752150117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11057999673298163669533489 8293499754973622752150117)
              ·
                refine ⟨1555031204057554266028147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8293499754973622752150117 1555031204057554266028147)
                ·
                  refine ⟨2332546806086331399042221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555031204057554266028147 2332546806086331399042221)
                  ·
                    refine ⟨874705052282374274640833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2332546806086331399042221 874705052282374274640833)
                    ·
                      rfl

theorem cell22_2555223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_2555223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555223 prefixEnd_2555223 := by exact prefixLift 2555223
  have htrace : WordTrace (prefixWord ++ tailWord_2555223) baseStart_2555223 baseEnd_2555223 := by
    simpa [prefixWord, tailWord_2555223, baseEnd_2555223] using wordTrace_append hprefix tailTrace_2555223
  have hstable : (prefixWord ++ tailWord_2555223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555223).length < 2 ^ (prefixWord ++ tailWord_2555223).sum := by decide
  have hdescent : baseEnd_2555223 < baseStart_2555223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555229 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2555229 : Nat := 118140960795 + 2555229 * 2 ^ 59
def prefixEnd_2555229 : Nat := 4983230072969 + 3 ^ 40 * 2555229 * 2
def baseEnd_2555229 : Nat := 874707106204992258990815

theorem tailTrace_2555229 : CollatzResearch.WordTrace tailWord_2555229 prefixEnd_2555229 874707106204992258990815 := by
  unfold tailWord_2555229
  simp only [CollatzResearch.WordTrace]
  refine ⟨93196858059849206214860741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62131238706566137476573827 93196858059849206214860741)
  ·
    refine ⟨17474410886221726165286389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93196858059849206214860741 17474410886221726165286389)
    ·
      refine ⟨1638226020583286827995599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17474410886221726165286389 1638226020583286827995599)
      ·
        refine ⟨2457339030874930241993399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638226020583286827995599 2457339030874930241993399)
        ·
          refine ⟨3686008546312395362990099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457339030874930241993399 3686008546312395362990099)
          ·
            refine ⟨5529012819468593044485149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686008546312395362990099 5529012819468593044485149)
            ·
              refine ⟨2073379807300722391681931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5529012819468593044485149 2073379807300722391681931)
              ·
                refine ⟨3110069710951083587522897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073379807300722391681931 3110069710951083587522897)
                ·
                  refine ⟨2332552283213312690642173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110069710951083587522897 2332552283213312690642173)
                  ·
                    refine ⟨874707106204992258990815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2332552283213312690642173 874707106204992258990815)
                    ·
                      rfl

theorem cell22_2555229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2555229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555229 prefixEnd_2555229 := by exact prefixLift 2555229
  have htrace : WordTrace (prefixWord ++ tailWord_2555229) baseStart_2555229 baseEnd_2555229 := by
    simpa [prefixWord, tailWord_2555229, baseEnd_2555229] using wordTrace_append hprefix tailTrace_2555229
  have hstable : (prefixWord ++ tailWord_2555229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555229).length < 2 ^ (prefixWord ++ tailWord_2555229).sum := by decide
  have hdescent : baseEnd_2555229 < baseStart_2555229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555249 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2555249 : Nat := 118140960795 + 2555249 * 2 ^ 59
def prefixEnd_2555249 : Nat := 4983230072969 + 3 ^ 40 * 2555249 * 2
def baseEnd_2555249 : Nat := 874713952613718873490753

theorem tailTrace_2555249 : CollatzResearch.WordTrace tailWord_2555249 prefixEnd_2555249 874713952613718873490753 := by
  unfold tailWord_2555249
  simp only [CollatzResearch.WordTrace]
  refine ⟨93197587519776749630588801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62131725013184499753725867 93197587519776749630588801)
  ·
    refine ⟨69898190639832562222941601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93197587519776749630588801 69898190639832562222941601)
    ·
      refine ⟨52423642979874421667206201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69898190639832562222941601 52423642979874421667206201)
      ·
        refine ⟨39317732234905816250404651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52423642979874421667206201 39317732234905816250404651)
        ·
          refine ⟨58976598352358724375606977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39317732234905816250404651 58976598352358724375606977)
          ·
            refine ⟨44232448764269043281705233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58976598352358724375606977 44232448764269043281705233)
            ·
              refine ⟨33174336573201782461278925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44232448764269043281705233 33174336573201782461278925)
              ·
                refine ⟨12440376214950668422979597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33174336573201782461278925 12440376214950668422979597)
                ·
                  refine ⟨4665141080606500658617349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12440376214950668422979597 4665141080606500658617349)
                  ·
                    refine ⟨874713952613718873490753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665141080606500658617349 874713952613718873490753)
                    ·
                      rfl

theorem cell22_2555249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2555249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555249 prefixEnd_2555249 := by exact prefixLift 2555249
  have htrace : WordTrace (prefixWord ++ tailWord_2555249) baseStart_2555249 baseEnd_2555249 := by
    simpa [prefixWord, tailWord_2555249, baseEnd_2555249] using wordTrace_append hprefix tailTrace_2555249
  have hstable : (prefixWord ++ tailWord_2555249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555249).length < 2 ^ (prefixWord ++ tailWord_2555249).sum := by decide
  have hdescent : baseEnd_2555249 < baseStart_2555249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555332 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_2555332 : Nat := 118140960795 + 2555332 * 2 ^ 59
def prefixEnd_2555332 : Nat := 4983230072969 + 3 ^ 40 * 2555332 * 2
def baseEnd_2555332 : Nat := 291580788403311441221833

theorem tailTrace_2555332 : CollatzResearch.WordTrace tailWord_2555332 prefixEnd_2555332 291580788403311441221833 := by
  unfold tailWord_2555332
  simp only [CollatzResearch.WordTrace]
  refine ⟨46600307389238027402930125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62133743185650703203906833 46600307389238027402930125)
  ·
    refine ⟨17475115270964260276098797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46600307389238027402930125 17475115270964260276098797)
    ·
      refine ⟨6553168226611597603537049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17475115270964260276098797 6553168226611597603537049)
      ·
        refine ⟨4914876169958698202652787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6553168226611597603537049 4914876169958698202652787)
        ·
          refine ⟨7372314254938047303979181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914876169958698202652787 7372314254938047303979181)
          ·
            refine ⟨2764617845601767738992193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7372314254938047303979181 2764617845601767738992193)
            ·
              refine ⟨2073463384201325804244145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2764617845601767738992193 2073463384201325804244145)
              ·
                refine ⟨1555097538150994353183109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073463384201325804244145 1555097538150994353183109)
                ·
                  refine ⟨291580788403311441221833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555097538150994353183109 291580788403311441221833)
                  ·
                    rfl

theorem cell22_2555332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_2555332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555332 prefixEnd_2555332 := by exact prefixLift 2555332
  have htrace : WordTrace (prefixWord ++ tailWord_2555332) baseStart_2555332 baseEnd_2555332 := by
    simpa [prefixWord, tailWord_2555332, baseEnd_2555332] using wordTrace_append hprefix tailTrace_2555332
  have hstable : (prefixWord ++ tailWord_2555332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555332).length < 2 ^ (prefixWord ++ tailWord_2555332).sum := by decide
  have hdescent : baseEnd_2555332 < baseStart_2555332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555339 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_2555339 : Nat := 118140960795 + 2555339 * 2 ^ 59
def prefixEnd_2555339 : Nat := 4983230072969 + 3 ^ 40 * 2555339 * 2
def baseEnd_2555339 : Nat := 874744761452988638740477

theorem tailTrace_2555339 : CollatzResearch.WordTrace tailWord_2555339 prefixEnd_2555339 874744761452988638740477 := by
  unfold tailWord_2555339
  simp only [CollatzResearch.WordTrace]
  refine ⟨93200870089450695001365071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62133913392967130000910047 93200870089450695001365071)
  ·
    refine ⟨139801305134176042502047607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93200870089450695001365071 139801305134176042502047607)
    ·
      refine ⟨209701957701264063753071411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139801305134176042502047607 209701957701264063753071411)
      ·
        refine ⟨314552936551896095629607117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209701957701264063753071411 314552936551896095629607117)
        ·
          refine ⟨117957351206961035861102669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314552936551896095629607117 117957351206961035861102669)
          ·
            refine ⟨44234006702610388447913501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117957351206961035861102669 44234006702610388447913501)
            ·
              refine ⟨16587752513478895667967563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44234006702610388447913501 16587752513478895667967563)
              ·
                refine ⟨24881628770218343501951345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16587752513478895667967563 24881628770218343501951345)
                ·
                  refine ⟨18661221577663757626463509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24881628770218343501951345 18661221577663757626463509)
                  ·
                    refine ⟨874744761452988638740477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18661221577663757626463509 874744761452988638740477)
                    ·
                      rfl

theorem cell22_2555339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_2555339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555339 prefixEnd_2555339 := by exact prefixLift 2555339
  have htrace : WordTrace (prefixWord ++ tailWord_2555339) baseStart_2555339 baseEnd_2555339 := by
    simpa [prefixWord, tailWord_2555339, baseEnd_2555339] using wordTrace_append hprefix tailTrace_2555339
  have hstable : (prefixWord ++ tailWord_2555339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555339).length < 2 ^ (prefixWord ++ tailWord_2555339).sum := by decide
  have hdescent : baseEnd_2555339 < baseStart_2555339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555448 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_2555448 : Nat := 118140960795 + 2555448 * 2 ^ 59
def prefixEnd_2555448 : Nat := 4983230072969 + 3 ^ 40 * 2555448 * 2
def baseEnd_2555448 : Nat := 874782074380548687765143

theorem tailTrace_2555448 : CollatzResearch.WordTrace tailWord_2555448 prefixEnd_2555448 874782074380548687765143 := by
  unfold tailWord_2555448
  simp only [CollatzResearch.WordTrace]
  refine ⟨46602422823027903308541499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62136563764037204411388665 46602422823027903308541499)
  ·
    refine ⟨69903634234541854962812249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46602422823027903308541499 69903634234541854962812249)
    ·
      refine ⟨52427725675906391222109187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69903634234541854962812249 52427725675906391222109187)
      ·
        refine ⟨78641588513859586833163781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52427725675906391222109187 78641588513859586833163781)
        ·
          refine ⟨14745297846348672531218209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78641588513859586833163781 14745297846348672531218209)
          ·
            refine ⟨11058973384761504398413657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14745297846348672531218209 11058973384761504398413657)
            ·
              refine ⟨8294230038571128298810243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11058973384761504398413657 8294230038571128298810243)
              ·
                refine ⟨12441345057856692448215365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294230038571128298810243 12441345057856692448215365)
                ·
                  refine ⟨2332752198348129834040381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12441345057856692448215365 2332752198348129834040381)
                  ·
                    refine ⟨874782074380548687765143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2332752198348129834040381 874782074380548687765143)
                    ·
                      rfl

theorem cell22_2555448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_2555448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555448 prefixEnd_2555448 := by exact prefixLift 2555448
  have htrace : WordTrace (prefixWord ++ tailWord_2555448) baseStart_2555448 baseEnd_2555448 := by
    simpa [prefixWord, tailWord_2555448, baseEnd_2555448] using wordTrace_append hprefix tailTrace_2555448
  have hstable : (prefixWord ++ tailWord_2555448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555448).length < 2 ^ (prefixWord ++ tailWord_2555448).sum := by decide
  have hdescent : baseEnd_2555448 < baseStart_2555448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555450 : List Nat := [3, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_2555450 : Nat := 118140960795 + 2555450 * 2 ^ 59
def prefixEnd_2555450 : Nat := 4983230072969 + 3 ^ 40 * 2555450 * 2
def baseEnd_2555450 : Nat := 291594253007140449738379

theorem tailTrace_2555450 : CollatzResearch.WordTrace tailWord_2555450 prefixEnd_2555450 291594253007140449738379 := by
  unfold tailWord_2555450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301229648012140239663951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62136612394699040639103869 23301229648012140239663951)
  ·
    refine ⟨34951844472018210359495927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23301229648012140239663951 34951844472018210359495927)
    ·
      refine ⟨52427766708027315539243891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34951844472018210359495927 52427766708027315539243891)
      ·
        refine ⟨78641650062040973308865837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52427766708027315539243891 78641650062040973308865837)
        ·
          refine ⟨29490618773265364990824689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78641650062040973308865837 29490618773265364990824689)
          ·
            refine ⟨22117964079949023743118517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29490618773265364990824689 22117964079949023743118517)
            ·
              refine ⟨2073559132495220975917361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22117964079949023743118517 2073559132495220975917361)
              ·
                refine ⟨1555169349371415731938021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073559132495220975917361 1555169349371415731938021)
                ·
                  refine ⟨291594253007140449738379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555169349371415731938021 291594253007140449738379)
                  ·
                    rfl

theorem cell22_2555450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_2555450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555450 prefixEnd_2555450 := by exact prefixLift 2555450
  have htrace : WordTrace (prefixWord ++ tailWord_2555450) baseStart_2555450 baseEnd_2555450 := by
    simpa [prefixWord, tailWord_2555450, baseEnd_2555450] using wordTrace_append hprefix tailTrace_2555450
  have hstable : (prefixWord ++ tailWord_2555450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555450).length < 2 ^ (prefixWord ++ tailWord_2555450).sum := by decide
  have hdescent : baseEnd_2555450 < baseStart_2555450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555461 : List Nat := [1, 3, 1, 1, 1, 4, 4, 7]
def baseStart_2555461 : Nat := 118140960795 + 2555461 * 2 ^ 59
def prefixEnd_2555461 : Nat := 4983230072969 + 3 ^ 40 * 2555461 * 2
def baseEnd_2555461 : Nat := 97198502727357887465567

theorem tailTrace_2555461 : CollatzResearch.WordTrace tailWord_2555461 prefixEnd_2555461 97198502727357887465567 := by
  unfold tailWord_2555461
  simp only [CollatzResearch.WordTrace]
  refine ⟨93205319795008709837306237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62136879863339139891537491 93205319795008709837306237)
  ·
    refine ⟨34951994923128266188989839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93205319795008709837306237 34951994923128266188989839)
    ·
      refine ⟨52427992384692399283484759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34951994923128266188989839 52427992384692399283484759)
      ·
        refine ⟨78641988577038598925227139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52427992384692399283484759 78641988577038598925227139)
        ·
          refine ⟨117962982865557898387840709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78641988577038598925227139 117962982865557898387840709)
          ·
            refine ⟨22118059287292105947720133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117962982865557898387840709 22118059287292105947720133)
            ·
              refine ⟨4147136116367269865197525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22118059287292105947720133 4147136116367269865197525)
              ·
                refine ⟨97198502727357887465567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4147136116367269865197525 97198502727357887465567)
                ·
                  rfl

theorem cell22_2555461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 7].length) (baseStart_2555461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555461 prefixEnd_2555461 := by exact prefixLift 2555461
  have htrace : WordTrace (prefixWord ++ tailWord_2555461) baseStart_2555461 baseEnd_2555461 := by
    simpa [prefixWord, tailWord_2555461, baseEnd_2555461] using wordTrace_append hprefix tailTrace_2555461
  have hstable : (prefixWord ++ tailWord_2555461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555461).length < 2 ^ (prefixWord ++ tailWord_2555461).sum := by decide
  have hdescent : baseEnd_2555461 < baseStart_2555461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555469 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2555469 : Nat := 118140960795 + 2555469 * 2 ^ 59
def prefixEnd_2555469 : Nat := 4983230072969 + 3 ^ 40 * 2555469 * 2
def baseEnd_2555469 : Nat := 874789263109711632990079

theorem tailTrace_2555469 : CollatzResearch.WordTrace tailWord_2555469 prefixEnd_2555469 874789263109711632990079 := by
  unfold tailWord_2555469
  simp only [CollatzResearch.WordTrace]
  refine ⟨93205611578979727203597461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62137074385986484802398307 93205611578979727203597461)
  ·
    refine ⟨4369013042764674712668631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93205611578979727203597461 4369013042764674712668631)
    ·
      refine ⟨6553519564147012069002947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369013042764674712668631 6553519564147012069002947)
      ·
        refine ⟨9830279346220518103504421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553519564147012069002947 9830279346220518103504421)
        ·
          refine ⟨1843177377416347144407079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9830279346220518103504421 1843177377416347144407079)
          ·
            refine ⟨2764766066124520716610619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843177377416347144407079 2764766066124520716610619)
            ·
              refine ⟨4147149099186781074915929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764766066124520716610619 4147149099186781074915929)
              ·
                refine ⟨3110361824390085806186947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147149099186781074915929 3110361824390085806186947)
                ·
                  refine ⟨4665542736585128709280421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110361824390085806186947 4665542736585128709280421)
                  ·
                    refine ⟨874789263109711632990079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665542736585128709280421 874789263109711632990079)
                    ·
                      rfl

theorem cell22_2555469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2555469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555469 prefixEnd_2555469 := by exact prefixLift 2555469
  have htrace : WordTrace (prefixWord ++ tailWord_2555469) baseStart_2555469 baseEnd_2555469 := by
    simpa [prefixWord, tailWord_2555469, baseEnd_2555469] using wordTrace_append hprefix tailTrace_2555469
  have hstable : (prefixWord ++ tailWord_2555469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555469).length < 2 ^ (prefixWord ++ tailWord_2555469).sum := by decide
  have hdescent : baseEnd_2555469 < baseStart_2555469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555574 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2555574 : Nat := 118140960795 + 2555574 * 2 ^ 59
def prefixEnd_2555574 : Nat := 4983230072969 + 3 ^ 40 * 2555574 * 2
def baseEnd_2555574 : Nat := 291608402251842119704919

theorem tailTrace_2555574 : CollatzResearch.WordTrace tailWord_2555574 prefixEnd_2555574 291608402251842119704919 := by
  unfold tailWord_2555574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825590077724958133510611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62139627495732886757446517 5825590077724958133510611)
  ·
    refine ⟨8738385116587437200265917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5825590077724958133510611 8738385116587437200265917)
    ·
      refine ⟨3276894418720288950099719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8738385116587437200265917 3276894418720288950099719)
      ·
        refine ⟨4915341628080433425149579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276894418720288950099719 4915341628080433425149579)
        ·
          refine ⟨7373012442120650137724369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915341628080433425149579 7373012442120650137724369)
          ·
            refine ⟨5529759331590487603293277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7373012442120650137724369 5529759331590487603293277)
            ·
              refine ⟨2073659749346432851234979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5529759331590487603293277 2073659749346432851234979)
              ·
                refine ⟨3110489624019649276852469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073659749346432851234979 3110489624019649276852469)
                ·
                  refine ⟨291608402251842119704919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3110489624019649276852469 291608402251842119704919)
                  ·
                    rfl

theorem cell22_2555574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2555574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555574 prefixEnd_2555574 := by exact prefixLift 2555574
  have htrace : WordTrace (prefixWord ++ tailWord_2555574) baseStart_2555574 baseEnd_2555574 := by
    simpa [prefixWord, tailWord_2555574, baseEnd_2555574] using wordTrace_append hprefix tailTrace_2555574
  have hstable : (prefixWord ++ tailWord_2555574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555574).length < 2 ^ (prefixWord ++ tailWord_2555574).sum := by decide
  have hdescent : baseEnd_2555574 < baseStart_2555574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555598 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2555598 : Nat := 118140960795 + 2555598 * 2 ^ 59
def prefixEnd_2555598 : Nat := 4983230072969 + 3 ^ 40 * 2555598 * 2
def baseEnd_2555598 : Nat := 874833422445998296514683

theorem tailTrace_2555598 : CollatzResearch.WordTrace tailWord_2555598 prefixEnd_2555598 874833422445998296514683 := by
  unfold tailWord_2555598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651289574439047779380431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62140211063674921490028965 11651289574439047779380431)
  ·
    refine ⟨17476934361658571669070647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651289574439047779380431 17476934361658571669070647)
    ·
      refine ⟨26215401542487857503605971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17476934361658571669070647 26215401542487857503605971)
      ·
        refine ⟨39323102313731786255408957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26215401542487857503605971 39323102313731786255408957)
        ·
          refine ⟨14746163367649419845778359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39323102313731786255408957 14746163367649419845778359)
          ·
            refine ⟨22119245051474129768667539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14746163367649419845778359 22119245051474129768667539)
            ·
              refine ⟨33178867577211194653001309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22119245051474129768667539 33178867577211194653001309)
              ·
                refine ⟨12442075341454197994875491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33178867577211194653001309 12442075341454197994875491)
                ·
                  refine ⟨18663113012181296992313237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12442075341454197994875491 18663113012181296992313237)
                  ·
                    refine ⟨874833422445998296514683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18663113012181296992313237 874833422445998296514683)
                    ·
                      rfl

theorem cell22_2555598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2555598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555598 prefixEnd_2555598 := by exact prefixLift 2555598
  have htrace : WordTrace (prefixWord ++ tailWord_2555598) baseStart_2555598 baseEnd_2555598 := by
    simpa [prefixWord, tailWord_2555598, baseEnd_2555598] using wordTrace_append hprefix tailTrace_2555598
  have hstable : (prefixWord ++ tailWord_2555598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555598).length < 2 ^ (prefixWord ++ tailWord_2555598).sum := by decide
  have hdescent : baseEnd_2555598 < baseStart_2555598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555602 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_2555602 : Nat := 118140960795 + 2555602 * 2 ^ 59
def prefixEnd_2555602 : Nat := 4983230072969 + 3 ^ 40 * 2555602 * 2
def baseEnd_2555602 : Nat := 291611597242581206471557

theorem tailTrace_2555602 : CollatzResearch.WordTrace tailWord_2555602 prefixEnd_2555602 291611597242581206471557 := by
  unfold tailWord_2555602
  simp only [CollatzResearch.WordTrace]
  refine ⟨23302615621874472729547265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62140308324998593945459373 23302615621874472729547265)
  ·
    refine ⟨17476961716405854547160449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23302615621874472729547265 17476961716405854547160449)
    ·
      refine ⟨13107721287304390910370337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17476961716405854547160449 13107721287304390910370337)
      ·
        refine ⟨9830790965478293182777753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13107721287304390910370337 9830790965478293182777753)
        ·
          refine ⟨7373093224108719887083315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9830790965478293182777753 7373093224108719887083315)
          ·
            refine ⟨11059639836163079830624973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7373093224108719887083315 11059639836163079830624973)
            ·
              refine ⟨4147364938561154936484365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11059639836163079830624973 4147364938561154936484365)
              ·
                refine ⟨1555261851960433101181637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4147364938561154936484365 1555261851960433101181637)
                ·
                  refine ⟨291611597242581206471557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555261851960433101181637 291611597242581206471557)
                  ·
                    rfl

theorem cell22_2555602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_2555602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555602 prefixEnd_2555602 := by exact prefixLift 2555602
  have htrace : WordTrace (prefixWord ++ tailWord_2555602) baseStart_2555602 baseEnd_2555602 := by
    simpa [prefixWord, tailWord_2555602, baseEnd_2555602] using wordTrace_append hprefix tailTrace_2555602
  have hstable : (prefixWord ++ tailWord_2555602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555602).length < 2 ^ (prefixWord ++ tailWord_2555602).sum := by decide
  have hdescent : baseEnd_2555602 < baseStart_2555602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555619 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 4]
def baseStart_2555619 : Nat := 118140960795 + 2555619 * 2 ^ 59
def prefixEnd_2555619 : Nat := 4983230072969 + 3 ^ 40 * 2555619 * 2
def baseEnd_2555619 : Nat := 291613537058387080579873

theorem tailTrace_2555619 : CollatzResearch.WordTrace tailWord_2555619 prefixEnd_2555619 291613537058387080579873 := by
  unfold tailWord_2555619
  simp only [CollatzResearch.WordTrace]
  refine ⟨93211082528436302821557911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62140721685624201881038607 93211082528436302821557911)
  ·
    refine ⟨139816623792654454232336867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93211082528436302821557911 139816623792654454232336867)
    ·
      refine ⟨209724935688981681348505301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139816623792654454232336867 209724935688981681348505301)
      ·
        refine ⟨4915428180210508156605593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 209724935688981681348505301 4915428180210508156605593)
        ·
          refine ⟨3686571135157881117454195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4915428180210508156605593 3686571135157881117454195)
          ·
            refine ⟨5529856702736821676181293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686571135157881117454195 5529856702736821676181293)
            ·
              refine ⟨2073696263526308128567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5529856702736821676181293 2073696263526308128567985)
              ·
                refine ⟨1555272197644731096425989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073696263526308128567985 1555272197644731096425989)
                ·
                  refine ⟨291613537058387080579873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555272197644731096425989 291613537058387080579873)
                  ·
                    rfl

theorem cell22_2555619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 4].length) (baseStart_2555619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555619 prefixEnd_2555619 := by exact prefixLift 2555619
  have htrace : WordTrace (prefixWord ++ tailWord_2555619) baseStart_2555619 baseEnd_2555619 := by
    simpa [prefixWord, tailWord_2555619, baseEnd_2555619] using wordTrace_append hprefix tailTrace_2555619
  have hstable : (prefixWord ++ tailWord_2555619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555619).length < 2 ^ (prefixWord ++ tailWord_2555619).sum := by decide
  have hdescent : baseEnd_2555619 < baseStart_2555619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555668 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2555668 : Nat := 118140960795 + 2555668 * 2 ^ 59
def prefixEnd_2555668 : Nat := 4983230072969 + 3 ^ 40 * 2555668 * 2
def baseEnd_2555668 : Nat := 874857384876541447264469

theorem tailTrace_2555668 : CollatzResearch.WordTrace tailWord_2555668 prefixEnd_2555668 874857384876541447264469 := by
  unfold tailWord_2555668
  simp only [CollatzResearch.WordTrace]
  refine ⟨46606434852629392095045829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62141913136839189460061105 46606434852629392095045829)
  ·
    refine ⟨8738706534868011017821093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46606434852629392095045829 8738706534868011017821093)
    ·
      refine ⟨1638507475287752065841455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8738706534868011017821093 1638507475287752065841455)
      ·
        refine ⟨2457761212931628098762183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638507475287752065841455 2457761212931628098762183)
        ·
          refine ⟨3686641819397442148143275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457761212931628098762183 3686641819397442148143275)
          ·
            refine ⟨5529962729096163222214913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686641819397442148143275 5529962729096163222214913)
            ·
              refine ⟨4147472046822122416661185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5529962729096163222214913 4147472046822122416661185)
              ·
                refine ⟨3110604035116591812495889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147472046822122416661185 3110604035116591812495889)
                ·
                  refine ⟨2332953026337443859371917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110604035116591812495889 2332953026337443859371917)
                  ·
                    refine ⟨874857384876541447264469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2332953026337443859371917 874857384876541447264469)
                    ·
                      rfl

theorem cell22_2555668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2555668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555668 prefixEnd_2555668 := by exact prefixLift 2555668
  have htrace : WordTrace (prefixWord ++ tailWord_2555668) baseStart_2555668 baseEnd_2555668 := by
    simpa [prefixWord, tailWord_2555668, baseEnd_2555668] using wordTrace_append hprefix tailTrace_2555668
  have hstable : (prefixWord ++ tailWord_2555668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555668).length < 2 ^ (prefixWord ++ tailWord_2555668).sum := by decide
  have hdescent : baseEnd_2555668 < baseStart_2555668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555763 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_2555763 : Nat := 118140960795 + 2555763 * 2 ^ 59
def prefixEnd_2555763 : Nat := 4983230072969 + 3 ^ 40 * 2555763 * 2
def baseEnd_2555763 : Nat := 874889905317992866139177

theorem tailTrace_2555763 : CollatzResearch.WordTrace tailWord_2555763 prefixEnd_2555763 874889905317992866139177 := by
  unfold tailWord_2555763
  simp only [CollatzResearch.WordTrace]
  refine ⟨93216334639914615414799943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62144223093276410276533295 93216334639914615414799943)
  ·
    refine ⟨139824501959871923122199915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93216334639914615414799943 139824501959871923122199915)
    ·
      refine ⟨209736752939807884683299873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139824501959871923122199915 209736752939807884683299873)
      ·
        refine ⟨157302564704855913512474905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209736752939807884683299873 157302564704855913512474905)
        ·
          refine ⟨117976923528641935134356179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157302564704855913512474905 117976923528641935134356179)
          ·
            refine ⟨176965385292962902701534269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117976923528641935134356179 176965385292962902701534269)
            ·
              refine ⟨66362019484861088513075351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176965385292962902701534269 66362019484861088513075351)
              ·
                refine ⟨99543029227291632769613027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66362019484861088513075351 99543029227291632769613027)
                ·
                  refine ⟨149314543840937449154419541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99543029227291632769613027 149314543840937449154419541)
                  ·
                    refine ⟨874889905317992866139177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 149314543840937449154419541 874889905317992866139177)
                    ·
                      rfl

theorem cell22_2555763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_2555763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555763 prefixEnd_2555763 := by exact prefixLift 2555763
  have htrace : WordTrace (prefixWord ++ tailWord_2555763) baseStart_2555763 baseEnd_2555763 := by
    simpa [prefixWord, tailWord_2555763, baseEnd_2555763] using wordTrace_append hprefix tailTrace_2555763
  have hstable : (prefixWord ++ tailWord_2555763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555763).length < 2 ^ (prefixWord ++ tailWord_2555763).sum := by decide
  have hdescent : baseEnd_2555763 < baseStart_2555763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555765 : List Nat := [1, 3, 4, 1, 1, 1, 3, 8]
def baseStart_2555765 : Nat := 118140960795 + 2555765 * 2 ^ 59
def prefixEnd_2555765 : Nat := 4983230072969 + 3 ^ 40 * 2555765 * 2
def baseEnd_2555765 : Nat := 97210065550985058621019

theorem tailTrace_2555765 : CollatzResearch.WordTrace tailWord_2555765 prefixEnd_2555765 97210065550985058621019 := by
  unfold tailWord_2555765
  simp only [CollatzResearch.WordTrace]
  refine ⟨93216407585907369756372749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62144271723938246504248499 93216407585907369756372749)
  ·
    refine ⟨34956152844715263658639781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93216407585907369756372749 34956152844715263658639781)
    ·
      refine ⟨6554278658384111935994959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34956152844715263658639781 6554278658384111935994959)
      ·
        refine ⟨9831417987576167903992439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554278658384111935994959 9831417987576167903992439)
        ·
          refine ⟨14747126981364251855988659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9831417987576167903992439 14747126981364251855988659)
          ·
            refine ⟨22120690472046377783982989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14747126981364251855988659 22120690472046377783982989)
            ·
              refine ⟨8295258927017391668993621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22120690472046377783982989 8295258927017391668993621)
              ·
                refine ⟨97210065550985058621019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8295258927017391668993621 97210065550985058621019)
                ·
                  rfl

theorem cell22_2555765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 8].length) (baseStart_2555765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555765 prefixEnd_2555765 := by exact prefixLift 2555765
  have htrace : WordTrace (prefixWord ++ tailWord_2555765) baseStart_2555765 baseEnd_2555765 := by
    simpa [prefixWord, tailWord_2555765, baseEnd_2555765] using wordTrace_append hprefix tailTrace_2555765
  have hstable : (prefixWord ++ tailWord_2555765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555765).length < 2 ^ (prefixWord ++ tailWord_2555765).sum := by decide
  have hdescent : baseEnd_2555765 < baseStart_2555765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555848 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 1, 3]
def baseStart_2555848 : Nat := 118140960795 + 2555848 * 2 ^ 59
def prefixEnd_2555848 : Nat := 4983230072969 + 3 ^ 40 * 2555848 * 2
def baseEnd_2555848 : Nat := 874919002555080977763917

theorem tailTrace_2555848 : CollatzResearch.WordTrace tailWord_2555848 prefixEnd_2555848 874919002555080977763917 := by
  unfold tailWord_2555848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46609717422303337465822099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62146289896404449954429465 46609717422303337465822099)
  ·
    refine ⟨69914576133455006198733149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46609717422303337465822099 69914576133455006198733149)
    ·
      refine ⟨26217966050045627324524931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69914576133455006198733149 26217966050045627324524931)
      ·
        refine ⟨39326949075068440986787397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26217966050045627324524931 39326949075068440986787397)
        ·
          refine ⟨7373802951575332685022637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39326949075068440986787397 7373802951575332685022637)
          ·
            refine ⟨2765176106840749756883489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7373802951575332685022637 2765176106840749756883489)
            ·
              refine ⟨2073882080130562317662617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765176106840749756883489 2073882080130562317662617)
              ·
                refine ⟨1555411560097921738246963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073882080130562317662617 1555411560097921738246963)
                ·
                  refine ⟨2333117340146882607370445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555411560097921738246963 2333117340146882607370445)
                  ·
                    refine ⟨874919002555080977763917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333117340146882607370445 874919002555080977763917)
                    ·
                      rfl

theorem cell22_2555848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_2555848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555848 prefixEnd_2555848 := by exact prefixLift 2555848
  have htrace : WordTrace (prefixWord ++ tailWord_2555848) baseStart_2555848 baseEnd_2555848 := by
    simpa [prefixWord, tailWord_2555848, baseEnd_2555848] using wordTrace_append hprefix tailTrace_2555848
  have hstable : (prefixWord ++ tailWord_2555848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555848).length < 2 ^ (prefixWord ++ tailWord_2555848).sum := by decide
  have hdescent : baseEnd_2555848 < baseStart_2555848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555855 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 6]
def baseStart_2555855 : Nat := 118140960795 + 2555855 * 2 ^ 59
def prefixEnd_2555855 : Nat := 4983230072969 + 3 ^ 40 * 2555855 * 2
def baseEnd_2555855 : Nat := 291640466266045097612965

theorem tailTrace_2555855 : CollatzResearch.WordTrace tailWord_2555855 prefixEnd_2555855 291640466266045097612965 := by
  unfold tailWord_2555855
  simp only [CollatzResearch.WordTrace]
  refine ⟨93219690155581315127149019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62146460103720876751432679 93219690155581315127149019)
  ·
    refine ⟨139829535233371972690723529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93219690155581315127149019 139829535233371972690723529)
    ·
      refine ⟨104872151425028979518042647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139829535233371972690723529 104872151425028979518042647)
      ·
        refine ⟨157308227137543469277063971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104872151425028979518042647 157308227137543469277063971)
        ·
          refine ⟨235962340706315203915595957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157308227137543469277063971 235962340706315203915595957)
          ·
            refine ⟨22121469441217050367087121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235962340706315203915595957 22121469441217050367087121)
            ·
              refine ⟨16591102080912787775315341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22121469441217050367087121 16591102080912787775315341)
              ·
                refine ⟨6221663280342295415743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16591102080912787775315341 6221663280342295415743253)
                ·
                  refine ⟨291640466266045097612965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6221663280342295415743253 291640466266045097612965)
                  ·
                    rfl

theorem cell22_2555855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_2555855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555855 prefixEnd_2555855 := by exact prefixLift 2555855
  have htrace : WordTrace (prefixWord ++ tailWord_2555855) baseStart_2555855 baseEnd_2555855 := by
    simpa [prefixWord, tailWord_2555855, baseEnd_2555855] using wordTrace_append hprefix tailTrace_2555855
  have hstable : (prefixWord ++ tailWord_2555855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555855).length < 2 ^ (prefixWord ++ tailWord_2555855).sum := by decide
  have hdescent : baseEnd_2555855 < baseStart_2555855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555887 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 4, 3]
def baseStart_2555887 : Nat := 118140960795 + 2555887 * 2 ^ 59
def prefixEnd_2555887 : Nat := 4983230072969 + 3 ^ 40 * 2555887 * 2
def baseEnd_2555887 : Nat := 874932353052097876038797

theorem tailTrace_2555887 : CollatzResearch.WordTrace tailWord_2555887 prefixEnd_2555887 874932353052097876038797 := by
  unfold tailWord_2555887
  simp only [CollatzResearch.WordTrace]
  refine ⟨93220857291465384592313915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62147238194310256394875943 93220857291465384592313915)
  ·
    refine ⟨139831285937198076888470873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93220857291465384592313915 139831285937198076888470873)
    ·
      refine ⟨104873464452898557666353155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139831285937198076888470873 104873464452898557666353155)
      ·
        refine ⟨157310196679347836499529733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104873464452898557666353155 157310196679347836499529733)
        ·
          refine ⟨29495661877377719343661825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157310196679347836499529733 29495661877377719343661825)
          ·
            refine ⟨22121746408033289507746369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29495661877377719343661825 22121746408033289507746369)
            ·
              refine ⟨16591309806024967130809777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22121746408033289507746369 16591309806024967130809777)
              ·
                refine ⟨12443482354518725348107333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16591309806024967130809777 12443482354518725348107333)
                ·
                  refine ⟨2333152941472261002770125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12443482354518725348107333 2333152941472261002770125)
                  ·
                    refine ⟨874932353052097876038797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333152941472261002770125 874932353052097876038797)
                    ·
                      rfl

theorem cell22_2555887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_2555887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555887 prefixEnd_2555887 := by exact prefixLift 2555887
  have htrace : WordTrace (prefixWord ++ tailWord_2555887) baseStart_2555887 baseEnd_2555887 := by
    simpa [prefixWord, tailWord_2555887, baseEnd_2555887] using wordTrace_append hprefix tailTrace_2555887
  have hstable : (prefixWord ++ tailWord_2555887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555887).length < 2 ^ (prefixWord ++ tailWord_2555887).sum := by decide
  have hdescent : baseEnd_2555887 < baseStart_2555887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555900 : List Nat := [2, 2, 2, 1, 2, 2, 11]
def baseStart_2555900 : Nat := 118140960795 + 2555900 * 2 ^ 59
def prefixEnd_2555900 : Nat := 4983230072969 + 3 ^ 40 * 2555900 * 2
def baseEnd_2555900 : Nat := 32405066785843339831991

theorem tailTrace_2555900 : CollatzResearch.WordTrace tailWord_2555900 prefixEnd_2555900 32405066785843339831991 := by
  unfold tailWord_2555900
  simp only [CollatzResearch.WordTrace]
  refine ⟨46610665720209143906268577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62147554293612191875024769 46610665720209143906268577)
  ·
    refine ⟨34957999290156857929701433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46610665720209143906268577 34957999290156857929701433)
    ·
      refine ⟨26218499467617643447276075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34957999290156857929701433 26218499467617643447276075)
      ·
        refine ⟨39327749201426465170914113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26218499467617643447276075 39327749201426465170914113)
        ·
          refine ⟨29495811901069848878185585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39327749201426465170914113 29495811901069848878185585)
          ·
            refine ⟨22121858925802386658639189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29495811901069848878185585 22121858925802386658639189)
            ·
              refine ⟨32405066785843339831991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22121858925802386658639189 32405066785843339831991)
              ·
                rfl

theorem cell22_2555900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 11].length) (baseStart_2555900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555900 prefixEnd_2555900 := by exact prefixLift 2555900
  have htrace : WordTrace (prefixWord ++ tailWord_2555900) baseStart_2555900 baseEnd_2555900 := by
    simpa [prefixWord, tailWord_2555900, baseEnd_2555900] using wordTrace_append hprefix tailTrace_2555900
  have hstable : (prefixWord ++ tailWord_2555900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555900).length < 2 ^ (prefixWord ++ tailWord_2555900).sum := by decide
  have hdescent : baseEnd_2555900 < baseStart_2555900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555962 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_2555962 : Nat := 118140960795 + 2555962 * 2 ^ 59
def prefixEnd_2555962 : Nat := 4983230072969 + 3 ^ 40 * 2555962 * 2
def baseEnd_2555962 : Nat := 291652675694940893471189

theorem tailTrace_2555962 : CollatzResearch.WordTrace tailWord_2555962 prefixEnd_2555962 291652675694940893471189 := by
  unfold tailWord_2555962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23305898191548418100323535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62149061844129114934196093 23305898191548418100323535)
  ·
    refine ⟨34958847287322627150485303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23305898191548418100323535 34958847287322627150485303)
    ·
      refine ⟨52438270930983940725727955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34958847287322627150485303 52438270930983940725727955)
      ·
        refine ⟨78657406396475911088591933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52438270930983940725727955 78657406396475911088591933)
        ·
          refine ⟨29496527398678466658221975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78657406396475911088591933 29496527398678466658221975)
          ·
            refine ⟨44244791098017699987332963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29496527398678466658221975 44244791098017699987332963)
            ·
              refine ⟨66367186647026549980999445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44244791098017699987332963 66367186647026549980999445)
              ·
                refine ⟨3110961874079369530359349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66367186647026549980999445 3110961874079369530359349)
                ·
                  refine ⟨291652675694940893471189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3110961874079369530359349 291652675694940893471189)
                  ·
                    rfl

theorem cell22_2555962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_2555962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2555962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2555962 prefixEnd_2555962 := by exact prefixLift 2555962
  have htrace : WordTrace (prefixWord ++ tailWord_2555962) baseStart_2555962 baseEnd_2555962 := by
    simpa [prefixWord, tailWord_2555962, baseEnd_2555962] using wordTrace_append hprefix tailTrace_2555962
  have hstable : (prefixWord ++ tailWord_2555962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555962).length < 2 ^ (prefixWord ++ tailWord_2555962).sum := by decide
  have hdescent : baseEnd_2555962 < baseStart_2555962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556058 : List Nat := [3, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_2556058 : Nat := 118140960795 + 2556058 * 2 ^ 59
def prefixEnd_2556058 : Nat := 4983230072969 + 3 ^ 40 * 2556058 * 2
def baseEnd_2556058 : Nat := 291663629948903476671091

theorem tailTrace_2556058 : CollatzResearch.WordTrace tailWord_2556058 prefixEnd_2556058 291663629948903476671091 := by
  unfold tailWord_2556058
  simp only [CollatzResearch.WordTrace]
  refine ⟨23306773543461470199197207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62151396115897253864525885 23306773543461470199197207)
  ·
    refine ⟨34960160315192205298795811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23306773543461470199197207 34960160315192205298795811)
    ·
      refine ⟨52440240472788307948193717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34960160315192205298795811 52440240472788307948193717)
      ·
        refine ⟨4916272544323903870143161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52440240472788307948193717 4916272544323903870143161)
        ·
          refine ⟨3687204408242927902607371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4916272544323903870143161 3687204408242927902607371)
          ·
            refine ⟨5530806612364391853911057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687204408242927902607371 5530806612364391853911057)
            ·
              refine ⟨4148104959273293890433293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530806612364391853911057 4148104959273293890433293)
              ·
                refine ⟨1555539359727485208912485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4148104959273293890433293 1555539359727485208912485)
                ·
                  refine ⟨291663629948903476671091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555539359727485208912485 291663629948903476671091)
                  ·
                    rfl

theorem cell22_2556058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_2556058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556058 prefixEnd_2556058 := by exact prefixLift 2556058
  have htrace : WordTrace (prefixWord ++ tailWord_2556058) baseStart_2556058 baseEnd_2556058 := by
    simpa [prefixWord, tailWord_2556058, baseEnd_2556058] using wordTrace_append hprefix tailTrace_2556058
  have hstable : (prefixWord ++ tailWord_2556058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556058).length < 2 ^ (prefixWord ++ tailWord_2556058).sum := by decide
  have hdescent : baseEnd_2556058 < baseStart_2556058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556114 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_2556114 : Nat := 118140960795 + 2556114 * 2 ^ 59
def prefixEnd_2556114 : Nat := 4983230072969 + 3 ^ 40 * 2556114 * 2
def baseEnd_2556114 : Nat := 291670019930381650204367

theorem tailTrace_2556114 : CollatzResearch.WordTrace tailWord_2556114 prefixEnd_2556114 291670019930381650204367 := by
  unfold tailWord_2556114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23307284165410750590206849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62152757774428668240551597 23307284165410750590206849)
  ·
    refine ⟨17480463124058062942655137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23307284165410750590206849 17480463124058062942655137)
    ·
      refine ⟨13110347343043547206991353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17480463124058062942655137 13110347343043547206991353)
      ·
        refine ⟨9832760507282660405243515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13110347343043547206991353 9832760507282660405243515)
        ·
          refine ⟨14749140760923990607865273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9832760507282660405243515 14749140760923990607865273)
          ·
            refine ⟨11061855570692992955898955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14749140760923990607865273 11061855570692992955898955)
            ·
              refine ⟨16592783356039489433848433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11061855570692992955898955 16592783356039489433848433)
              ·
                refine ⟨12444587517029617075386325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16592783356039489433848433 12444587517029617075386325)
                ·
                  refine ⟨291670019930381650204367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12444587517029617075386325 291670019930381650204367)
                  ·
                    rfl

theorem cell22_2556114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_2556114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556114 prefixEnd_2556114 := by exact prefixLift 2556114
  have htrace : WordTrace (prefixWord ++ tailWord_2556114) baseStart_2556114 baseEnd_2556114 := by
    simpa [prefixWord, tailWord_2556114, baseEnd_2556114] using wordTrace_append hprefix tailTrace_2556114
  have hstable : (prefixWord ++ tailWord_2556114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556114).length < 2 ^ (prefixWord ++ tailWord_2556114).sum := by decide
  have hdescent : baseEnd_2556114 < baseStart_2556114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556193 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 4]
def baseStart_2556193 : Nat := 118140960795 + 2556193 * 2 ^ 59
def prefixEnd_2556193 : Nat := 4983230072969 + 3 ^ 40 * 2556193 * 2
def baseEnd_2556193 : Nat := 291679034368538359295953

theorem tailTrace_2556193 : CollatzResearch.WordTrace tailWord_2556193 prefixEnd_2556193 291679034368538359295953 := by
  unfold tailWord_2556193
  simp only [CollatzResearch.WordTrace]
  refine ⟨93232018028356798852953233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62154678685571199235302155 93232018028356798852953233)
  ·
    refine ⟨69924013521267599139714925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93232018028356798852953233 69924013521267599139714925)
    ·
      refine ⟨26221505070475349677393097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69924013521267599139714925 26221505070475349677393097)
      ·
        refine ⟨19666128802856512258044823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26221505070475349677393097 19666128802856512258044823)
        ·
          refine ⟨29499193204284768387067235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19666128802856512258044823 29499193204284768387067235)
          ·
            refine ⟨44248789806427152580600853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29499193204284768387067235 44248789806427152580600853)
            ·
              refine ⟨2074162022176272777215665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44248789806427152580600853 2074162022176272777215665)
              ·
                refine ⟨1555621516632204582911749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074162022176272777215665 1555621516632204582911749)
                ·
                  refine ⟨291679034368538359295953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555621516632204582911749 291679034368538359295953)
                  ·
                    rfl

theorem cell22_2556193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_2556193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556193 prefixEnd_2556193 := by exact prefixLift 2556193
  have htrace : WordTrace (prefixWord ++ tailWord_2556193) baseStart_2556193 baseEnd_2556193 := by
    simpa [prefixWord, tailWord_2556193, baseEnd_2556193] using wordTrace_append hprefix tailTrace_2556193
  have hstable : (prefixWord ++ tailWord_2556193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556193).length < 2 ^ (prefixWord ++ tailWord_2556193).sum := by decide
  have hdescent : baseEnd_2556193 < baseStart_2556193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556204 : List Nat := [2, 2, 1, 1, 1, 3, 5, 7]
def baseStart_2556204 : Nat := 118140960795 + 2556204 * 2 ^ 59
def prefixEnd_2556204 : Nat := 4983230072969 + 3 ^ 40 * 2556204 * 2
def baseEnd_2556204 : Nat := 97226763181157190651425

theorem tailTrace_2556204 : CollatzResearch.WordTrace tailWord_2556204 prefixEnd_2556204 97226763181157190651425 := by
  unfold tailWord_2556204
  simp only [CollatzResearch.WordTrace]
  refine ⟨46616209615658473865801833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62154946154211298487735777 46616209615658473865801833)
  ·
    refine ⟨34962157211743855399351375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46616209615658473865801833 34962157211743855399351375)
    ·
      refine ⟨52443235817615783099027063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34962157211743855399351375 52443235817615783099027063)
      ·
        refine ⟨78664853726423674648540595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52443235817615783099027063 78664853726423674648540595)
        ·
          refine ⟨117997280589635511972810893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78664853726423674648540595 117997280589635511972810893)
          ·
            refine ⟨44248980221113316989804085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117997280589635511972810893 44248980221113316989804085)
            ·
              refine ⟨4148341895729373467794133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44248980221113316989804085 4148341895729373467794133)
              ·
                refine ⟨97226763181157190651425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4148341895729373467794133 97226763181157190651425)
                ·
                  rfl

theorem cell22_2556204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_2556204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556204 prefixEnd_2556204 := by exact prefixLift 2556204
  have htrace : WordTrace (prefixWord ++ tailWord_2556204) baseStart_2556204 baseEnd_2556204 := by
    simpa [prefixWord, tailWord_2556204, baseEnd_2556204] using wordTrace_append hprefix tailTrace_2556204
  have hstable : (prefixWord ++ tailWord_2556204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556204).length < 2 ^ (prefixWord ++ tailWord_2556204).sum := by decide
  have hdescent : baseEnd_2556204 < baseStart_2556204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556236 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_2556236 : Nat := 118140960795 + 2556236 * 2 ^ 59
def prefixEnd_2556236 : Nat := 4983230072969 + 3 ^ 40 * 2556236 * 2
def baseEnd_2556236 : Nat := 875051822884377299062727

theorem tailTrace_2556236 : CollatzResearch.WordTrace tailWord_2556236 prefixEnd_2556236 875051822884377299062727 := by
  unfold tailWord_2556236
  simp only [CollatzResearch.WordTrace]
  refine ⟨46616793183600508598384281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62155724244800678131179041 46616793183600508598384281)
  ·
    refine ⟨34962594887700381448788211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46616793183600508598384281 34962594887700381448788211)
    ·
      refine ⟨52443892331550572173182317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34962594887700381448788211 52443892331550572173182317)
      ·
        refine ⟨19666459624331464564943369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52443892331550572173182317 19666459624331464564943369)
        ·
          refine ⟨14749844718248598423707527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19666459624331464564943369 14749844718248598423707527)
          ·
            refine ⟨22124767077372897635561291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14749844718248598423707527 22124767077372897635561291)
            ·
              refine ⟨33187150616059346453341937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22124767077372897635561291 33187150616059346453341937)
              ·
                refine ⟨24890362962044509840006453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33187150616059346453341937 24890362962044509840006453)
                ·
                  refine ⟨2333471527691672797500605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24890362962044509840006453 2333471527691672797500605)
                  ·
                    refine ⟨875051822884377299062727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333471527691672797500605 875051822884377299062727)
                    ·
                      rfl

theorem cell22_2556236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_2556236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556236 prefixEnd_2556236 := by exact prefixLift 2556236
  have htrace : WordTrace (prefixWord ++ tailWord_2556236) baseStart_2556236 baseEnd_2556236 := by
    simpa [prefixWord, tailWord_2556236, baseEnd_2556236] using wordTrace_append hprefix tailTrace_2556236
  have hstable : (prefixWord ++ tailWord_2556236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556236).length < 2 ^ (prefixWord ++ tailWord_2556236).sum := by decide
  have hdescent : baseEnd_2556236 < baseStart_2556236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556311 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 6]
def baseStart_2556311 : Nat := 118140960795 + 2556311 * 2 ^ 59
def prefixEnd_2556311 : Nat := 4983230072969 + 3 ^ 40 * 2556311 * 2
def baseEnd_2556311 : Nat := 291692498972367367812499

theorem tailTrace_2556311 : CollatzResearch.WordTrace tailWord_2556311 prefixEnd_2556311 291692498972367367812499 := by
  unfold tailWord_2556311
  simp only [CollatzResearch.WordTrace]
  refine ⟨93236321841929305005748787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62157547894619536670499191 93236321841929305005748787)
  ·
    refine ⟨139854482762893957508623181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93236321841929305005748787 139854482762893957508623181)
    ·
      refine ⟨52445431036085234065733693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139854482762893957508623181 52445431036085234065733693)
      ·
        refine ⟨19667036638531962774650135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52445431036085234065733693 19667036638531962774650135)
        ·
          refine ⟨29500554957797944161975203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19667036638531962774650135 29500554957797944161975203)
          ·
            refine ⟨44250832436696916242962805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29500554957797944161975203 44250832436696916242962805)
            ·
              refine ⟨4148515540940335897777763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44250832436696916242962805 4148515540940335897777763)
              ·
                refine ⟨6222773311410503846666645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148515540940335897777763 6222773311410503846666645)
                ·
                  refine ⟨291692498972367367812499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6222773311410503846666645 291692498972367367812499)
                  ·
                    rfl

theorem cell22_2556311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 6].length) (baseStart_2556311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556311 prefixEnd_2556311 := by exact prefixLift 2556311
  have htrace : WordTrace (prefixWord ++ tailWord_2556311) baseStart_2556311 baseEnd_2556311 := by
    simpa [prefixWord, tailWord_2556311, baseEnd_2556311] using wordTrace_append hprefix tailTrace_2556311
  have hstable : (prefixWord ++ tailWord_2556311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556311).length < 2 ^ (prefixWord ++ tailWord_2556311).sum := by decide
  have hdescent : baseEnd_2556311 < baseStart_2556311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556317 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 5]
def baseStart_2556317 : Nat := 118140960795 + 2556317 * 2 ^ 59
def prefixEnd_2556317 : Nat := 4983230072969 + 3 ^ 40 * 2556317 * 2
def baseEnd_2556317 : Nat := 291693183613240029262493

theorem tailTrace_2556317 : CollatzResearch.WordTrace tailWord_2556317 prefixEnd_2556317 291693183613240029262493 := by
  unfold tailWord_2556317
  simp only [CollatzResearch.WordTrace]
  refine ⟨93236540679907568030467205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62157693786605045353644803 93236540679907568030467205)
  ·
    refine ⟨17481851377482669005712601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93236540679907568030467205 17481851377482669005712601)
    ·
      refine ⟨13111388533112001754284451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17481851377482669005712601 13111388533112001754284451)
      ·
        refine ⟨19667082799668002631426677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13111388533112001754284451 19667082799668002631426677)
        ·
          refine ⟨1843789012468875246696251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19667082799668002631426677 1843789012468875246696251)
          ·
            refine ⟨2765683518703312870044377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843789012468875246696251 2765683518703312870044377)
            ·
              refine ⟨2074262639027484652533283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765683518703312870044377 2074262639027484652533283)
              ·
                refine ⟨3111393958541226978799925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074262639027484652533283 3111393958541226978799925)
                ·
                  refine ⟨291693183613240029262493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3111393958541226978799925 291693183613240029262493)
                  ·
                    rfl

theorem cell22_2556317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_2556317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556317 prefixEnd_2556317 := by exact prefixLift 2556317
  have htrace : WordTrace (prefixWord ++ tailWord_2556317) baseStart_2556317 baseEnd_2556317 := by
    simpa [prefixWord, tailWord_2556317, baseEnd_2556317] using wordTrace_append hprefix tailTrace_2556317
  have hstable : (prefixWord ++ tailWord_2556317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556317).length < 2 ^ (prefixWord ++ tailWord_2556317).sum := by decide
  have hdescent : baseEnd_2556317 < baseStart_2556317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556356 : List Nat := [2, 3, 3, 2, 12]
def baseStart_2556356 : Nat := 118140960795 + 2556356 * 2 ^ 59
def prefixEnd_2556356 : Nat := 4983230072969 + 3 ^ 40 * 2556356 * 2
def baseEnd_2556356 : Nat := 3601205355295213934413

theorem tailTrace_2556356 : CollatzResearch.WordTrace tailWord_2556356 prefixEnd_2556356 3601205355295213934413 := by
  unfold tailWord_2556356
  simp only [CollatzResearch.WordTrace]
  refine ⟨46618981563383138845568461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62158642084510851794091281 46618981563383138845568461)
  ·
    refine ⟨17482118086268677067088173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46618981563383138845568461 17482118086268677067088173)
    ·
      refine ⟨6555794282350753900158065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17482118086268677067088173 6555794282350753900158065)
      ·
        refine ⟨4916845711763065425118549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6555794282350753900158065 4916845711763065425118549)
        ·
          refine ⟨3601205355295213934413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4916845711763065425118549 3601205355295213934413)
          ·
            rfl

theorem cell22_2556356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 12].length) (baseStart_2556356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556356 prefixEnd_2556356 := by exact prefixLift 2556356
  have htrace : WordTrace (prefixWord ++ tailWord_2556356) baseStart_2556356 baseEnd_2556356 := by
    simpa [prefixWord, tailWord_2556356, baseEnd_2556356] using wordTrace_append hprefix tailTrace_2556356
  have hstable : (prefixWord ++ tailWord_2556356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556356).length < 2 ^ (prefixWord ++ tailWord_2556356).sum := by decide
  have hdescent : baseEnd_2556356 < baseStart_2556356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556360 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_2556360 : Nat := 118140960795 + 2556360 * 2 ^ 59
def prefixEnd_2556360 : Nat := 4983230072969 + 3 ^ 40 * 2556360 * 2
def baseEnd_2556360 : Nat := 875094270618482308962347

theorem tailTrace_2556360 : CollatzResearch.WordTrace tailWord_2556360 prefixEnd_2556360 875094270618482308962347 := by
  unfold tailWord_2556360
  simp only [CollatzResearch.WordTrace]
  refine ⟨46619054509375893187141267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62158739345834524249521689 46619054509375893187141267)
  ·
    refine ⟨69928581764063839780711901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46619054509375893187141267 69928581764063839780711901)
    ·
      refine ⟨26223218161523939917766963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69928581764063839780711901 26223218161523939917766963)
      ·
        refine ⟨39334827242285909876650445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26223218161523939917766963 39334827242285909876650445)
        ·
          refine ⟨14750560215857216203743917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39334827242285909876650445 14750560215857216203743917)
          ·
            refine ⟨5531460080946456076403969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14750560215857216203743917 5531460080946456076403969)
            ·
              refine ⟨4148595060709842057302977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531460080946456076403969 4148595060709842057302977)
              ·
                refine ⟨3111446295532381542977233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4148595060709842057302977 3111446295532381542977233)
                ·
                  refine ⟨2333584721649286157232925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3111446295532381542977233 2333584721649286157232925)
                  ·
                    refine ⟨875094270618482308962347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333584721649286157232925 875094270618482308962347)
                    ·
                      rfl

theorem cell22_2556360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_2556360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556360 prefixEnd_2556360 := by exact prefixLift 2556360
  have htrace : WordTrace (prefixWord ++ tailWord_2556360) baseStart_2556360 baseEnd_2556360 := by
    simpa [prefixWord, tailWord_2556360, baseEnd_2556360] using wordTrace_append hprefix tailTrace_2556360
  have hstable : (prefixWord ++ tailWord_2556360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556360).length < 2 ^ (prefixWord ++ tailWord_2556360).sum := by decide
  have hdescent : baseEnd_2556360 < baseStart_2556360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556373 : List Nat := [1, 3, 2, 3, 1, 4, 1, 7]
def baseStart_2556373 : Nat := 118140960795 + 2556373 * 2 ^ 59
def prefixEnd_2556373 : Nat := 4983230072969 + 3 ^ 40 * 2556373 * 2
def baseEnd_2556373 : Nat := 97233191198239400931923

theorem tailTrace_2556373 : CollatzResearch.WordTrace tailWord_2556373 prefixEnd_2556373 97233191198239400931923 := by
  unfold tailWord_2556373
  simp only [CollatzResearch.WordTrace]
  refine ⟨93238583167704689594505773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62159055445136459729670515 93238583167704689594505773)
  ·
    refine ⟨34964468687889258597939665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93238583167704689594505773 34964468687889258597939665)
    ·
      refine ⟨26223351515916943948454749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34964468687889258597939665 26223351515916943948454749)
      ·
        refine ⟨9833756818468853980670531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26223351515916943948454749 9833756818468853980670531)
        ·
          refine ⟨14750635227703280971005797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833756818468853980670531 14750635227703280971005797)
          ·
            refine ⟨2765744105194365182063587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14750635227703280971005797 2765744105194365182063587)
            ·
              refine ⟨4148616157791547773095381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765744105194365182063587 4148616157791547773095381)
              ·
                refine ⟨97233191198239400931923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4148616157791547773095381 97233191198239400931923)
                ·
                  rfl

theorem cell22_2556373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 7].length) (baseStart_2556373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556373 prefixEnd_2556373 := by exact prefixLift 2556373
  have htrace : WordTrace (prefixWord ++ tailWord_2556373) baseStart_2556373 baseEnd_2556373 := by
    simpa [prefixWord, tailWord_2556373, baseEnd_2556373] using wordTrace_append hprefix tailTrace_2556373
  have hstable : (prefixWord ++ tailWord_2556373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556373).length < 2 ^ (prefixWord ++ tailWord_2556373).sum := by decide
  have hdescent : baseEnd_2556373 < baseStart_2556373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556401 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 7]
def baseStart_2556401 : Nat := 118140960795 + 2556401 * 2 ^ 59
def prefixEnd_2556401 : Nat := 4983230072969 + 3 ^ 40 * 2556401 * 2
def baseEnd_2556401 : Nat := 291702768585457289562407

theorem tailTrace_2556401 : CollatzResearch.WordTrace tailWord_2556401 prefixEnd_2556401 291702768585457289562407 := by
  unfold tailWord_2556401
  simp only [CollatzResearch.WordTrace]
  refine ⟨93239604411603250376525057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62159736274402166917683371 93239604411603250376525057)
  ·
    refine ⟨69929703308702437782393793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93239604411603250376525057 69929703308702437782393793)
    ·
      refine ⟨52447277481526828336795345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69929703308702437782393793 52447277481526828336795345)
      ·
        refine ⟨39335458111145121252596509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52447277481526828336795345 39335458111145121252596509)
        ·
          refine ⟨14750796791679420469723691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39335458111145121252596509 14750796791679420469723691)
          ·
            refine ⟨22126195187519130704585537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14750796791679420469723691 22126195187519130704585537)
            ·
              refine ⟨16594646390639348028439153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22126195187519130704585537 16594646390639348028439153)
              ·
                refine ⟨12445984792979511021329365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16594646390639348028439153 12445984792979511021329365)
                ·
                  refine ⟨291702768585457289562407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12445984792979511021329365 291702768585457289562407)
                  ·
                    rfl

theorem cell22_2556401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_2556401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556401 prefixEnd_2556401 := by exact prefixLift 2556401
  have htrace : WordTrace (prefixWord ++ tailWord_2556401) baseStart_2556401 baseEnd_2556401 := by
    simpa [prefixWord, tailWord_2556401, baseEnd_2556401] using wordTrace_append hprefix tailTrace_2556401
  have hstable : (prefixWord ++ tailWord_2556401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556401).length < 2 ^ (prefixWord ++ tailWord_2556401).sum := by decide
  have hdescent : baseEnd_2556401 < baseStart_2556401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556491 : List Nat := [1, 1, 1, 1, 3, 1, 5, 9]
def baseStart_2556491 : Nat := 118140960795 + 2556491 * 2 ^ 59
def prefixEnd_2556491 : Nat := 4983230072969 + 3 ^ 40 * 2556491 * 2
def baseEnd_2556491 : Nat := 97237679399515737104105

theorem tailTrace_2556491 : CollatzResearch.WordTrace tailWord_2556491 prefixEnd_2556491 97237679399515737104105 := by
  unfold tailWord_2556491
  simp only [CollatzResearch.WordTrace]
  refine ⟨93242886981277195747301327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62161924654184797164867551 93242886981277195747301327)
  ·
    refine ⟨139864330471915793620951991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93242886981277195747301327 139864330471915793620951991)
    ·
      refine ⟨209796495707873690431427987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139864330471915793620951991 209796495707873690431427987)
      ·
        refine ⟨314694743561810535647141981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209796495707873690431427987 314694743561810535647141981)
        ·
          refine ⟨118010528835678950867678243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314694743561810535647141981 118010528835678950867678243)
          ·
            refine ⟨177015793253518426301517365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118010528835678950867678243 177015793253518426301517365)
            ·
              refine ⟨16595230617517352465767253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177015793253518426301517365 16595230617517352465767253)
              ·
                refine ⟨97237679399515737104105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16595230617517352465767253 97237679399515737104105)
                ·
                  rfl

theorem cell22_2556491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 9].length) (baseStart_2556491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556491 prefixEnd_2556491 := by exact prefixLift 2556491
  have htrace : WordTrace (prefixWord ++ tailWord_2556491) baseStart_2556491 baseEnd_2556491 := by
    simpa [prefixWord, tailWord_2556491, baseEnd_2556491] using wordTrace_append hprefix tailTrace_2556491
  have hstable : (prefixWord ++ tailWord_2556491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556491).length < 2 ^ (prefixWord ++ tailWord_2556491).sum := by decide
  have hdescent : baseEnd_2556491 < baseStart_2556491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556523 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 7, 3]
def baseStart_2556523 : Nat := 118140960795 + 2556523 * 2 ^ 59
def prefixEnd_2556523 : Nat := 4983230072969 + 3 ^ 40 * 2556523 * 2
def baseEnd_2556523 : Nat := 875150068849604217136847

theorem tailTrace_2556523 : CollatzResearch.WordTrace tailWord_2556523 prefixEnd_2556523 875150068849604217136847 := by
  unfold tailWord_2556523
  simp only [CollatzResearch.WordTrace]
  refine ⟨93244054117161265212466223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62162702744774176808310815 93244054117161265212466223)
  ·
    refine ⟨139866081175741897818699335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93244054117161265212466223 139866081175741897818699335)
    ·
      refine ⟨209799121763612846728049003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139866081175741897818699335 209799121763612846728049003)
      ·
        refine ⟨314698682645419270092073505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209799121763612846728049003 314698682645419270092073505)
        ·
          refine ⟨236024011984064452569055129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314698682645419270092073505 236024011984064452569055129)
          ·
            refine ⟨177018008988048339426791347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236024011984064452569055129 177018008988048339426791347)
            ·
              refine ⟨265527013482072509140187021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177018008988048339426791347 265527013482072509140187021)
              ·
                refine ⟨99572630055777190927570133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265527013482072509140187021 99572630055777190927570133)
                ·
                  refine ⟨2333733516932277912364925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 99572630055777190927570133 2333733516932277912364925)
                  ·
                    refine ⟨875150068849604217136847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333733516932277912364925 875150068849604217136847)
                    ·
                      rfl

theorem cell22_2556523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3].length) (baseStart_2556523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556523 prefixEnd_2556523 := by exact prefixLift 2556523
  have htrace : WordTrace (prefixWord ++ tailWord_2556523) baseStart_2556523 baseEnd_2556523 := by
    simpa [prefixWord, tailWord_2556523, baseEnd_2556523] using wordTrace_append hprefix tailTrace_2556523
  have hstable : (prefixWord ++ tailWord_2556523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556523).length < 2 ^ (prefixWord ++ tailWord_2556523).sum := by decide
  have hdescent : baseEnd_2556523 < baseStart_2556523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556546 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2556546 : Nat := 118140960795 + 2556546 * 2 ^ 59
def prefixEnd_2556546 : Nat := 4983230072969 + 3 ^ 40 * 2556546 * 2
def baseEnd_2556546 : Nat := 875157942219639823811777

theorem tailTrace_2556546 : CollatzResearch.WordTrace tailWord_2556546 prefixEnd_2556546 875157942219639823811777 := by
  unfold tailWord_2556546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23311223249019485035138373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62163261997385293427035661 23311223249019485035138373)
  ·
    refine ⟨4370854359191153444088445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23311223249019485035138373 4370854359191153444088445)
    ·
      refine ⟨1639070384696682541533167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4370854359191153444088445 1639070384696682541533167)
      ·
        refine ⟨2458605577045023812299751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639070384696682541533167 2458605577045023812299751)
        ·
          refine ⟨3687908365567535718449627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458605577045023812299751 3687908365567535718449627)
          ·
            refine ⟨5531862548351303577674441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687908365567535718449627 5531862548351303577674441)
            ·
              refine ⟨4148896911263477683255831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531862548351303577674441 4148896911263477683255831)
              ·
                refine ⟨6223345366895216524883747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148896911263477683255831 6223345366895216524883747)
                ·
                  refine ⟨9335018050342824787325621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223345366895216524883747 9335018050342824787325621)
                  ·
                    refine ⟨875157942219639823811777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9335018050342824787325621 875157942219639823811777)
                    ·
                      rfl

theorem cell22_2556546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2556546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556546 prefixEnd_2556546 := by exact prefixLift 2556546
  have htrace : WordTrace (prefixWord ++ tailWord_2556546) baseStart_2556546 baseEnd_2556546 := by
    simpa [prefixWord, tailWord_2556546, baseEnd_2556546] using wordTrace_append hprefix tailTrace_2556546
  have hstable : (prefixWord ++ tailWord_2556546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556546).length < 2 ^ (prefixWord ++ tailWord_2556546).sum := by decide
  have hdescent : baseEnd_2556546 < baseStart_2556546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556568 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_2556568 : Nat := 118140960795 + 2556568 * 2 ^ 59
def prefixEnd_2556568 : Nat := 4983230072969 + 3 ^ 40 * 2556568 * 2
def baseEnd_2556568 : Nat := 875165473269239099761709

theorem tailTrace_2556568 : CollatzResearch.WordTrace tailWord_2556568 prefixEnd_2556568 875165473269239099761709 := by
  unfold tailWord_2556568
  simp only [CollatzResearch.WordTrace]
  refine ⟨46622847700999118948927179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62163796934665491931902905 46622847700999118948927179)
  ·
    refine ⟨69934271551498678423390769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46622847700999118948927179 69934271551498678423390769)
    ·
      refine ⟨52450703663624008817543077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69934271551498678423390769 52450703663624008817543077)
      ·
        refine ⟨9834506936929501653289327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52450703663624008817543077 9834506936929501653289327)
        ·
          refine ⟨14751760405394252479933991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9834506936929501653289327 14751760405394252479933991)
          ·
            refine ⟨22127640608091378719900987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14751760405394252479933991 22127640608091378719900987)
            ·
              refine ⟨33191460912137068079851481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22127640608091378719900987 33191460912137068079851481)
              ·
                refine ⟨24893595684102801059888611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33191460912137068079851481 24893595684102801059888611)
                ·
                  refine ⟨37340393526154201589832917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24893595684102801059888611 37340393526154201589832917)
                  ·
                    refine ⟨875165473269239099761709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37340393526154201589832917 875165473269239099761709)
                    ·
                      rfl

theorem cell22_2556568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_2556568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556568 prefixEnd_2556568 := by exact prefixLift 2556568
  have htrace : WordTrace (prefixWord ++ tailWord_2556568) baseStart_2556568 baseEnd_2556568 := by
    simpa [prefixWord, tailWord_2556568, baseEnd_2556568] using wordTrace_append hprefix tailTrace_2556568
  have hstable : (prefixWord ++ tailWord_2556568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556568).length < 2 ^ (prefixWord ++ tailWord_2556568).sum := by decide
  have hdescent : baseEnd_2556568 < baseStart_2556568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556632 : List Nat := [2, 1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_2556632 : Nat := 118140960795 + 2556632 * 2 ^ 59
def prefixEnd_2556632 : Nat := 4983230072969 + 3 ^ 40 * 2556632 * 2
def baseEnd_2556632 : Nat := 291729127259054755387171

theorem tailTrace_2556632 : CollatzResearch.WordTrace tailWord_2556632 prefixEnd_2556632 291729127259054755387171 := by
  unfold tailWord_2556632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46624014836883188414092075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62165353115844251218789433 46624014836883188414092075)
  ·
    refine ⟨69936022255324782621138113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46624014836883188414092075 69936022255324782621138113)
    ·
      refine ⟨52452016691493586965853585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69936022255324782621138113 52452016691493586965853585)
      ·
        refine ⟨39339012518620190224390189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52452016691493586965853585 39339012518620190224390189)
        ·
          refine ⟨14752129694482571334146321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39339012518620190224390189 14752129694482571334146321)
          ·
            refine ⟨11064097270861928500609741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14752129694482571334146321 11064097270861928500609741)
            ·
              refine ⟨4149036476573223187728653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11064097270861928500609741 4149036476573223187728653)
              ·
                refine ⟨1555888678714958695398245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4149036476573223187728653 1555888678714958695398245)
                ·
                  refine ⟨291729127259054755387171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555888678714958695398245 291729127259054755387171)
                  ·
                    rfl

theorem cell22_2556632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_2556632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556632 prefixEnd_2556632 := by exact prefixLift 2556632
  have htrace : WordTrace (prefixWord ++ tailWord_2556632) baseStart_2556632 baseEnd_2556632 := by
    simpa [prefixWord, tailWord_2556632, baseEnd_2556632] using wordTrace_append hprefix tailTrace_2556632
  have hstable : (prefixWord ++ tailWord_2556632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556632).length < 2 ^ (prefixWord ++ tailWord_2556632).sum := by decide
  have hdescent : baseEnd_2556632 < baseStart_2556632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556645 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2556645 : Nat := 118140960795 + 2556645 * 2 ^ 59
def prefixEnd_2556645 : Nat := 4983230072969 + 3 ^ 40 * 2556645 * 2
def baseEnd_2556645 : Nat := 875191831942836565586473

theorem tailTrace_2556645 : CollatzResearch.WordTrace tailWord_2556645 prefixEnd_2556645 875191831942836565586473 := by
  unfold tailWord_2556645
  simp only [CollatzResearch.WordTrace]
  refine ⟨93248503822719280048407389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62165669215146186698938259 93248503822719280048407389)
  ·
    refine ⟨34968188933519730018152771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93248503822719280048407389 34968188933519730018152771)
    ·
      refine ⟨52452283400279595027229157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34968188933519730018152771 52452283400279595027229157)
      ·
        refine ⟨9834803137552424067605467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52452283400279595027229157 9834803137552424067605467)
        ·
          refine ⟨14752204706328636101408201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9834803137552424067605467 14752204706328636101408201)
          ·
            refine ⟨11064153529746477076056151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14752204706328636101408201 11064153529746477076056151)
            ·
              refine ⟨16596230294619715614084227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11064153529746477076056151 16596230294619715614084227)
              ·
                refine ⟨24894345441929573421126341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16596230294619715614084227 24894345441929573421126341)
                ·
                  refine ⟨4667689770361795016461189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24894345441929573421126341 4667689770361795016461189)
                  ·
                    refine ⟨875191831942836565586473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4667689770361795016461189 875191831942836565586473)
                    ·
                      rfl

theorem cell22_2556645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2556645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556645 prefixEnd_2556645 := by exact prefixLift 2556645
  have htrace : WordTrace (prefixWord ++ tailWord_2556645) baseStart_2556645 baseEnd_2556645 := by
    simpa [prefixWord, tailWord_2556645, baseEnd_2556645] using wordTrace_append hprefix tailTrace_2556645
  have hstable : (prefixWord ++ tailWord_2556645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556645).length < 2 ^ (prefixWord ++ tailWord_2556645).sum := by decide
  have hdescent : baseEnd_2556645 < baseStart_2556645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556675 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 5, 3]
def baseStart_2556675 : Nat := 118140960795 + 2556675 * 2 ^ 59
def prefixEnd_2556675 : Nat := 4983230072969 + 3 ^ 40 * 2556675 * 2
def baseEnd_2556675 : Nat := 875202101555926487336381

theorem tailTrace_2556675 : CollatzResearch.WordTrace tailWord_2556675 prefixEnd_2556675 875202101555926487336381 := by
  unfold tailWord_2556675
  simp only [CollatzResearch.WordTrace]
  refine ⟨93249598012610595171999479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62166398675073730114666319 93249598012610595171999479)
  ·
    refine ⟨139874397018915892757999219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93249598012610595171999479 139874397018915892757999219)
    ·
      refine ⟨209811595528373839136998829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139874397018915892757999219 209811595528373839136998829)
      ·
        refine ⟨78679348323140189676374561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209811595528373839136998829 78679348323140189676374561)
        ·
          refine ⟨59009511242355142257280921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78679348323140189676374561 59009511242355142257280921)
          ·
            refine ⟨44257133431766356692960691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59009511242355142257280921 44257133431766356692960691)
            ·
              refine ⟨66385700147649535039441037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44257133431766356692960691 66385700147649535039441037)
              ·
                refine ⟨24894637555368575639790389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66385700147649535039441037 24894637555368575639790389)
                ·
                  refine ⟨2333872270815803966230349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24894637555368575639790389 2333872270815803966230349)
                  ·
                    refine ⟨875202101555926487336381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333872270815803966230349 875202101555926487336381)
                    ·
                      rfl

theorem cell22_2556675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3].length) (baseStart_2556675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556675 prefixEnd_2556675 := by exact prefixLift 2556675
  have htrace : WordTrace (prefixWord ++ tailWord_2556675) baseStart_2556675 baseEnd_2556675 := by
    simpa [prefixWord, tailWord_2556675, baseEnd_2556675] using wordTrace_append hprefix tailTrace_2556675
  have hstable : (prefixWord ++ tailWord_2556675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556675).length < 2 ^ (prefixWord ++ tailWord_2556675).sum := by decide
  have hdescent : baseEnd_2556675 < baseStart_2556675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556709 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_2556709 : Nat := 118140960795 + 2556709 * 2 ^ 59
def prefixEnd_2556709 : Nat := 4983230072969 + 3 ^ 40 * 2556709 * 2
def baseEnd_2556709 : Nat := 875213740450761731986277

theorem tailTrace_2556709 : CollatzResearch.WordTrace tailWord_2556709 prefixEnd_2556709 875213740450761731986277 := by
  unfold tailWord_2556709
  simp only [CollatzResearch.WordTrace]
  refine ⟨93250838094487418978737181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62167225396324945985824787 93250838094487418978737181)
  ·
    refine ⟨34969064285432782117026443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93250838094487418978737181 34969064285432782117026443)
    ·
      refine ⟨52453596428149173175539665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34969064285432782117026443 52453596428149173175539665)
      ·
        refine ⟨39340197321111879881654749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52453596428149173175539665 39340197321111879881654749)
        ·
          refine ⟨14752573995416954955620531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39340197321111879881654749 14752573995416954955620531)
          ·
            refine ⟨22128860993125432433430797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14752573995416954955620531 22128860993125432433430797)
            ·
              refine ⟨8298322872422037162536549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22128860993125432433430797 8298322872422037162536549)
              ·
                refine ⟨1555935538579131967975603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8298322872422037162536549 1555935538579131967975603)
                ·
                  refine ⟨2333903307868697951963405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555935538579131967975603 2333903307868697951963405)
                  ·
                    refine ⟨875213740450761731986277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333903307868697951963405 875213740450761731986277)
                    ·
                      rfl

theorem cell22_2556709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_2556709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556709 prefixEnd_2556709 := by exact prefixLift 2556709
  have htrace : WordTrace (prefixWord ++ tailWord_2556709) baseStart_2556709 baseEnd_2556709 := by
    simpa [prefixWord, tailWord_2556709, baseEnd_2556709] using wordTrace_append hprefix tailTrace_2556709
  have hstable : (prefixWord ++ tailWord_2556709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556709).length < 2 ^ (prefixWord ++ tailWord_2556709).sum := by decide
  have hdescent : baseEnd_2556709 < baseStart_2556709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556726 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2556726 : Nat := 118140960795 + 2556726 * 2 ^ 59
def prefixEnd_2556726 : Nat := 4983230072969 + 3 ^ 40 * 2556726 * 2
def baseEnd_2556726 : Nat := 875219559898179354311225

theorem tailTrace_2556726 : CollatzResearch.WordTrace tailWord_2556726 prefixEnd_2556726 875219559898179354311225 := by
  unfold tailWord_2556726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828216133464114430131627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62167638756950553921404021 5828216133464114430131627)
  ·
    refine ⟨8742324200196171645197441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5828216133464114430131627 8742324200196171645197441)
    ·
      refine ⟨6556743150147128733898081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8742324200196171645197441 6556743150147128733898081)
      ·
        refine ⟨4917557362610346550423561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6556743150147128733898081 4917557362610346550423561)
        ·
          refine ⟨3688168021957759912817671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4917557362610346550423561 3688168021957759912817671)
          ·
            refine ⟨5532252032936639869226507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688168021957759912817671 5532252032936639869226507)
            ·
              refine ⟨8298378049404959803839761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532252032936639869226507 8298378049404959803839761)
              ·
                refine ⟨6223783537053719852879821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8298378049404959803839761 6223783537053719852879821)
                ·
                  refine ⟨2333918826395144944829933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6223783537053719852879821 2333918826395144944829933)
                  ·
                    refine ⟨875219559898179354311225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333918826395144944829933 875219559898179354311225)
                    ·
                      rfl

theorem cell22_2556726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2556726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556726 prefixEnd_2556726 := by exact prefixLift 2556726
  have htrace : WordTrace (prefixWord ++ tailWord_2556726) baseStart_2556726 baseEnd_2556726 := by
    simpa [prefixWord, tailWord_2556726, baseEnd_2556726] using wordTrace_append hprefix tailTrace_2556726
  have hstable : (prefixWord ++ tailWord_2556726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556726).length < 2 ^ (prefixWord ++ tailWord_2556726).sum := by decide
  have hdescent : baseEnd_2556726 < baseStart_2556726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556756 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2556756 : Nat := 118140960795 + 2556756 * 2 ^ 59
def prefixEnd_2556756 : Nat := 4983230072969 + 3 ^ 40 * 2556756 * 2
def baseEnd_2556756 : Nat := 291743276503756425353711

theorem tailTrace_2556756 : CollatzResearch.WordTrace tailWord_2556756 prefixEnd_2556756 291743276503756425353711 := by
  unfold tailWord_2556756
  simp only [CollatzResearch.WordTrace]
  refine ⟨46626276162658573002849061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62168368216878097337132081 46626276162658573002849061)
  ·
    refine ⟨8742426780498482438034199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46626276162658573002849061 8742426780498482438034199)
    ·
      refine ⟨13113640170747723657051299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742426780498482438034199 13113640170747723657051299)
      ·
        refine ⟨19670460256121585485576949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13113640170747723657051299 19670460256121585485576949)
        ·
          refine ⟨1844105649011398639272839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19670460256121585485576949 1844105649011398639272839)
          ·
            refine ⟨2766158473517097958909259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844105649011398639272839 2766158473517097958909259)
            ·
              refine ⟨4149237710275646938363889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766158473517097958909259 4149237710275646938363889)
              ·
                refine ⟨3111928282706735203772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4149237710275646938363889 3111928282706735203772917)
                ·
                  refine ⟨291743276503756425353711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3111928282706735203772917 291743276503756425353711)
                  ·
                    rfl

theorem cell22_2556756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2556756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556756 prefixEnd_2556756 := by exact prefixLift 2556756
  have htrace : WordTrace (prefixWord ++ tailWord_2556756) baseStart_2556756 baseEnd_2556756 := by
    simpa [prefixWord, tailWord_2556756, baseEnd_2556756] using wordTrace_append hprefix tailTrace_2556756
  have hstable : (prefixWord ++ tailWord_2556756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556756).length < 2 ^ (prefixWord ++ tailWord_2556756).sum := by decide
  have hdescent : baseEnd_2556756 < baseStart_2556756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556767 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 4]
def baseStart_2556767 : Nat := 118140960795 + 2556767 * 2 ^ 59
def prefixEnd_2556767 : Nat := 4983230072969 + 3 ^ 40 * 2556767 * 2
def baseEnd_2556767 : Nat := 291744531678689638012033

theorem tailTrace_2556767 : CollatzResearch.WordTrace tailWord_2556767 prefixEnd_2556767 291744531678689638012033 := by
  unfold tailWord_2556767
  simp only [CollatzResearch.WordTrace]
  refine ⟨93252953528277294884348555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62168635685518196589565703 93252953528277294884348555)
  ·
    refine ⟨139879430292415942326522833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93252953528277294884348555 139879430292415942326522833)
    ·
      refine ⟨104909572719311956744892125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139879430292415942326522833 104909572719311956744892125)
      ·
        refine ⟨39341089769741983779334547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104909572719311956744892125 39341089769741983779334547)
        ·
          refine ⟨59011634654612975669001821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39341089769741983779334547 59011634654612975669001821)
          ·
            refine ⟨22129362995479865875875683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59011634654612975669001821 22129362995479865875875683)
            ·
              refine ⟨33194044493219798813813525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22129362995479865875875683 33194044493219798813813525)
              ·
                refine ⟨1555970835619678069397509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33194044493219798813813525 1555970835619678069397509)
                ·
                  refine ⟨291744531678689638012033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555970835619678069397509 291744531678689638012033)
                  ·
                    rfl

theorem cell22_2556767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 4].length) (baseStart_2556767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556767 prefixEnd_2556767 := by exact prefixLift 2556767
  have htrace : WordTrace (prefixWord ++ tailWord_2556767) baseStart_2556767 baseEnd_2556767 := by
    simpa [prefixWord, tailWord_2556767, baseEnd_2556767] using wordTrace_append hprefix tailTrace_2556767
  have hstable : (prefixWord ++ tailWord_2556767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556767).length < 2 ^ (prefixWord ++ tailWord_2556767).sum := by decide
  have hdescent : baseEnd_2556767 < baseStart_2556767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556780 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2556780 : Nat := 118140960795 + 2556780 * 2 ^ 59
def prefixEnd_2556780 : Nat := 4983230072969 + 3 ^ 40 * 2556780 * 2
def baseEnd_2556780 : Nat := 875238045201741213461059

theorem tailTrace_2556780 : CollatzResearch.WordTrace tailWord_2556780 prefixEnd_2556780 875238045201741213461059 := by
  unfold tailWord_2556780
  simp only [CollatzResearch.WordTrace]
  refine ⟨46626713838615099052285897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62168951784820132069714529 46626713838615099052285897)
  ·
    refine ⟨34970035378961324289214423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46626713838615099052285897 34970035378961324289214423)
    ·
      refine ⟨52455053068441986433821635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34970035378961324289214423 52455053068441986433821635)
      ·
        refine ⟨78682579602662979650732453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52455053068441986433821635 78682579602662979650732453)
        ·
          refine ⟨14752983675499308684512335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78682579602662979650732453 14752983675499308684512335)
          ·
            refine ⟨22129475513248963026768503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14752983675499308684512335 22129475513248963026768503)
            ·
              refine ⟨33194213269873444540152755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22129475513248963026768503 33194213269873444540152755)
              ·
                refine ⟨49791319904810166810229133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33194213269873444540152755 49791319904810166810229133)
                ·
                  refine ⟨18671744964303812553835925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49791319904810166810229133 18671744964303812553835925)
                  ·
                    refine ⟨875238045201741213461059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18671744964303812553835925 875238045201741213461059)
                    ·
                      rfl

theorem cell22_2556780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2556780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556780 prefixEnd_2556780 := by exact prefixLift 2556780
  have htrace : WordTrace (prefixWord ++ tailWord_2556780) baseStart_2556780 baseEnd_2556780 := by
    simpa [prefixWord, tailWord_2556780, baseEnd_2556780] using wordTrace_append hprefix tailTrace_2556780
  have hstable : (prefixWord ++ tailWord_2556780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556780).length < 2 ^ (prefixWord ++ tailWord_2556780).sum := by decide
  have hdescent : baseEnd_2556780 < baseStart_2556780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556818 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_2556818 : Nat := 118140960795 + 2556818 * 2 ^ 59
def prefixEnd_2556818 : Nat := 4983230072969 + 3 ^ 40 * 2556818 * 2
def baseEnd_2556818 : Nat := 291750351126107260336981

theorem tailTrace_2556818 : CollatzResearch.WordTrace tailWord_2556818 prefixEnd_2556818 291750351126107260336981 := by
  unfold tailWord_2556818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313703412773132648613777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62169875767395020396303405 23313703412773132648613777)
  ·
    refine ⟨17485277559579849486460333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23313703412773132648613777 17485277559579849486460333)
    ·
      refine ⟨6556979084842443557422625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17485277559579849486460333 6556979084842443557422625)
      ·
        refine ⟨4917734313631832668066969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6556979084842443557422625 4917734313631832668066969)
        ·
          refine ⟨3688300735223874501050227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4917734313631832668066969 3688300735223874501050227)
          ·
            refine ⟨5532451102835811751575341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688300735223874501050227 5532451102835811751575341)
            ·
              refine ⟨2074669163563429406840753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5532451102835811751575341 2074669163563429406840753)
              ·
                refine ⟨1556001872672572055130565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074669163563429406840753 1556001872672572055130565)
                ·
                  refine ⟨291750351126107260336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556001872672572055130565 291750351126107260336981)
                  ·
                    rfl

theorem cell22_2556818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_2556818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556818 prefixEnd_2556818 := by exact prefixLift 2556818
  have htrace : WordTrace (prefixWord ++ tailWord_2556818) baseStart_2556818 baseEnd_2556818 := by
    simpa [prefixWord, tailWord_2556818, baseEnd_2556818] using wordTrace_append hprefix tailTrace_2556818
  have hstable : (prefixWord ++ tailWord_2556818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556818).length < 2 ^ (prefixWord ++ tailWord_2556818).sum := by decide
  have hdescent : baseEnd_2556818 < baseStart_2556818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556825 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_2556825 : Nat := 118140960795 + 2556825 * 2 ^ 59
def prefixEnd_2556825 : Nat := 4983230072969 + 3 ^ 40 * 2556825 * 2
def baseEnd_2556825 : Nat := 875253449621376096085921

theorem tailTrace_2556825 : CollatzResearch.WordTrace tailWord_2556825 prefixEnd_2556825 875253449621376096085921 := by
  unfold tailWord_2556825
  simp only [CollatzResearch.WordTrace]
  refine ⟨93255068962067170789959929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62170045974711447193306619 93255068962067170789959929)
  ·
    refine ⟨69941301721550378092469947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93255068962067170789959929 69941301721550378092469947)
    ·
      refine ⟨104911952582325567138704921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69941301721550378092469947 104911952582325567138704921)
      ·
        refine ⟨78683964436744175354028691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104911952582325567138704921 78683964436744175354028691)
        ·
          refine ⟨118025946655116263031043037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78683964436744175354028691 118025946655116263031043037)
          ·
            refine ⟨44259729995668598636641139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118025946655116263031043037 44259729995668598636641139)
            ·
              refine ⟨66389594993502897954961709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44259729995668598636641139 66389594993502897954961709)
              ·
                refine ⟨24896098122563586733110641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66389594993502897954961709 24896098122563586733110641)
                ·
                  refine ⟨18672073591922690049832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24896098122563586733110641 18672073591922690049832981)
                  ·
                    refine ⟨875253449621376096085921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18672073591922690049832981 875253449621376096085921)
                    ·
                      rfl

theorem cell22_2556825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_2556825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556825 prefixEnd_2556825 := by exact prefixLift 2556825
  have htrace : WordTrace (prefixWord ++ tailWord_2556825) baseStart_2556825 baseEnd_2556825 := by
    simpa [prefixWord, tailWord_2556825, baseEnd_2556825] using wordTrace_append hprefix tailTrace_2556825
  have hstable : (prefixWord ++ tailWord_2556825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556825).length < 2 ^ (prefixWord ++ tailWord_2556825).sum := by decide
  have hdescent : baseEnd_2556825 < baseStart_2556825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556833 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_2556833 : Nat := 118140960795 + 2556833 * 2 ^ 59
def prefixEnd_2556833 : Nat := 4983230072969 + 3 ^ 40 * 2556833 * 2
def baseEnd_2556833 : Nat := 875256188184866741885897

theorem tailTrace_2556833 : CollatzResearch.WordTrace tailWord_2556833 prefixEnd_2556833 875256188184866741885897 := by
  unfold tailWord_2556833
  simp only [CollatzResearch.WordTrace]
  refine ⟨93255360746038188156251153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62170240497358792104167435 93255360746038188156251153)
  ·
    refine ⟨69941520559528641117188365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93255360746038188156251153 69941520559528641117188365)
    ·
      refine ⟨26228070209823240418945637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69941520559528641117188365 26228070209823240418945637)
      ·
        refine ⟨4917763164341857578552307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26228070209823240418945637 4917763164341857578552307)
        ·
          refine ⟨7376644746512786367828461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917763164341857578552307 7376644746512786367828461)
          ·
            refine ⟨2766241779942294887935673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7376644746512786367828461 2766241779942294887935673)
            ·
              refine ⟨2074681334956721165951755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766241779942294887935673 2074681334956721165951755)
              ·
                refine ⟨3112022002435081748927633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074681334956721165951755 3112022002435081748927633)
                ·
                  refine ⟨2334016501826311311695725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112022002435081748927633 2334016501826311311695725)
                  ·
                    refine ⟨875256188184866741885897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334016501826311311695725 875256188184866741885897)
                    ·
                      rfl

theorem cell22_2556833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_2556833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556833 prefixEnd_2556833 := by exact prefixLift 2556833
  have htrace : WordTrace (prefixWord ++ tailWord_2556833) baseStart_2556833 baseEnd_2556833 := by
    simpa [prefixWord, tailWord_2556833, baseEnd_2556833] using wordTrace_append hprefix tailTrace_2556833
  have hstable : (prefixWord ++ tailWord_2556833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556833).length < 2 ^ (prefixWord ++ tailWord_2556833).sum := by decide
  have hdescent : baseEnd_2556833 < baseStart_2556833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556878 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_2556878 : Nat := 118140960795 + 2556878 * 2 ^ 59
def prefixEnd_2556878 : Nat := 4983230072969 + 3 ^ 40 * 2556878 * 2
def baseEnd_2556878 : Nat := 875271592604501624510759

theorem tailTrace_2556878 : CollatzResearch.WordTrace tailWord_2556878 prefixEnd_2556878 875271592604501624510759 := by
  unfold tailWord_2556878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11657125253859395105204911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62171334687250107227759525 11657125253859395105204911)
  ·
    refine ⟨17485687880789092657807367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11657125253859395105204911 17485687880789092657807367)
    ·
      refine ⟨26228531821183638986711051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17485687880789092657807367 26228531821183638986711051)
      ·
        refine ⟨39342797731775458480066577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26228531821183638986711051 39342797731775458480066577)
        ·
          refine ⟨29507098298831593860049933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39342797731775458480066577 29507098298831593860049933)
          ·
            refine ⟨11065161862061847697518725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29507098298831593860049933 11065161862061847697518725)
            ·
              refine ⟨2074717849136596443284761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11065161862061847697518725 2074717849136596443284761)
              ·
                refine ⟨1556038386852447332463571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074717849136596443284761 1556038386852447332463571)
                ·
                  refine ⟨2334057580278670998695357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556038386852447332463571 2334057580278670998695357)
                  ·
                    refine ⟨875271592604501624510759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334057580278670998695357 875271592604501624510759)
                    ·
                      rfl

theorem cell22_2556878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_2556878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556878 prefixEnd_2556878 := by exact prefixLift 2556878
  have htrace : WordTrace (prefixWord ++ tailWord_2556878) baseStart_2556878 baseEnd_2556878 := by
    simpa [prefixWord, tailWord_2556878, baseEnd_2556878] using wordTrace_append hprefix tailTrace_2556878
  have hstable : (prefixWord ++ tailWord_2556878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556878).length < 2 ^ (prefixWord ++ tailWord_2556878).sum := by decide
  have hdescent : baseEnd_2556878 < baseStart_2556878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556951 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 1, 5]
def baseStart_2556951 : Nat := 118140960795 + 2556951 * 2 ^ 59
def prefixEnd_2556951 : Nat := 4983230072969 + 3 ^ 40 * 2556951 * 2
def baseEnd_2556951 : Nat := 875296581996353767435535

theorem tailTrace_2556951 : CollatzResearch.WordTrace tailWord_2556951 prefixEnd_2556951 875296581996353767435535 := by
  unfold tailWord_2556951
  simp only [CollatzResearch.WordTrace]
  refine ⟨93259664559610694309046707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62173109706407129539364471 93259664559610694309046707)
  ·
    refine ⟨139889496839416041463570061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93259664559610694309046707 139889496839416041463570061)
    ·
      refine ⟨52458561314781015548838773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139889496839416041463570061 52458561314781015548838773)
      ·
        refine ⟨4917990123260720207703635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52458561314781015548838773 4917990123260720207703635)
        ·
          refine ⟨7376985184891080311555453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917990123260720207703635 7376985184891080311555453)
          ·
            refine ⟨2766369444334155116833295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7376985184891080311555453 2766369444334155116833295)
            ·
              refine ⟨4149554166501232675249943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766369444334155116833295 4149554166501232675249943)
              ·
                refine ⟨6224331249751849012874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149554166501232675249943 6224331249751849012874915)
                ·
                  refine ⟨9336496874627773519312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224331249751849012874915 9336496874627773519312373)
                  ·
                    refine ⟨875296581996353767435535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9336496874627773519312373 875296581996353767435535)
                    ·
                      rfl

theorem cell22_2556951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_2556951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556951 prefixEnd_2556951 := by exact prefixLift 2556951
  have htrace : WordTrace (prefixWord ++ tailWord_2556951) baseStart_2556951 baseEnd_2556951 := by
    simpa [prefixWord, tailWord_2556951, baseEnd_2556951] using wordTrace_append hprefix tailTrace_2556951
  have hstable : (prefixWord ++ tailWord_2556951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556951).length < 2 ^ (prefixWord ++ tailWord_2556951).sum := by decide
  have hdescent : baseEnd_2556951 < baseStart_2556951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556964 : List Nat := [2, 3, 1, 4, 1, 2, 1, 8]
def baseStart_2556964 : Nat := 118140960795 + 2556964 * 2 ^ 59
def prefixEnd_2556964 : Nat := 4983230072969 + 3 ^ 40 * 2556964 * 2
def baseEnd_2556964 : Nat := 97255670240225118540055

theorem tailTrace_2556964 : CollatzResearch.WordTrace tailWord_2556964 prefixEnd_2556964 97255670240225118540055 := by
  unfold tailWord_2556964
  simp only [CollatzResearch.WordTrace]
  refine ⟨46630069354281798764634973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62173425805709065019513297 46630069354281798764634973)
  ·
    refine ⟨17486276007855674536738115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46630069354281798764634973 17486276007855674536738115)
    ·
      refine ⟨26229414011783511805107173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17486276007855674536738115 26229414011783511805107173)
      ·
        refine ⟨4918015127209408463457595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26229414011783511805107173 4918015127209408463457595)
        ·
          refine ⟨7377022690814112695186393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4918015127209408463457595 7377022690814112695186393)
          ·
            refine ⟨5532767018110584521389795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7377022690814112695186393 5532767018110584521389795)
            ·
              refine ⟨8299150527165876782084693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532767018110584521389795 8299150527165876782084693)
              ·
                refine ⟨97255670240225118540055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8299150527165876782084693 97255670240225118540055)
                ·
                  rfl

theorem cell22_2556964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_2556964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556964 prefixEnd_2556964 := by exact prefixLift 2556964
  have htrace : WordTrace (prefixWord ++ tailWord_2556964) baseStart_2556964 baseEnd_2556964 := by
    simpa [prefixWord, tailWord_2556964, baseEnd_2556964] using wordTrace_append hprefix tailTrace_2556964
  have hstable : (prefixWord ++ tailWord_2556964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556964).length < 2 ^ (prefixWord ++ tailWord_2556964).sum := by decide
  have hdescent : baseEnd_2556964 < baseStart_2556964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556970 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_2556970 : Nat := 118140960795 + 2556970 * 2 ^ 59
def prefixEnd_2556970 : Nat := 4983230072969 + 3 ^ 40 * 2556970 * 2
def baseEnd_2556970 : Nat := 291767695361548017070159

theorem tailTrace_2556970 : CollatzResearch.WordTrace tailWord_2556970 prefixEnd_2556970 291767695361548017070159 := by
  unfold tailWord_2556970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315089386635465138497091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62173571697694573702658909 23315089386635465138497091)
  ·
    refine ⟨34972634079953197707745637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23315089386635465138497091 34972634079953197707745637)
    ·
      refine ⟨6557368889991224570202307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34972634079953197707745637 6557368889991224570202307)
      ·
        refine ⟨9836053334986836855303461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6557368889991224570202307 9836053334986836855303461)
        ·
          refine ⟨1844260000310031910369399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9836053334986836855303461 1844260000310031910369399)
          ·
            refine ⟨2766390000465047865554099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844260000310031910369399 2766390000465047865554099)
            ·
              refine ⟨4149585000697571798331149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766390000465047865554099 4149585000697571798331149)
              ·
                refine ⟨1556094375261589424374181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4149585000697571798331149 1556094375261589424374181)
                ·
                  refine ⟨291767695361548017070159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556094375261589424374181 291767695361548017070159)
                  ·
                    rfl

theorem cell22_2556970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_2556970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556970 prefixEnd_2556970 := by exact prefixLift 2556970
  have htrace : WordTrace (prefixWord ++ tailWord_2556970) baseStart_2556970 baseEnd_2556970 := by
    simpa [prefixWord, tailWord_2556970, baseEnd_2556970] using wordTrace_append hprefix tailTrace_2556970
  have hstable : (prefixWord ++ tailWord_2556970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556970).length < 2 ^ (prefixWord ++ tailWord_2556970).sum := by decide
  have hdescent : baseEnd_2556970 < baseStart_2556970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556992 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_2556992 : Nat := 118140960795 + 2556992 * 2 ^ 59
def prefixEnd_2556992 : Nat := 4983230072969 + 3 ^ 40 * 2556992 * 2
def baseEnd_2556992 : Nat := 291770205711414442386803

theorem tailTrace_2556992 : CollatzResearch.WordTrace tailWord_2556992 prefixEnd_2556992 291770205711414442386803 := by
  unfold tailWord_2556992
  simp only [CollatzResearch.WordTrace]
  refine ⟨46630579976231079155644615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62174106634974772207526153 46630579976231079155644615)
  ·
    refine ⟨69945869964346618733466923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46630579976231079155644615 69945869964346618733466923)
    ·
      refine ⟨104918804946519928100200385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69945869964346618733466923 104918804946519928100200385)
      ·
        refine ⟨78689103709889946075150289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104918804946519928100200385 78689103709889946075150289)
        ·
          refine ⟨59016827782417459556362717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78689103709889946075150289 59016827782417459556362717)
          ·
            refine ⟨22131310418406547333636019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59016827782417459556362717 22131310418406547333636019)
            ·
              refine ⟨33196965627609821000454029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22131310418406547333636019 33196965627609821000454029)
              ·
                refine ⟨12448862110353682875170261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33196965627609821000454029 12448862110353682875170261)
                ·
                  refine ⟨291770205711414442386803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12448862110353682875170261 291770205711414442386803)
                  ·
                    rfl

theorem cell22_2556992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_2556992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2556992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2556992 prefixEnd_2556992 := by exact prefixLift 2556992
  have htrace : WordTrace (prefixWord ++ tailWord_2556992) baseStart_2556992 baseEnd_2556992 := by
    simpa [prefixWord, tailWord_2556992, baseEnd_2556992] using wordTrace_append hprefix tailTrace_2556992
  have hstable : (prefixWord ++ tailWord_2556992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556992).length < 2 ^ (prefixWord ++ tailWord_2556992).sum := by decide
  have hdescent : baseEnd_2556992 < baseStart_2556992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557120 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_2557120 : Nat := 118140960795 + 2557120 * 2 ^ 59
def prefixEnd_2557120 : Nat := 4983230072969 + 3 ^ 40 * 2557120 * 2
def baseEnd_2557120 : Nat := 875354434150093659960017

theorem tailTrace_2557120 : CollatzResearch.WordTrace tailWord_2557120 prefixEnd_2557120 875354434150093659960017 := by
  unfold tailWord_2557120
  simp only [CollatzResearch.WordTrace]
  refine ⟨46632914247999218085974407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62177218997332290781299209 46632914247999218085974407)
  ·
    refine ⟨69949371371998827128961611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46632914247999218085974407 69949371371998827128961611)
    ·
      refine ⟨104924057057998240693442417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69949371371998827128961611 104924057057998240693442417)
      ·
        refine ⟨78693042793498680520081813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104924057057998240693442417 78693042793498680520081813)
        ·
          refine ⟨3688736380945250649378835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78693042793498680520081813 3688736380945250649378835)
          ·
            refine ⟨5533104571417875974068253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688736380945250649378835 5533104571417875974068253)
            ·
              refine ⟨2074914214281703490275595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5533104571417875974068253 2074914214281703490275595)
              ·
                refine ⟨3112371321422555235413393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074914214281703490275595 3112371321422555235413393)
                ·
                  refine ⟨2334278491066916426560045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112371321422555235413393 2334278491066916426560045)
                  ·
                    refine ⟨875354434150093659960017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334278491066916426560045 875354434150093659960017)
                    ·
                      rfl

theorem cell22_2557120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_2557120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557120 prefixEnd_2557120 := by exact prefixLift 2557120
  have htrace : WordTrace (prefixWord ++ tailWord_2557120) baseStart_2557120 baseEnd_2557120 := by
    simpa [prefixWord, tailWord_2557120, baseEnd_2557120] using wordTrace_append hprefix tailTrace_2557120
  have hstable : (prefixWord ++ tailWord_2557120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557120).length < 2 ^ (prefixWord ++ tailWord_2557120).sum := by decide
  have hdescent : baseEnd_2557120 < baseStart_2557120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557165 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2557165 : Nat := 118140960795 + 2557165 * 2 ^ 59
def prefixEnd_2557165 : Nat := 4983230072969 + 3 ^ 40 * 2557165 * 2
def baseEnd_2557165 : Nat := 875369838569728542584879

theorem tailTrace_2557165 : CollatzResearch.WordTrace tailWord_2557165 prefixEnd_2557165 875369838569728542584879 := by
  unfold tailWord_2557165
  simp only [CollatzResearch.WordTrace]
  refine ⟨93267469780835408857336949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62178313187223605904891299 93267469780835408857336949)
  ·
    refine ⟨8743825291953319580375339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93267469780835408857336949 8743825291953319580375339)
    ·
      refine ⟨13115737937929979370563009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743825291953319580375339 13115737937929979370563009)
      ·
        refine ⟨9836803453447484527922257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13115737937929979370563009 9836803453447484527922257)
        ·
          refine ⟨7377602590085613395941693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9836803453447484527922257 7377602590085613395941693)
          ·
            refine ⟨2766600971282105023478135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7377602590085613395941693 2766600971282105023478135)
            ·
              refine ⟨4149901456923157535217203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766600971282105023478135 4149901456923157535217203)
              ·
                refine ⟨6224852185384736302825805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149901456923157535217203 6224852185384736302825805)
                ·
                  refine ⟨2334319569519276113559677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6224852185384736302825805 2334319569519276113559677)
                  ·
                    refine ⟨875369838569728542584879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334319569519276113559677 875369838569728542584879)
                    ·
                      rfl

theorem cell22_2557165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2557165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557165 prefixEnd_2557165 := by exact prefixLift 2557165
  have htrace : WordTrace (prefixWord ++ tailWord_2557165) baseStart_2557165 baseEnd_2557165 := by
    simpa [prefixWord, tailWord_2557165, baseEnd_2557165] using wordTrace_append hprefix tailTrace_2557165
  have hstable : (prefixWord ++ tailWord_2557165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557165).length < 2 ^ (prefixWord ++ tailWord_2557165).sum := by decide
  have hdescent : baseEnd_2557165 < baseStart_2557165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557189 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 8]
def baseStart_2557189 : Nat := 118140960795 + 2557189 * 2 ^ 59
def prefixEnd_2557189 : Nat := 4983230072969 + 3 ^ 40 * 2557189 * 2
def baseEnd_2557189 : Nat := 291792684753400159994935

theorem tailTrace_2557189 : CollatzResearch.WordTrace tailWord_2557189 prefixEnd_2557189 291792684753400159994935 := by
  unfold tailWord_2557189
  simp only [CollatzResearch.WordTrace]
  refine ⟨93268345132748460956210621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62178896755165640637473747 93268345132748460956210621)
  ·
    refine ⟨34975629424780672858578983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93268345132748460956210621 34975629424780672858578983)
    ·
      refine ⟨52463444137171009287868475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34975629424780672858578983 52463444137171009287868475)
      ·
        refine ⟨78695166205756513931802713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52463444137171009287868475 78695166205756513931802713)
        ·
          refine ⟨59021374654317385448852035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78695166205756513931802713 59021374654317385448852035)
          ·
            refine ⟨88532061981476078173278053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59021374654317385448852035 88532061981476078173278053)
            ·
              refine ⟨16599761621526764657489635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88532061981476078173278053 16599761621526764657489635)
              ·
                refine ⟨24899642432290146986234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16599761621526764657489635 24899642432290146986234453)
                ·
                  refine ⟨291792684753400159994935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24899642432290146986234453 291792684753400159994935)
                  ·
                    rfl

theorem cell22_2557189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_2557189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557189 prefixEnd_2557189 := by exact prefixLift 2557189
  have htrace : WordTrace (prefixWord ++ tailWord_2557189) baseStart_2557189 baseEnd_2557189 := by
    simpa [prefixWord, tailWord_2557189, baseEnd_2557189] using wordTrace_append hprefix tailTrace_2557189
  have hstable : (prefixWord ++ tailWord_2557189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557189).length < 2 ^ (prefixWord ++ tailWord_2557189).sum := by decide
  have hdescent : baseEnd_2557189 < baseStart_2557189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557283 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 3, 3]
def baseStart_2557283 : Nat := 118140960795 + 2557283 * 2 ^ 59
def prefixEnd_2557283 : Nat := 4983230072969 + 3 ^ 40 * 2557283 * 2
def baseEnd_2557283 : Nat := 875410232381215568134517

theorem tailTrace_2557283 : CollatzResearch.WordTrace tailWord_2557283 prefixEnd_2557283 875410232381215568134517 := by
  unfold tailWord_2557283
  simp only [CollatzResearch.WordTrace]
  refine ⟨93271773594407915010132503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62181182396271943340088335 93271773594407915010132503)
  ·
    refine ⟨139907660391611872515198755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93271773594407915010132503 139907660391611872515198755)
    ·
      refine ⟨209861490587417808772798133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139907660391611872515198755 209861490587417808772798133)
      ·
        refine ⟨19674514742570419572449825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209861490587417808772798133 19674514742570419572449825)
        ·
          refine ⟨14755886056927814679337369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19674514742570419572449825 14755886056927814679337369)
          ·
            refine ⟨11066914542695861009503027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14755886056927814679337369 11066914542695861009503027)
            ·
              refine ⟨16600371814043791514254541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11066914542695861009503027 16600371814043791514254541)
              ·
                refine ⟨6225139430266421817845453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16600371814043791514254541 6225139430266421817845453)
                ·
                  refine ⟨2334427286349908181692045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6225139430266421817845453 2334427286349908181692045)
                  ·
                    refine ⟨875410232381215568134517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334427286349908181692045 875410232381215568134517)
                    ·
                      rfl

theorem cell22_2557283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3].length) (baseStart_2557283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557283 prefixEnd_2557283 := by exact prefixLift 2557283
  have htrace : WordTrace (prefixWord ++ tailWord_2557283) baseStart_2557283 baseEnd_2557283 := by
    simpa [prefixWord, tailWord_2557283, baseEnd_2557283] using wordTrace_append hprefix tailTrace_2557283
  have hstable : (prefixWord ++ tailWord_2557283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557283).length < 2 ^ (prefixWord ++ tailWord_2557283).sum := by decide
  have hdescent : baseEnd_2557283 < baseStart_2557283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557373 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2557373 : Nat := 118140960795 + 2557373 * 2 ^ 59
def prefixEnd_2557373 : Nat := 4983230072969 + 3 ^ 40 * 2557373 * 2
def baseEnd_2557373 : Nat := 875441041220485333384241

theorem tailTrace_2557373 : CollatzResearch.WordTrace tailWord_2557373 prefixEnd_2557373 875441041220485333384241 := by
  unfold tailWord_2557373
  simp only [CollatzResearch.WordTrace]
  refine ⟨93275056164081860380908773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62183370776054573587272515 93275056164081860380908773)
  ·
    refine ⟨17489073030765348821420395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93275056164081860380908773 17489073030765348821420395)
    ·
      refine ⟨26233609546148023232130593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17489073030765348821420395 26233609546148023232130593)
      ·
        refine ⟨19675207159611017424097945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26233609546148023232130593 19675207159611017424097945)
        ·
          refine ⟨14756405369708263068073459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19675207159611017424097945 14756405369708263068073459)
          ·
            refine ⟨22134608054562394602110189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14756405369708263068073459 22134608054562394602110189)
            ·
              refine ⟨8300478020460897975791321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22134608054562394602110189 8300478020460897975791321)
              ·
                refine ⟨6225358515345673481843491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8300478020460897975791321 6225358515345673481843491)
                ·
                  refine ⟨9338037773018510222765237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225358515345673481843491 9338037773018510222765237)
                  ·
                    refine ⟨875441041220485333384241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9338037773018510222765237 875441041220485333384241)
                    ·
                      rfl

theorem cell22_2557373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2557373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557373 prefixEnd_2557373 := by exact prefixLift 2557373
  have htrace : WordTrace (prefixWord ++ tailWord_2557373) baseStart_2557373 baseEnd_2557373 := by
    simpa [prefixWord, tailWord_2557373, baseEnd_2557373] using wordTrace_append hprefix tailTrace_2557373
  have hstable : (prefixWord ++ tailWord_2557373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557373).length < 2 ^ (prefixWord ++ tailWord_2557373).sum := by decide
  have hdescent : baseEnd_2557373 < baseStart_2557373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557386 : List Nat := [3, 1, 2, 1, 2, 13]
def baseStart_2557386 : Nat := 118140960795 + 2557386 * 2 ^ 59
def prefixEnd_2557386 : Nat := 4983230072969 + 3 ^ 40 * 2557386 * 2
def baseEnd_2557386 : Nat := 10807969029458736207521

theorem tailTrace_2557386 : CollatzResearch.WordTrace tailWord_2557386 prefixEnd_2557386 10807969029458736207521 := by
  unfold tailWord_2557386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23318882578258690900283003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62183686875356509067421341 23318882578258690900283003)
  ·
    refine ⟨34978323867388036350424505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23318882578258690900283003 34978323867388036350424505)
    ·
      refine ⟨26233742900541027262818379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34978323867388036350424505 26233742900541027262818379)
      ·
        refine ⟨39350614350811540894227569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26233742900541027262818379 39350614350811540894227569)
        ·
          refine ⟨29512960763108655670670677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39350614350811540894227569 29512960763108655670670677)
          ·
            refine ⟨10807969029458736207521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 29512960763108655670670677 10807969029458736207521)
            ·
              rfl

theorem cell22_2557386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 13].length) (baseStart_2557386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557386 prefixEnd_2557386 := by exact prefixLift 2557386
  have htrace : WordTrace (prefixWord ++ tailWord_2557386) baseStart_2557386 baseEnd_2557386 := by
    simpa [prefixWord, tailWord_2557386, baseEnd_2557386] using wordTrace_append hprefix tailTrace_2557386
  have hstable : (prefixWord ++ tailWord_2557386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557386).length < 2 ^ (prefixWord ++ tailWord_2557386).sum := by decide
  have hdescent : baseEnd_2557386 < baseStart_2557386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557390 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2557390 : Nat := 118140960795 + 2557390 * 2 ^ 59
def prefixEnd_2557390 : Nat := 4983230072969 + 3 ^ 40 * 2557390 * 2
def baseEnd_2557390 : Nat := 875446860667902955709189

theorem tailTrace_2557390 : CollatzResearch.WordTrace tailWord_2557390 prefixEnd_2557390 875446860667902955709189 := by
  unfold tailWord_2557390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11659459525627534035534703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62183784136680181522851749 11659459525627534035534703)
  ·
    refine ⟨17489189288441301053302055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11659459525627534035534703 17489189288441301053302055)
    ·
      refine ⟨26233783932661951579953083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17489189288441301053302055 26233783932661951579953083)
      ·
        refine ⟨39350675898992927369929625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26233783932661951579953083 39350675898992927369929625)
        ·
          refine ⟨29513006924244695527447219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39350675898992927369929625 29513006924244695527447219)
          ·
            refine ⟨44269510386367043291170829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29513006924244695527447219 44269510386367043291170829)
            ·
              refine ⟨16601066394887641234189061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44269510386367043291170829 16601066394887641234189061)
              ·
                refine ⟨3112699949041432731410449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16601066394887641234189061 3112699949041432731410449)
                ·
                  refine ⟨2334524961781074548557837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112699949041432731410449 2334524961781074548557837)
                  ·
                    refine ⟨875446860667902955709189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334524961781074548557837 875446860667902955709189)
                    ·
                      rfl

theorem cell22_2557390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2557390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557390 prefixEnd_2557390 := by exact prefixLift 2557390
  have htrace : WordTrace (prefixWord ++ tailWord_2557390) baseStart_2557390 baseEnd_2557390 := by
    simpa [prefixWord, tailWord_2557390, baseEnd_2557390] using wordTrace_append hprefix tailTrace_2557390
  have hstable : (prefixWord ++ tailWord_2557390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557390).length < 2 ^ (prefixWord ++ tailWord_2557390).sum := by decide
  have hdescent : baseEnd_2557390 < baseStart_2557390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557452 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_2557452 : Nat := 118140960795 + 2557452 * 2 ^ 59
def prefixEnd_2557452 : Nat := 4983230072969 + 3 ^ 40 * 2557452 * 2
def baseEnd_2557452 : Nat := 875468084534955460658999

theorem tailTrace_2557452 : CollatzResearch.WordTrace tailWord_2557452 prefixEnd_2557452 875468084534955460658999 := by
  unfold tailWord_2557452
  simp only [CollatzResearch.WordTrace]
  refine ⟨46638968765397828436517305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62185291687197104582023073 46638968765397828436517305)
  ·
    refine ⟨34979226574048371327387979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46638968765397828436517305 34979226574048371327387979)
    ·
      refine ⟨52468839861072556991081969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34979226574048371327387979 52468839861072556991081969)
      ·
        refine ⟨39351629895804417743311477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52468839861072556991081969 39351629895804417743311477)
        ·
          refine ⟨3689215302731664163435451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39351629895804417743311477 3689215302731664163435451)
          ·
            refine ⟨5533822954097496245153177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689215302731664163435451 5533822954097496245153177)
            ·
              refine ⟨4150367215573122183864883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5533822954097496245153177 4150367215573122183864883)
              ·
                refine ⟨6225550823359683275797325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150367215573122183864883 6225550823359683275797325)
                ·
                  refine ⟨2334581558759881228423997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6225550823359683275797325 2334581558759881228423997)
                  ·
                    refine ⟨875468084534955460658999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334581558759881228423997 875468084534955460658999)
                    ·
                      rfl

theorem cell22_2557452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_2557452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557452 prefixEnd_2557452 := by exact prefixLift 2557452
  have htrace : WordTrace (prefixWord ++ tailWord_2557452) baseStart_2557452 baseEnd_2557452 := by
    simpa [prefixWord, tailWord_2557452, baseEnd_2557452] using wordTrace_append hprefix tailTrace_2557452
  have hstable : (prefixWord ++ tailWord_2557452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557452).length < 2 ^ (prefixWord ++ tailWord_2557452).sum := by decide
  have hdescent : baseEnd_2557452 < baseStart_2557452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557486 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2557486 : Nat := 118140960795 + 2557486 * 2 ^ 59
def prefixEnd_2557486 : Nat := 4983230072969 + 3 ^ 40 * 2557486 * 2
def baseEnd_2557486 : Nat := 875479723429790705308895

theorem tailTrace_2557486 : CollatzResearch.WordTrace tailWord_2557486 prefixEnd_2557486 875479723429790705308895 := by
  unfold tailWord_2557486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11659897201584060084971539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62186118408448320453181541 11659897201584060084971539)
  ·
    refine ⟨17489845802376090127457309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11659897201584060084971539 17489845802376090127457309)
    ·
      refine ⟨6558692175891033797796491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17489845802376090127457309 6558692175891033797796491)
      ·
        refine ⟨9838038263836550696694737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558692175891033797796491 9838038263836550696694737)
        ·
          refine ⟨7378528697877413022521053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9838038263836550696694737 7378528697877413022521053)
          ·
            refine ⟨2766948261704029883445395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7378528697877413022521053 2766948261704029883445395)
            ·
              refine ⟨4150422392556044825168093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766948261704029883445395 4150422392556044825168093)
              ·
                refine ⟨1556408397208516809438035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4150422392556044825168093 1556408397208516809438035)
                ·
                  refine ⟨2334612595812775214157053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556408397208516809438035 2334612595812775214157053)
                  ·
                    refine ⟨875479723429790705308895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334612595812775214157053 875479723429790705308895)
                    ·
                      rfl

theorem cell22_2557486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2557486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557486 prefixEnd_2557486 := by exact prefixLift 2557486
  have htrace : WordTrace (prefixWord ++ tailWord_2557486) baseStart_2557486 baseEnd_2557486 := by
    simpa [prefixWord, tailWord_2557486, baseEnd_2557486] using wordTrace_append hprefix tailTrace_2557486
  have hstable : (prefixWord ++ tailWord_2557486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557486).length < 2 ^ (prefixWord ++ tailWord_2557486).sum := by decide
  have hdescent : baseEnd_2557486 < baseStart_2557486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557495 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2557495 : Nat := 118140960795 + 2557495 * 2 ^ 59
def prefixEnd_2557495 : Nat := 4983230072969 + 3 ^ 40 * 2557495 * 2
def baseEnd_2557495 : Nat := 875482804313717681833867

theorem tailTrace_2557495 : CollatzResearch.WordTrace tailWord_2557495 prefixEnd_2557495 875482804313717681833867 := by
  unfold tailWord_2557495
  simp only [CollatzResearch.WordTrace]
  refine ⟨93279505869639875216849939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62186337246426583477899959 93279505869639875216849939)
  ·
    refine ⟨139919258804459812825274909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93279505869639875216849939 139919258804459812825274909)
    ·
      refine ⟨52469722051672429809478091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139919258804459812825274909 52469722051672429809478091)
      ·
        refine ⟨78704583077508644714217137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52469722051672429809478091 78704583077508644714217137)
        ·
          refine ⟨59028437308131483535662853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78704583077508644714217137 59028437308131483535662853)
          ·
            refine ⟨11067831995274653162936785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59028437308131483535662853 11067831995274653162936785)
            ·
              refine ⟨8300873996455989872202589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11067831995274653162936785 8300873996455989872202589)
              ·
                refine ⟨3112827748670996202075971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8300873996455989872202589 3112827748670996202075971)
                ·
                  refine ⟨4669241623006494303113957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112827748670996202075971 4669241623006494303113957)
                  ·
                    refine ⟨875482804313717681833867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669241623006494303113957 875482804313717681833867)
                    ·
                      rfl

theorem cell22_2557495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2557495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557495 prefixEnd_2557495 := by exact prefixLift 2557495
  have htrace : WordTrace (prefixWord ++ tailWord_2557495) baseStart_2557495 baseEnd_2557495 := by
    simpa [prefixWord, tailWord_2557495, baseEnd_2557495] using wordTrace_append hprefix tailTrace_2557495
  have hstable : (prefixWord ++ tailWord_2557495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557495).length < 2 ^ (prefixWord ++ tailWord_2557495).sum := by decide
  have hdescent : baseEnd_2557495 < baseStart_2557495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557540 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_2557540 : Nat := 118140960795 + 2557540 * 2 ^ 59
def prefixEnd_2557540 : Nat := 4983230072969 + 3 ^ 40 * 2557540 * 2
def baseEnd_2557540 : Nat := 875498208733352564458729

theorem tailTrace_2557540 : CollatzResearch.WordTrace tailWord_2557540 prefixEnd_2557540 875498208733352564458729 := by
  unfold tailWord_2557540
  simp only [CollatzResearch.WordTrace]
  refine ⟨46640573577238423951119037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62187431436317898601492049 46640573577238423951119037)
  ·
    refine ⟨17490215091464408981669639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46640573577238423951119037 17490215091464408981669639)
    ·
      refine ⟨26235322637196613472504459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17490215091464408981669639 26235322637196613472504459)
      ·
        refine ⟨39352983955794920208756689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26235322637196613472504459 39352983955794920208756689)
        ·
          refine ⟨29514737966846190156567517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39352983955794920208756689 29514737966846190156567517)
          ·
            refine ⟨11068026737567321308712819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29514737966846190156567517 11068026737567321308712819)
            ·
              refine ⟨16602040106350981963069229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068026737567321308712819 16602040106350981963069229)
              ·
                refine ⟨6225765039881618236150961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16602040106350981963069229 6225765039881618236150961)
                ·
                  refine ⟨4669323779911213677113221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6225765039881618236150961 4669323779911213677113221)
                  ·
                    refine ⟨875498208733352564458729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669323779911213677113221 875498208733352564458729)
                    ·
                      rfl

theorem cell22_2557540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_2557540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557540 prefixEnd_2557540 := by exact prefixLift 2557540
  have htrace : WordTrace (prefixWord ++ tailWord_2557540) baseStart_2557540 baseEnd_2557540 := by
    simpa [prefixWord, tailWord_2557540, baseEnd_2557540] using wordTrace_append hprefix tailTrace_2557540
  have hstable : (prefixWord ++ tailWord_2557540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557540).length < 2 ^ (prefixWord ++ tailWord_2557540).sum := by decide
  have hdescent : baseEnd_2557540 < baseStart_2557540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557557 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2557557 : Nat := 118140960795 + 2557557 * 2 ^ 59
def prefixEnd_2557557 : Nat := 4983230072969 + 3 ^ 40 * 2557557 * 2
def baseEnd_2557557 : Nat := 875504028180770186783677

theorem tailTrace_2557557 : CollatzResearch.WordTrace tailWord_2557557 prefixEnd_2557557 875504028180770186783677 := by
  unfold tailWord_2557557
  simp only [CollatzResearch.WordTrace]
  refine ⟨93281767195415259805606925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62187844796943506537071283 93281767195415259805606925)
  ·
    refine ⟨34980662698280722427102597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93281767195415259805606925 34980662698280722427102597)
    ·
      refine ⟨6558874255927635455081737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34980662698280722427102597 6558874255927635455081737)
      ·
        refine ⟨4919155691945726591311303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6558874255927635455081737 4919155691945726591311303)
        ·
          refine ⟨7378733537918589886966955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919155691945726591311303 7378733537918589886966955)
          ·
            refine ⟨11068100306877884830450433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7378733537918589886966955 11068100306877884830450433)
            ·
              refine ⟨8301075230158413622837825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068100306877884830450433 8301075230158413622837825)
              ·
                refine ⟨6225806422618810217128369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8301075230158413622837825 6225806422618810217128369)
                ·
                  refine ⟨4669354816964107662846277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6225806422618810217128369 4669354816964107662846277)
                  ·
                    refine ⟨875504028180770186783677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669354816964107662846277 875504028180770186783677)
                    ·
                      rfl

theorem cell22_2557557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2557557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557557 prefixEnd_2557557 := by exact prefixLift 2557557
  have htrace : WordTrace (prefixWord ++ tailWord_2557557) baseStart_2557557 baseEnd_2557557 := by
    simpa [prefixWord, tailWord_2557557, baseEnd_2557557] using wordTrace_append hprefix tailTrace_2557557
  have hstable : (prefixWord ++ tailWord_2557557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557557).length < 2 ^ (prefixWord ++ tailWord_2557557).sum := by decide
  have hdescent : baseEnd_2557557 < baseStart_2557557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557568 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_2557568 : Nat := 118140960795 + 2557568 * 2 ^ 59
def prefixEnd_2557568 : Nat := 4983230072969 + 3 ^ 40 * 2557568 * 2
def baseEnd_2557568 : Nat := 875507793705569824758643

theorem tailTrace_2557568 : CollatzResearch.WordTrace tailWord_2557568 prefixEnd_2557568 875507793705569824758643 := by
  unfold tailWord_2557568
  simp only [CollatzResearch.WordTrace]
  refine ⟨46641084199187704342128679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62188112265583605789504905 46641084199187704342128679)
  ·
    refine ⟨69961626298781556513193019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46641084199187704342128679 69961626298781556513193019)
    ·
      refine ⟨104942439448172334769789529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69961626298781556513193019 104942439448172334769789529)
      ·
        refine ⟨78706829586129251077342147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104942439448172334769789529 78706829586129251077342147)
        ·
          refine ⟨118060244379193876616013221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78706829586129251077342147 118060244379193876616013221)
          ·
            refine ⟨22136295821098851865502479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118060244379193876616013221 22136295821098851865502479)
            ·
              refine ⟨33204443731648277798253719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22136295821098851865502479 33204443731648277798253719)
              ·
                refine ⟨49806665597472416697380579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33204443731648277798253719 49806665597472416697380579)
                ·
                  refine ⟨74709998396208625046070869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49806665597472416697380579 74709998396208625046070869)
                  ·
                    refine ⟨875507793705569824758643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74709998396208625046070869 875507793705569824758643)
                    ·
                      rfl

theorem cell22_2557568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_2557568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557568 prefixEnd_2557568 := by exact prefixLift 2557568
  have htrace : WordTrace (prefixWord ++ tailWord_2557568) baseStart_2557568 baseEnd_2557568 := by
    simpa [prefixWord, tailWord_2557568, baseEnd_2557568] using wordTrace_append hprefix tailTrace_2557568
  have hstable : (prefixWord ++ tailWord_2557568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557568).length < 2 ^ (prefixWord ++ tailWord_2557568).sum := by decide
  have hdescent : baseEnd_2557568 < baseStart_2557568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557572 : List Nat := [2, 3, 2, 1, 4, 2, 1, 7]
def baseStart_2557572 : Nat := 118140960795 + 2557572 * 2 ^ 59
def prefixEnd_2557572 : Nat := 4983230072969 + 3 ^ 40 * 2557572 * 2
def baseEnd_2557572 : Nat := 97278795887479460850959

theorem tailTrace_2557572 : CollatzResearch.WordTrace tailWord_2557572 prefixEnd_2557572 97278795887479460850959 := by
  unfold tailWord_2557572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46641157145180458683701485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62188209526907278244935313 46641157145180458683701485)
  ·
    refine ⟨17490433929442672006388057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46641157145180458683701485 17490433929442672006388057)
    ·
      refine ⟨13117825447082004004791043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17490433929442672006388057 13117825447082004004791043)
      ·
        refine ⟨19676738170623006007186565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13117825447082004004791043 19676738170623006007186565)
        ·
          refine ⟨3689388406991813626347481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19676738170623006007186565 3689388406991813626347481)
          ·
            refine ⟨2767041305243860219760611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3689388406991813626347481 2767041305243860219760611)
            ·
              refine ⟨4150561957865790329640917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767041305243860219760611 4150561957865790329640917)
              ·
                refine ⟨97278795887479460850959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4150561957865790329640917 97278795887479460850959)
                ·
                  rfl

theorem cell22_2557572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_2557572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557572 prefixEnd_2557572 := by exact prefixLift 2557572
  have htrace : WordTrace (prefixWord ++ tailWord_2557572) baseStart_2557572 baseEnd_2557572 := by
    simpa [prefixWord, tailWord_2557572, baseEnd_2557572] using wordTrace_append hprefix tailTrace_2557572
  have hstable : (prefixWord ++ tailWord_2557572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557572).length < 2 ^ (prefixWord ++ tailWord_2557572).sum := by decide
  have hdescent : baseEnd_2557572 < baseStart_2557572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557604 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_2557604 : Nat := 118140960795 + 2557604 * 2 ^ 59
def prefixEnd_2557604 : Nat := 4983230072969 + 3 ^ 40 * 2557604 * 2
def baseEnd_2557604 : Nat := 875520117241277730858533

theorem tailTrace_2557604 : CollatzResearch.WordTrace tailWord_2557604 prefixEnd_2557604 875520117241277730858533 := by
  unfold tailWord_2557604
  simp only [CollatzResearch.WordTrace]
  refine ⟨46641740713122493416283933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62188987617496657888378577 46641740713122493416283933)
  ·
    refine ⟨17490652767420935031106475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46641740713122493416283933 17490652767420935031106475)
    ·
      refine ⟨26235979151131402546659713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17490652767420935031106475 26235979151131402546659713)
      ·
        refine ⟨19676984363348551909994785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26235979151131402546659713 19676984363348551909994785)
        ·
          refine ⟨14757738272511413932496089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19676984363348551909994785 14757738272511413932496089)
          ·
            refine ⟨11068303704383560449372067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14757738272511413932496089 11068303704383560449372067)
            ·
              refine ⟨16602455556575340674058101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068303704383560449372067 16602455556575340674058101)
              ·
                refine ⟨1556480208428938188192947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16602455556575340674058101 1556480208428938188192947)
                ·
                  refine ⟨2334720312643407282289421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556480208428938188192947 2334720312643407282289421)
                  ·
                    refine ⟨875520117241277730858533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334720312643407282289421 875520117241277730858533)
                    ·
                      rfl

theorem cell22_2557604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_2557604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557604 prefixEnd_2557604 := by exact prefixLift 2557604
  have htrace : WordTrace (prefixWord ++ tailWord_2557604) baseStart_2557604 baseEnd_2557604 := by
    simpa [prefixWord, tailWord_2557604, baseEnd_2557604] using wordTrace_append hprefix tailTrace_2557604
  have hstable : (prefixWord ++ tailWord_2557604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557604).length < 2 ^ (prefixWord ++ tailWord_2557604).sum := by decide
  have hdescent : baseEnd_2557604 < baseStart_2557604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557675 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_2557675 : Nat := 118140960795 + 2557675 * 2 ^ 59
def prefixEnd_2557675 : Nat := 4983230072969 + 3 ^ 40 * 2557675 * 2
def baseEnd_2557675 : Nat := 875544421992257212333315

theorem tailTrace_2557675 : CollatzResearch.WordTrace tailWord_2557675 prefixEnd_2557675 875544421992257212333315 := by
  unfold tailWord_2557675
  simp only [CollatzResearch.WordTrace]
  refine ⟨93286071008987765958402479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62190714005991843972268319 93286071008987765958402479)
  ·
    refine ⟨139929106513481648937603719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93286071008987765958402479 139929106513481648937603719)
    ·
      refine ⟨209893659770222473406405579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139929106513481648937603719 209893659770222473406405579)
      ·
        refine ⟨314840489655333710109608369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209893659770222473406405579 314840489655333710109608369)
        ·
          refine ⟨236130367241500282582206277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314840489655333710109608369 236130367241500282582206277)
          ·
            refine ⟨44274443857781302984163677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236130367241500282582206277 44274443857781302984163677)
            ·
              refine ⟨16602916446667988619061379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44274443857781302984163677 16602916446667988619061379)
              ·
                refine ⟨24904374670001982928592069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16602916446667988619061379 24904374670001982928592069)
                ·
                  refine ⟨4669570250625371799111013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24904374670001982928592069 4669570250625371799111013)
                  ·
                    refine ⟨875544421992257212333315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669570250625371799111013 875544421992257212333315)
                    ·
                      rfl

theorem cell22_2557675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_2557675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557675 prefixEnd_2557675 := by exact prefixLift 2557675
  have htrace : WordTrace (prefixWord ++ tailWord_2557675) baseStart_2557675 baseEnd_2557675 := by
    simpa [prefixWord, tailWord_2557675, baseEnd_2557675] using wordTrace_append hprefix tailTrace_2557675
  have hstable : (prefixWord ++ tailWord_2557675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557675).length < 2 ^ (prefixWord ++ tailWord_2557675).sum := by decide
  have hdescent : baseEnd_2557675 < baseStart_2557675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557679 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 4]
def baseStart_2557679 : Nat := 118140960795 + 2557679 * 2 ^ 59
def prefixEnd_2557679 : Nat := 4983230072969 + 3 ^ 40 * 2557679 * 2
def baseEnd_2557679 : Nat := 291848597091334178411101

theorem tailTrace_2557679 : CollatzResearch.WordTrace tailWord_2557679 prefixEnd_2557679 291848597091334178411101 := by
  unfold tailWord_2557679
  simp only [CollatzResearch.WordTrace]
  refine ⟨93286216900973274641548091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62190811267315516427698727 93286216900973274641548091)
  ·
    refine ⟨139929325351459911962322137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93286216900973274641548091 139929325351459911962322137)
    ·
      refine ⟨104946994013594933971741603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139929325351459911962322137 104946994013594933971741603)
      ·
        refine ⟨157420491020392400957612405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104946994013594933971741603 157420491020392400957612405)
        ·
          refine ⟨14758171033161787589776163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157420491020392400957612405 14758171033161787589776163)
          ·
            refine ⟨22137256549742681384664245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14758171033161787589776163 22137256549742681384664245)
            ·
              refine ⟨2075367801538376379812273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22137256549742681384664245 2075367801538376379812273)
              ·
                refine ⟨1556525851153782284859205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075367801538376379812273 1556525851153782284859205)
                ·
                  refine ⟨291848597091334178411101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556525851153782284859205 291848597091334178411101)
                  ·
                    rfl

theorem cell22_2557679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 4].length) (baseStart_2557679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557679 prefixEnd_2557679 := by exact prefixLift 2557679
  have htrace : WordTrace (prefixWord ++ tailWord_2557679) baseStart_2557679 baseEnd_2557679 := by
    simpa [prefixWord, tailWord_2557679, baseEnd_2557679] using wordTrace_append hprefix tailTrace_2557679
  have hstable : (prefixWord ++ tailWord_2557679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557679).length < 2 ^ (prefixWord ++ tailWord_2557679).sum := by decide
  have hdescent : baseEnd_2557679 < baseStart_2557679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557752 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_2557752 : Nat := 118140960795 + 2557752 * 2 ^ 59
def prefixEnd_2557752 : Nat := 4983230072969 + 3 ^ 40 * 2557752 * 2
def baseEnd_2557752 : Nat := 291856926888618226052693

theorem tailTrace_2557752 : CollatzResearch.WordTrace tailWord_2557752 prefixEnd_2557752 291856926888618226052693 := by
  unfold tailWord_2557752
  simp only [CollatzResearch.WordTrace]
  refine ⟨46644439714854404054477755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62192586286472538739303673 46644439714854404054477755)
  ·
    refine ⟨69966659572281606081716633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46644439714854404054477755 69966659572281606081716633)
    ·
      refine ⟨52474994679211204561287475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69966659572281606081716633 52474994679211204561287475)
      ·
        refine ⟨78712492018816806841931213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52474994679211204561287475 78712492018816806841931213)
        ·
          refine ⟨29517184507056302565724205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78712492018816806841931213 29517184507056302565724205)
          ·
            refine ⟨11068944190146113462146577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29517184507056302565724205 11068944190146113462146577)
            ·
              refine ⟨8301708142609585096609933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068944190146113462146577 8301708142609585096609933)
              ·
                refine ⟨3113140553478594411228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8301708142609585096609933 3113140553478594411228725)
                ·
                  refine ⟨291856926888618226052693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3113140553478594411228725 291856926888618226052693)
                  ·
                    rfl

theorem cell22_2557752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_2557752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557752 prefixEnd_2557752 := by exact prefixLift 2557752
  have htrace : WordTrace (prefixWord ++ tailWord_2557752) baseStart_2557752 baseEnd_2557752 := by
    simpa [prefixWord, tailWord_2557752, baseEnd_2557752] using wordTrace_append hprefix tailTrace_2557752
  have hstable : (prefixWord ++ tailWord_2557752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557752).length < 2 ^ (prefixWord ++ tailWord_2557752).sum := by decide
  have hdescent : baseEnd_2557752 < baseStart_2557752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557773 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2557773 : Nat := 118140960795 + 2557773 * 2 ^ 59
def prefixEnd_2557773 : Nat := 4983230072969 + 3 ^ 40 * 2557773 * 2
def baseEnd_2557773 : Nat := 875577969395017623383015

theorem tailTrace_2557773 : CollatzResearch.WordTrace tailWord_2557773 prefixEnd_2557773 875577969395017623383015 := by
  unfold tailWord_2557773
  simp only [CollatzResearch.WordTrace]
  refine ⟨93289645362632728695469973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62193096908421819130313315 93289645362632728695469973)
  ·
    refine ⟨4372952126373409157600155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93289645362632728695469973 4372952126373409157600155)
    ·
      refine ⟨6559428189560113736400233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372952126373409157600155 6559428189560113736400233)
      ·
        refine ⟨4919571142170085302300175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6559428189560113736400233 4919571142170085302300175)
        ·
          refine ⟨7379356713255127953450263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919571142170085302300175 7379356713255127953450263)
          ·
            refine ⟨11069035069882691930175395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379356713255127953450263 11069035069882691930175395)
            ·
              refine ⟨16603552604824037895263093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11069035069882691930175395 16603552604824037895263093)
              ·
                refine ⟨1556583056702253552680915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16603552604824037895263093 1556583056702253552680915)
                ·
                  refine ⟨2334874585053380329021373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556583056702253552680915 2334874585053380329021373)
                  ·
                    refine ⟨875577969395017623383015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334874585053380329021373 875577969395017623383015)
                    ·
                      rfl

theorem cell22_2557773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2557773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557773 prefixEnd_2557773 := by exact prefixLift 2557773
  have htrace : WordTrace (prefixWord ++ tailWord_2557773) baseStart_2557773 baseEnd_2557773 := by
    simpa [prefixWord, tailWord_2557773, baseEnd_2557773] using wordTrace_append hprefix tailTrace_2557773
  have hstable : (prefixWord ++ tailWord_2557773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557773).length < 2 ^ (prefixWord ++ tailWord_2557773).sum := by decide
  have hdescent : baseEnd_2557773 < baseStart_2557773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557827 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_2557827 : Nat := 118140960795 + 2557827 * 2 ^ 59
def prefixEnd_2557827 : Nat := 4983230072969 + 3 ^ 40 * 2557827 * 2
def baseEnd_2557827 : Nat := 875596454698579482532849

theorem tailTrace_2557827 : CollatzResearch.WordTrace tailWord_2557827 prefixEnd_2557827 875596454698579482532849 := by
  unfold tailWord_2557827
  simp only [CollatzResearch.WordTrace]
  refine ⟨93291614904437095917935735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62194409936291397278623823 93291614904437095917935735)
  ·
    refine ⟨139937422356655643876903603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93291614904437095917935735 139937422356655643876903603)
    ·
      refine ⟨209906133534983465815355405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139937422356655643876903603 209906133534983465815355405)
      ·
        refine ⟨78714800075618799680758277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209906133534983465815355405 78714800075618799680758277)
        ·
          refine ⟨14759025014178524940142177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78714800075618799680758277 14759025014178524940142177)
          ·
            refine ⟨11069268760633893705106633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14759025014178524940142177 11069268760633893705106633)
            ·
              refine ⟨8301951570475420278829975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11069268760633893705106633 8301951570475420278829975)
              ·
                refine ⟨12452927355713130418244963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8301951570475420278829975 12452927355713130418244963)
                ·
                  refine ⟨18679391033569695627367445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12452927355713130418244963 18679391033569695627367445)
                  ·
                    refine ⟨875596454698579482532849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18679391033569695627367445 875596454698579482532849)
                    ·
                      rfl

theorem cell22_2557827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_2557827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557827 prefixEnd_2557827 := by exact prefixLift 2557827
  have htrace : WordTrace (prefixWord ++ tailWord_2557827) baseStart_2557827 baseEnd_2557827 := by
    simpa [prefixWord, tailWord_2557827, baseEnd_2557827] using wordTrace_append hprefix tailTrace_2557827
  have hstable : (prefixWord ++ tailWord_2557827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557827).length < 2 ^ (prefixWord ++ tailWord_2557827).sum := by decide
  have hdescent : baseEnd_2557827 < baseStart_2557827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557844 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2557844 : Nat := 118140960795 + 2557844 * 2 ^ 59
def prefixEnd_2557844 : Nat := 4983230072969 + 3 ^ 40 * 2557844 * 2
def baseEnd_2557844 : Nat := 875602274145997104857797

theorem tailTrace_2557844 : CollatzResearch.WordTrace tailWord_2557844 prefixEnd_2557844 875602274145997104857797 := by
  unfold tailWord_2557844
  simp only [CollatzResearch.WordTrace]
  refine ⟨46646117472687753910652293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62194823296917005214203057 46646117472687753910652293)
  ·
    refine ⟨8746147026128953858247305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46646117472687753910652293 8746147026128953858247305)
    ·
      refine ⟨6559610269596715393685479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8746147026128953858247305 6559610269596715393685479)
      ·
        refine ⟨9839415404395073090528219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6559610269596715393685479 9839415404395073090528219)
        ·
          refine ⟨14759123106592609635792329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9839415404395073090528219 14759123106592609635792329)
          ·
            refine ⟨11069342329944457226844247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14759123106592609635792329 11069342329944457226844247)
            ·
              refine ⟨16604013494916685840266371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11069342329944457226844247 16604013494916685840266371)
              ·
                refine ⟨24906020242375028760399557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16604013494916685840266371 24906020242375028760399557)
                ·
                  refine ⟨4669878795445317892574917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24906020242375028760399557 4669878795445317892574917)
                  ·
                    refine ⟨875602274145997104857797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669878795445317892574917 875602274145997104857797)
                    ·
                      rfl

theorem cell22_2557844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2557844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557844 prefixEnd_2557844 := by exact prefixLift 2557844
  have htrace : WordTrace (prefixWord ++ tailWord_2557844) baseStart_2557844 baseEnd_2557844 := by
    simpa [prefixWord, tailWord_2557844, baseEnd_2557844] using wordTrace_append hprefix tailTrace_2557844
  have hstable : (prefixWord ++ tailWord_2557844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557844).length < 2 ^ (prefixWord ++ tailWord_2557844).sum := by decide
  have hdescent : baseEnd_2557844 < baseStart_2557844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557848 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_2557848 : Nat := 118140960795 + 2557848 * 2 ^ 59
def prefixEnd_2557848 : Nat := 4983230072969 + 3 ^ 40 * 2557848 * 2
def baseEnd_2557848 : Nat := 291867881142580809252595

theorem tailTrace_2557848 : CollatzResearch.WordTrace tailWord_2557848 prefixEnd_2557848 291867881142580809252595 := by
  unfold tailWord_2557848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46646190418680508252225099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62194920558240677669633465 46646190418680508252225099)
  ·
    refine ⟨69969285628020762378337649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46646190418680508252225099 69969285628020762378337649)
    ·
      refine ⟨52476964221015571783753237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69969285628020762378337649 52476964221015571783753237)
      ·
        refine ⟨2459857697860104927363433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52476964221015571783753237 2459857697860104927363433)
        ·
          refine ⟨1844893273395078695522575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459857697860104927363433 1844893273395078695522575)
          ·
            refine ⟨2767339910092618043283863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844893273395078695522575 2767339910092618043283863)
            ·
              refine ⟨4151009865138927064925795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767339910092618043283863 4151009865138927064925795)
              ·
                refine ⟨6226514797708390597388693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151009865138927064925795 6226514797708390597388693)
                ·
                  refine ⟨291867881142580809252595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6226514797708390597388693 291867881142580809252595)
                  ·
                    rfl

theorem cell22_2557848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_2557848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557848 prefixEnd_2557848 := by exact prefixLift 2557848
  have htrace : WordTrace (prefixWord ++ tailWord_2557848) baseStart_2557848 baseEnd_2557848 := by
    simpa [prefixWord, tailWord_2557848, baseEnd_2557848] using wordTrace_append hprefix tailTrace_2557848
  have hstable : (prefixWord ++ tailWord_2557848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557848).length < 2 ^ (prefixWord ++ tailWord_2557848).sum := by decide
  have hdescent : baseEnd_2557848 < baseStart_2557848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557863 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2557863 : Nat := 118140960795 + 2557863 * 2 ^ 59
def prefixEnd_2557863 : Nat := 4983230072969 + 3 ^ 40 * 2557863 * 2
def baseEnd_2557863 : Nat := 875608778234287388632739

theorem tailTrace_2557863 : CollatzResearch.WordTrace tailWord_2557863 prefixEnd_2557863 875608778234287388632739 := by
  unfold tailWord_2557863
  simp only [CollatzResearch.WordTrace]
  refine ⟨93292927932306674066246243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62195285288204449377497495 93292927932306674066246243)
  ·
    refine ⟨139939391898460011099369365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93292927932306674066246243 139939391898460011099369365)
    ·
      refine ⟨6559658995240313020282939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139939391898460011099369365 6559658995240313020282939)
      ·
        refine ⟨9839488492860469530424409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6559658995240313020282939 9839488492860469530424409)
        ·
          refine ⟨7379616369645352147818307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9839488492860469530424409 7379616369645352147818307)
          ·
            refine ⟨11069424554468028221727461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379616369645352147818307 11069424554468028221727461)
            ·
              refine ⟨2075517103962755291573899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11069424554468028221727461 2075517103962755291573899)
              ·
                refine ⟨3113275655944132937360849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075517103962755291573899 3113275655944132937360849)
                ·
                  refine ⟨2334956741958099703020637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113275655944132937360849 2334956741958099703020637)
                  ·
                    refine ⟨875608778234287388632739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334956741958099703020637 875608778234287388632739)
                    ·
                      rfl

theorem cell22_2557863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2557863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557863 prefixEnd_2557863 := by exact prefixLift 2557863
  have htrace : WordTrace (prefixWord ++ tailWord_2557863) baseStart_2557863 baseEnd_2557863 := by
    simpa [prefixWord, tailWord_2557863, baseEnd_2557863] using wordTrace_append hprefix tailTrace_2557863
  have hstable : (prefixWord ++ tailWord_2557863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557863).length < 2 ^ (prefixWord ++ tailWord_2557863).sum := by decide
  have hdescent : baseEnd_2557863 < baseStart_2557863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557874 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_2557874 : Nat := 118140960795 + 2557874 * 2 ^ 59
def prefixEnd_2557874 : Nat := 4983230072969 + 3 ^ 40 * 2557874 * 2
def baseEnd_2557874 : Nat := 875612543759087026607705

theorem tailTrace_2557874 : CollatzResearch.WordTrace tailWord_2557874 prefixEnd_2557874 875612543759087026607705 := by
  unfold tailWord_2557874
  simp only [CollatzResearch.WordTrace]
  refine ⟨23323332283816705736224169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62195552756844548629931117 23323332283816705736224169)
  ·
    refine ⟨17492499212862529302168127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23323332283816705736224169 17492499212862529302168127)
    ·
      refine ⟨26238748819293793953252191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17492499212862529302168127 26238748819293793953252191)
      ·
        refine ⟨39358123228940690929878287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26238748819293793953252191 39358123228940690929878287)
        ·
          refine ⟨59037184843411036394817431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39358123228940690929878287 59037184843411036394817431)
          ·
            refine ⟨88555777265116554592226147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59037184843411036394817431 88555777265116554592226147)
            ·
              refine ⟨132833665897674831888339221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88555777265116554592226147 132833665897674831888339221)
              ·
                refine ⟨6226578088953507744765901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132833665897674831888339221 6226578088953507744765901)
                ·
                  refine ⟨2334966783357565404287213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6226578088953507744765901 2334966783357565404287213)
                  ·
                    refine ⟨875612543759087026607705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334966783357565404287213 875612543759087026607705)
                    ·
                      rfl

theorem cell22_2557874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_2557874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557874 prefixEnd_2557874 := by exact prefixLift 2557874
  have htrace : WordTrace (prefixWord ++ tailWord_2557874) baseStart_2557874 baseEnd_2557874 := by
    simpa [prefixWord, tailWord_2557874, baseEnd_2557874] using wordTrace_append hprefix tailTrace_2557874
  have hstable : (prefixWord ++ tailWord_2557874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557874).length < 2 ^ (prefixWord ++ tailWord_2557874).sum := by decide
  have hdescent : baseEnd_2557874 < baseStart_2557874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557908 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2557908 : Nat := 118140960795 + 2557908 * 2 ^ 59
def prefixEnd_2557908 : Nat := 4983230072969 + 3 ^ 40 * 2557908 * 2
def baseEnd_2557908 : Nat := 875624182653922271257601

theorem tailTrace_2557908 : CollatzResearch.WordTrace tailWord_2557908 prefixEnd_2557908 875624182653922271257601 := by
  unfold tailWord_2557908
  simp only [CollatzResearch.WordTrace]
  refine ⟨46647284608571823375817189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62196379478095764501089585 46647284608571823375817189)
  ·
    refine ⟨8746365864107216882965723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46647284608571823375817189 8746365864107216882965723)
    ·
      refine ⟨13119548796160825324448585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8746365864107216882965723 13119548796160825324448585)
      ·
        refine ⟨9839661597120618993336439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13119548796160825324448585 9839661597120618993336439)
        ·
          refine ⟨14759492395680928490004659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9839661597120618993336439 14759492395680928490004659)
          ·
            refine ⟨22139238593521392735006989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14759492395680928490004659 22139238593521392735006989)
            ·
              refine ⟨8302214472570522275627621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22139238593521392735006989 8302214472570522275627621)
              ·
                refine ⟨1556665213606972926680179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8302214472570522275627621 1556665213606972926680179)
                ·
                  refine ⟨2334997820410459390020269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556665213606972926680179 2334997820410459390020269)
                  ·
                    refine ⟨875624182653922271257601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2334997820410459390020269 875624182653922271257601)
                    ·
                      rfl

theorem cell22_2557908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2557908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557908 prefixEnd_2557908 := by exact prefixLift 2557908
  have htrace : WordTrace (prefixWord ++ tailWord_2557908) baseStart_2557908 baseEnd_2557908 := by
    simpa [prefixWord, tailWord_2557908, baseEnd_2557908] using wordTrace_append hprefix tailTrace_2557908
  have hstable : (prefixWord ++ tailWord_2557908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557908).length < 2 ^ (prefixWord ++ tailWord_2557908).sum := by decide
  have hdescent : baseEnd_2557908 < baseStart_2557908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557919 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_2557919 : Nat := 118140960795 + 2557919 * 2 ^ 59
def prefixEnd_2557919 : Nat := 4983230072969 + 3 ^ 40 * 2557919 * 2
def baseEnd_2557919 : Nat := 875627948178721909232567

theorem tailTrace_2557919 : CollatzResearch.WordTrace tailWord_2557919 prefixEnd_2557919 875627948178721909232567 := by
  unfold tailWord_2557919
  simp only [CollatzResearch.WordTrace]
  refine ⟨93294970420103795630284811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62196646946735863753523207 93294970420103795630284811)
  ·
    refine ⟨139942455630155693445427217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93294970420103795630284811 139942455630155693445427217)
    ·
      refine ⟨104956841722616770084070413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139942455630155693445427217 104956841722616770084070413)
      ·
        refine ⟨39358815645981288781526405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104956841722616770084070413 39358815645981288781526405)
        ·
          refine ⟨7379777933621491646536201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39358815645981288781526405 7379777933621491646536201)
          ·
            refine ⟨5534833450216118734902151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7379777933621491646536201 5534833450216118734902151)
            ·
              refine ⟨8302250175324178102353227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534833450216118734902151 8302250175324178102353227)
              ·
                refine ⟨12453375262986267153529841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8302250175324178102353227 12453375262986267153529841)
                ·
                  refine ⟨9340031447239700365147381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12453375262986267153529841 9340031447239700365147381)
                  ·
                    refine ⟨875627948178721909232567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9340031447239700365147381 875627948178721909232567)
                    ·
                      rfl

theorem cell22_2557919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_2557919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557919 prefixEnd_2557919 := by exact prefixLift 2557919
  have htrace : WordTrace (prefixWord ++ tailWord_2557919) baseStart_2557919 baseEnd_2557919 := by
    simpa [prefixWord, tailWord_2557919, baseEnd_2557919] using wordTrace_append hprefix tailTrace_2557919
  have hstable : (prefixWord ++ tailWord_2557919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557919).length < 2 ^ (prefixWord ++ tailWord_2557919).sum := by decide
  have hdescent : baseEnd_2557919 < baseStart_2557919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557966 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_2557966 : Nat := 118140960795 + 2557966 * 2 ^ 59
def prefixEnd_2557966 : Nat := 4983230072969 + 3 ^ 40 * 2557966 * 2
def baseEnd_2557966 : Nat := 291881345746409817769141

theorem tailTrace_2557966 : CollatzResearch.WordTrace tailWord_2557966 prefixEnd_2557966 291881345746409817769141 := by
  unfold tailWord_2557966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662085581366690332155719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62197789767289015104830501 11662085581366690332155719)
  ·
    refine ⟨17493128372050035498233579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11662085581366690332155719 17493128372050035498233579)
    ·
      refine ⟨26239692558075053247350369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17493128372050035498233579 26239692558075053247350369)
      ·
        refine ⟨19679769418556289935512777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26239692558075053247350369 19679769418556289935512777)
        ·
          refine ⟨14759827063917217451634583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19679769418556289935512777 14759827063917217451634583)
          ·
            refine ⟨22139740595875826177451875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14759827063917217451634583 22139740595875826177451875)
            ·
              refine ⟨33209610893813739266177813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22139740595875826177451875 33209610893813739266177813)
              ·
                refine ⟨1556700510647519028102085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33209610893813739266177813 1556700510647519028102085)
                ·
                  refine ⟨291881345746409817769141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556700510647519028102085 291881345746409817769141)
                  ·
                    rfl

theorem cell22_2557966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_2557966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557966 prefixEnd_2557966 := by exact prefixLift 2557966
  have htrace : WordTrace (prefixWord ++ tailWord_2557966) baseStart_2557966 baseEnd_2557966 := by
    simpa [prefixWord, tailWord_2557966, baseEnd_2557966] using wordTrace_append hprefix tailTrace_2557966
  have hstable : (prefixWord ++ tailWord_2557966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557966).length < 2 ^ (prefixWord ++ tailWord_2557966).sum := by decide
  have hdescent : baseEnd_2557966 < baseStart_2557966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557977 : List Nat := [1, 2, 1, 2, 1, 1, 3, 11]
def baseStart_2557977 : Nat := 118140960795 + 2557977 * 2 ^ 59
def prefixEnd_2557977 : Nat := 4983230072969 + 3 ^ 40 * 2557977 * 2
def baseEnd_2557977 : Nat := 97294200307114343475821

theorem tailTrace_2557977 : CollatzResearch.WordTrace tailWord_2557977 prefixEnd_2557977 97294200307114343475821 := by
  unfold tailWord_2557977
  simp only [CollatzResearch.WordTrace]
  refine ⟨93297085853893671535896185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62198057235929114357264123 93297085853893671535896185)
  ·
    refine ⟨69972814390420253651922139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93297085853893671535896185 69972814390420253651922139)
    ·
      refine ⟨104959221585630380477883209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69972814390420253651922139 104959221585630380477883209)
      ·
        refine ⟨78719416189222785358412407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104959221585630380477883209 78719416189222785358412407)
        ·
          refine ⟨118079124283834178037618611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78719416189222785358412407 118079124283834178037618611)
          ·
            refine ⟨177118686425751267056427917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118079124283834178037618611 177118686425751267056427917)
            ·
              refine ⟨66419507409656725146160469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177118686425751267056427917 66419507409656725146160469)
              ·
                refine ⟨97294200307114343475821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66419507409656725146160469 97294200307114343475821)
                ·
                  rfl

theorem cell22_2557977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 11].length) (baseStart_2557977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557977 prefixEnd_2557977 := by exact prefixLift 2557977
  have htrace : WordTrace (prefixWord ++ tailWord_2557977) baseStart_2557977 baseEnd_2557977 := by
    simpa [prefixWord, tailWord_2557977, baseEnd_2557977] using wordTrace_append hprefix tailTrace_2557977
  have hstable : (prefixWord ++ tailWord_2557977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557977).length < 2 ^ (prefixWord ++ tailWord_2557977).sum := by decide
  have hdescent : baseEnd_2557977 < baseStart_2557977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557981 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2557981 : Nat := 118140960795 + 2557981 * 2 ^ 59
def prefixEnd_2557981 : Nat := 4983230072969 + 3 ^ 40 * 2557981 * 2
def baseEnd_2557981 : Nat := 875649172045774414182377

theorem tailTrace_2557981 : CollatzResearch.WordTrace tailWord_2557981 prefixEnd_2557981 875649172045774414182377 := by
  unfold tailWord_2557981
  simp only [CollatzResearch.WordTrace]
  refine ⟨93297231745879180219041797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62198154497252786812694531 93297231745879180219041797)
  ·
    refine ⟨17493230952352346291070337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93297231745879180219041797 17493230952352346291070337)
    ·
      refine ⟨13119923214264259718302753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17493230952352346291070337 13119923214264259718302753)
      ·
        refine ⟨9839942410698194788727065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13119923214264259718302753 9839942410698194788727065)
        ·
          refine ⟨7379956808023646091545299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9839942410698194788727065 7379956808023646091545299)
          ·
            refine ⟨11069935212035469137317949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379956808023646091545299 11069935212035469137317949)
            ·
              refine ⟨4151225704513300926494231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11069935212035469137317949 4151225704513300926494231)
              ·
                refine ⟨6226838556769951389741347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151225704513300926494231 6226838556769951389741347)
                ·
                  refine ⟨9340257835154927084612021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226838556769951389741347 9340257835154927084612021)
                  ·
                    refine ⟨875649172045774414182377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9340257835154927084612021 875649172045774414182377)
                    ·
                      rfl

theorem cell22_2557981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2557981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2557981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2557981 prefixEnd_2557981 := by exact prefixLift 2557981
  have htrace : WordTrace (prefixWord ++ tailWord_2557981) baseStart_2557981 baseEnd_2557981 := by
    simpa [prefixWord, tailWord_2557981, baseEnd_2557981] using wordTrace_append hprefix tailTrace_2557981
  have hstable : (prefixWord ++ tailWord_2557981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557981).length < 2 ^ (prefixWord ++ tailWord_2557981).sum := by decide
  have hdescent : baseEnd_2557981 < baseStart_2557981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558077 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_2558077 : Nat := 118140960795 + 2558077 * 2 ^ 59
def prefixEnd_2558077 : Nat := 4983230072969 + 3 ^ 40 * 2558077 * 2
def baseEnd_2558077 : Nat := 875682034807662163782083

theorem tailTrace_2558077 : CollatzResearch.WordTrace tailWord_2558077 prefixEnd_2558077 875682034807662163782083 := by
  unfold tailWord_2558077
  simp only [CollatzResearch.WordTrace]
  refine ⟨93300733153531388614536485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62200488769020925743024323 93300733153531388614536485)
  ·
    refine ⟨17493887466287135365225591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93300733153531388614536485 17493887466287135365225591)
    ·
      refine ⟨26240831199430703047838387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17493887466287135365225591 26240831199430703047838387)
      ·
        refine ⟨39361246799146054571757581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26240831199430703047838387 39361246799146054571757581)
        ·
          refine ⟨14760467549679770464409093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39361246799146054571757581 14760467549679770464409093)
          ·
            refine ⟨2767587665564956962076705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14760467549679770464409093 2767587665564956962076705)
            ·
              refine ⟨2075690749173717721557529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767587665564956962076705 2075690749173717721557529)
              ·
                refine ⟨1556768061880288291168147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075690749173717721557529 1556768061880288291168147)
                ·
                  refine ⟨2335152092820432436752221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556768061880288291168147 2335152092820432436752221)
                  ·
                    refine ⟨875682034807662163782083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335152092820432436752221 875682034807662163782083)
                    ·
                      rfl

theorem cell22_2558077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_2558077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558077 prefixEnd_2558077 := by exact prefixLift 2558077
  have htrace : WordTrace (prefixWord ++ tailWord_2558077) baseStart_2558077 baseEnd_2558077 := by
    simpa [prefixWord, tailWord_2558077, baseEnd_2558077] using wordTrace_append hprefix tailTrace_2558077
  have hstable : (prefixWord ++ tailWord_2558077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558077).length < 2 ^ (prefixWord ++ tailWord_2558077).sum := by decide
  have hdescent : baseEnd_2558077 < baseStart_2558077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558191 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 7]
def baseStart_2558191 : Nat := 118140960795 + 2558191 * 2 ^ 59
def prefixEnd_2558191 : Nat := 4983230072969 + 3 ^ 40 * 2558191 * 2
def baseEnd_2558191 : Nat := 291907019779134622143911

theorem tailTrace_2558191 : CollatzResearch.WordTrace tailWord_2558191 prefixEnd_2558191 291907019779134622143911 := by
  unfold tailWord_2558191
  simp only [CollatzResearch.WordTrace]
  refine ⟨93304891075118386084186427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62203260716745590722790951 93304891075118386084186427)
  ·
    refine ⟨139957336612677579126279641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93304891075118386084186427 139957336612677579126279641)
    ·
      refine ⟨104968002459508184344709731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139957336612677579126279641 104968002459508184344709731)
      ·
        refine ⟨157452003689262276517064597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104968002459508184344709731 157452003689262276517064597)
        ·
          refine ⟨7380562672934169211737403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157452003689262276517064597 7380562672934169211737403)
          ·
            refine ⟨11070844009401253817606105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7380562672934169211737403 11070844009401253817606105)
            ·
              refine ⟨8303133007050940363204579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11070844009401253817606105 8303133007050940363204579)
              ·
                refine ⟨12454699510576410544806869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8303133007050940363204579 12454699510576410544806869)
                ·
                  refine ⟨291907019779134622143911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12454699510576410544806869 291907019779134622143911)
                  ·
                    rfl

theorem cell22_2558191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_2558191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558191 prefixEnd_2558191 := by exact prefixLift 2558191
  have htrace : WordTrace (prefixWord ++ tailWord_2558191) baseStart_2558191 baseEnd_2558191 := by
    simpa [prefixWord, tailWord_2558191, baseEnd_2558191] using wordTrace_append hprefix tailTrace_2558191
  have hstable : (prefixWord ++ tailWord_2558191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558191).length < 2 ^ (prefixWord ++ tailWord_2558191).sum := by decide
  have hdescent : baseEnd_2558191 < baseStart_2558191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558208 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_2558208 : Nat := 118140960795 + 2558208 * 2 ^ 59
def prefixEnd_2558208 : Nat := 4983230072969 + 3 ^ 40 * 2558208 * 2
def baseEnd_2558208 : Nat := 291908959594940496252227

theorem tailTrace_2558208 : CollatzResearch.WordTrace tailWord_2558208 prefixEnd_2558208 291908959594940496252227 := by
  unfold tailWord_2558208
  simp only [CollatzResearch.WordTrace]
  refine ⟨46652755558028398993777639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62203674077371198658370185 46652755558028398993777639)
  ·
    refine ⟨69979133337042598490666459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46652755558028398993777639 69979133337042598490666459)
    ·
      refine ⟨104968700005563897735999689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69979133337042598490666459 104968700005563897735999689)
      ·
        refine ⟨78726525004172923301999767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104968700005563897735999689 78726525004172923301999767)
        ·
          refine ⟨118089787506259384952999651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78726525004172923301999767 118089787506259384952999651)
          ·
            refine ⟨177134681259389077429499477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118089787506259384952999651 177134681259389077429499477)
            ·
              refine ⟨2075797046008465751126947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 177134681259389077429499477 2075797046008465751126947)
              ·
                refine ⟨3113695569012698626690421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075797046008465751126947 3113695569012698626690421)
                ·
                  refine ⟨291908959594940496252227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3113695569012698626690421 291908959594940496252227)
                  ·
                    rfl

theorem cell22_2558208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_2558208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558208 prefixEnd_2558208 := by exact prefixLift 2558208
  have htrace : WordTrace (prefixWord ++ tailWord_2558208) baseStart_2558208 baseEnd_2558208 := by
    simpa [prefixWord, tailWord_2558208, baseEnd_2558208] using wordTrace_append hprefix tailTrace_2558208
  have hstable : (prefixWord ++ tailWord_2558208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558208).length < 2 ^ (prefixWord ++ tailWord_2558208).sum := by decide
  have hdescent : baseEnd_2558208 < baseStart_2558208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558268 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2558268 : Nat := 118140960795 + 2558268 * 2 ^ 59
def prefixEnd_2558268 : Nat := 4983230072969 + 3 ^ 40 * 2558268 * 2
def baseEnd_2558268 : Nat := 875747418011001332256497

theorem tailTrace_2558268 : CollatzResearch.WordTrace tailWord_2558268 prefixEnd_2558268 875747418011001332256497 := by
  unfold tailWord_2558268
  simp only [CollatzResearch.WordTrace]
  refine ⟨46653849747919714117369729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62205132997226285489826305 46653849747919714117369729)
  ·
    refine ⟨34990387310939785588027297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46653849747919714117369729 34990387310939785588027297)
    ·
      refine ⟨26242790483204839191020473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34990387310939785588027297 26242790483204839191020473)
      ·
        refine ⟨19682092862403629393265355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26242790483204839191020473 19682092862403629393265355)
        ·
          refine ⟨29523139293605444089898033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19682092862403629393265355 29523139293605444089898033)
          ·
            refine ⟨22142354470204083067423525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29523139293605444089898033 22142354470204083067423525)
            ·
              refine ⟨4151691463163265575141911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22142354470204083067423525 4151691463163265575141911)
              ·
                refine ⟨6227537194744898362712867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151691463163265575141911 6227537194744898362712867)
                ·
                  refine ⟨9341305792117347544069301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6227537194744898362712867 9341305792117347544069301)
                  ·
                    refine ⟨875747418011001332256497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9341305792117347544069301 875747418011001332256497)
                    ·
                      rfl

theorem cell22_2558268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2558268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558268 prefixEnd_2558268 := by exact prefixLift 2558268
  have htrace : WordTrace (prefixWord ++ tailWord_2558268) baseStart_2558268 baseEnd_2558268 := by
    simpa [prefixWord, tailWord_2558268, baseEnd_2558268] using wordTrace_append hprefix tailTrace_2558268
  have hstable : (prefixWord ++ tailWord_2558268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558268).length < 2 ^ (prefixWord ++ tailWord_2558268).sum := by decide
  have hdescent : baseEnd_2558268 < baseStart_2558268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558347 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 1, 3]
def baseStart_2558347 : Nat := 118140960795 + 2558347 * 2 ^ 59
def prefixEnd_2558347 : Nat := 4983230072969 + 3 ^ 40 * 2558347 * 2
def baseEnd_2558347 : Nat := 875774461325471459531255

theorem tailTrace_2558347 : CollatzResearch.WordTrace tailWord_2558347 prefixEnd_2558347 875774461325471459531255 := by
  unfold tailWord_2558347
  simp only [CollatzResearch.WordTrace]
  refine ⟨93310580862553224726865295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62207053908368816484576863 93310580862553224726865295)
  ·
    refine ⟨139965871293829837090297943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93310580862553224726865295 139965871293829837090297943)
    ·
      refine ⟨209948806940744755635446915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139965871293829837090297943 209948806940744755635446915)
      ·
        refine ⟨314923210411117133453170373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209948806940744755635446915 314923210411117133453170373)
        ·
          refine ⟨59048101952084462522469445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314923210411117133453170373 59048101952084462522469445)
          ·
            refine ⟨11071519116015836722963021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59048101952084462522469445 11071519116015836722963021)
            ·
              refine ⟨4151819668505938771111133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11071519116015836722963021 4151819668505938771111133)
              ·
                refine ⟨1556932375689727039166675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4151819668505938771111133 1556932375689727039166675)
                ·
                  refine ⟨2335398563534590558750013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556932375689727039166675 2335398563534590558750013)
                  ·
                    refine ⟨875774461325471459531255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335398563534590558750013 875774461325471459531255)
                    ·
                      rfl

theorem cell22_2558347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 1, 3].length) (baseStart_2558347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558347 prefixEnd_2558347 := by exact prefixLift 2558347
  have htrace : WordTrace (prefixWord ++ tailWord_2558347) baseStart_2558347 baseEnd_2558347 := by
    simpa [prefixWord, tailWord_2558347, baseEnd_2558347] using wordTrace_append hprefix tailTrace_2558347
  have hstable : (prefixWord ++ tailWord_2558347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558347).length < 2 ^ (prefixWord ++ tailWord_2558347).sum := by decide
  have hdescent : baseEnd_2558347 < baseStart_2558347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558373 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2558373 : Nat := 118140960795 + 2558373 * 2 ^ 59
def prefixEnd_2558373 : Nat := 4983230072969 + 3 ^ 40 * 2558373 * 2
def baseEnd_2558373 : Nat := 875783361656816058381175

theorem tailTrace_2558373 : CollatzResearch.WordTrace tailWord_2558373 prefixEnd_2558373 875783361656816058381175 := by
  unfold tailWord_2558373
  simp only [CollatzResearch.WordTrace]
  refine ⟨93311529160459031167311773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62207686106972687444874515 93311529160459031167311773)
  ·
    refine ⟨34991823435172136687741915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93311529160459031167311773 34991823435172136687741915)
    ·
      refine ⟨52487735152758205031612873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34991823435172136687741915 52487735152758205031612873)
      ·
        refine ⟨39365801364568653773709655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52487735152758205031612873 39365801364568653773709655)
        ·
          refine ⟨59048702046852980660564483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39365801364568653773709655 59048702046852980660564483)
          ·
            refine ⟨88573053070279470990846725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59048702046852980660564483 88573053070279470990846725)
            ·
              refine ⟨16607447450677400810783761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88573053070279470990846725 16607447450677400810783761)
              ·
                refine ⟨12455585588008050608087821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16607447450677400810783761 12455585588008050608087821)
                ·
                  refine ⟨4670844595503018978032933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12455585588008050608087821 4670844595503018978032933)
                  ·
                    refine ⟨875783361656816058381175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4670844595503018978032933 875783361656816058381175)
                    ·
                      rfl

theorem cell22_2558373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2558373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558373 prefixEnd_2558373 := by exact prefixLift 2558373
  have htrace : WordTrace (prefixWord ++ tailWord_2558373) baseStart_2558373 baseEnd_2558373 := by
    simpa [prefixWord, tailWord_2558373, baseEnd_2558373] using wordTrace_append hprefix tailTrace_2558373
  have hstable : (prefixWord ++ tailWord_2558373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558373).length < 2 ^ (prefixWord ++ tailWord_2558373).sum := by decide
  have hdescent : baseEnd_2558373 < baseStart_2558373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558407 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2558407 : Nat := 118140960795 + 2558407 * 2 ^ 59
def prefixEnd_2558407 : Nat := 4983230072969 + 3 ^ 40 * 2558407 * 2
def baseEnd_2558407 : Nat := 875795000551651303031071

theorem tailTrace_2558407 : CollatzResearch.WordTrace tailWord_2558407 prefixEnd_2558407 875795000551651303031071 := by
  unfold tailWord_2558407
  simp only [CollatzResearch.WordTrace]
  refine ⟨93312769242335854974049475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62208512828223903316032983 93312769242335854974049475)
  ·
    refine ⟨139969153863503782461074213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93312769242335854974049475 139969153863503782461074213)
    ·
      refine ⟨26244216349406959211451415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139969153863503782461074213 26244216349406959211451415)
      ·
        refine ⟨39366324524110438817177123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26244216349406959211451415 39366324524110438817177123)
        ·
          refine ⟨59049486786165658225765685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39366324524110438817177123 59049486786165658225765685)
          ·
            refine ⟨5535889386203030458665533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59049486786165658225765685 5535889386203030458665533)
            ·
              refine ⟨2075958519826136421999575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5535889386203030458665533 2075958519826136421999575)
              ·
                refine ⟨3113937779739204632999363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075958519826136421999575 3113937779739204632999363)
                ·
                  refine ⟨4670906669608806949499045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113937779739204632999363 4670906669608806949499045)
                  ·
                    refine ⟨875795000551651303031071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4670906669608806949499045 875795000551651303031071)
                    ·
                      rfl

theorem cell22_2558407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2558407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558407 prefixEnd_2558407 := by exact prefixLift 2558407
  have htrace : WordTrace (prefixWord ++ tailWord_2558407) baseStart_2558407 baseEnd_2558407 := by
    simpa [prefixWord, tailWord_2558407, baseEnd_2558407] using wordTrace_append hprefix tailTrace_2558407
  have hstable : (prefixWord ++ tailWord_2558407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558407).length < 2 ^ (prefixWord ++ tailWord_2558407).sum := by decide
  have hdescent : baseEnd_2558407 < baseStart_2558407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558437 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2558437 : Nat := 118140960795 + 2558437 * 2 ^ 59
def prefixEnd_2558437 : Nat := 4983230072969 + 3 ^ 40 * 2558437 * 2
def baseEnd_2558437 : Nat := 875805270164741224780979

theorem tailTrace_2558437 : CollatzResearch.WordTrace tailWord_2558437 prefixEnd_2558437 875805270164741224780979 := by
  unfold tailWord_2558437
  simp only [CollatzResearch.WordTrace]
  refine ⟨93313863432227170097641565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62209242288151446731761043 93313863432227170097641565)
  ·
    refine ⟨34992698787085188786615587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93313863432227170097641565 34992698787085188786615587)
    ·
      refine ⟨52489048180627783179923381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34992698787085188786615587 52489048180627783179923381)
      ·
        refine ⟨4920848266933854673117817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52489048180627783179923381 4920848266933854673117817)
        ·
          refine ⟨3690636200200391004838363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920848266933854673117817 3690636200200391004838363)
          ·
            refine ⟨5535954300300586507257545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690636200200391004838363 5535954300300586507257545)
            ·
              refine ⟨4151965725225439880443159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5535954300300586507257545 4151965725225439880443159)
              ·
                refine ⟨6227948587838159820664739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151965725225439880443159 6227948587838159820664739)
                ·
                  refine ⟨9341922881757239730997109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6227948587838159820664739 9341922881757239730997109)
                  ·
                    refine ⟨875805270164741224780979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9341922881757239730997109 875805270164741224780979)
                    ·
                      rfl

theorem cell22_2558437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2558437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558437 prefixEnd_2558437 := by exact prefixLift 2558437
  have htrace : WordTrace (prefixWord ++ tailWord_2558437) baseStart_2558437 baseEnd_2558437 := by
    simpa [prefixWord, tailWord_2558437, baseEnd_2558437] using wordTrace_append hprefix tailTrace_2558437
  have hstable : (prefixWord ++ tailWord_2558437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558437).length < 2 ^ (prefixWord ++ tailWord_2558437).sum := by decide
  have hdescent : baseEnd_2558437 < baseStart_2558437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558471 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2558471 : Nat := 118140960795 + 2558471 * 2 ^ 59
def prefixEnd_2558471 : Nat := 4983230072969 + 3 ^ 40 * 2558471 * 2
def baseEnd_2558471 : Nat := 875816909059576469430875

theorem tailTrace_2558471 : CollatzResearch.WordTrace tailWord_2558471 prefixEnd_2558471 875816909059576469430875 := by
  unfold tailWord_2558471
  simp only [CollatzResearch.WordTrace]
  refine ⟨93315103514103993904379267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62210069009402662602919511 93315103514103993904379267)
  ·
    refine ⟨139972655271155990856568901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93315103514103993904379267 139972655271155990856568901)
    ·
      refine ⟨26244872863341748285606669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139972655271155990856568901 26244872863341748285606669)
      ·
        refine ⟨9841827323753155607102501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26244872863341748285606669 9841827323753155607102501)
        ·
          refine ⟨1845342623203716676331719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9841827323753155607102501 1845342623203716676331719)
          ·
            refine ⟨2768013934805575014497579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845342623203716676331719 2768013934805575014497579)
            ·
              refine ⟨4152020902208362521746369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768013934805575014497579 4152020902208362521746369)
              ·
                refine ⟨3114015676656271891309777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152020902208362521746369 3114015676656271891309777)
                ·
                  refine ⟨2335511757492203918482333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114015676656271891309777 2335511757492203918482333)
                  ·
                    refine ⟨875816909059576469430875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335511757492203918482333 875816909059576469430875)
                    ·
                      rfl

theorem cell22_2558471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2558471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558471 prefixEnd_2558471 := by exact prefixLift 2558471
  have htrace : WordTrace (prefixWord ++ tailWord_2558471) baseStart_2558471 baseEnd_2558471 := by
    simpa [prefixWord, tailWord_2558471, baseEnd_2558471] using wordTrace_append hprefix tailTrace_2558471
  have hstable : (prefixWord ++ tailWord_2558471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558471).length < 2 ^ (prefixWord ++ tailWord_2558471).sum := by decide
  have hdescent : baseEnd_2558471 < baseStart_2558471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558508 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2558508 : Nat := 118140960795 + 2558508 * 2 ^ 59
def prefixEnd_2558508 : Nat := 4983230072969 + 3 ^ 40 * 2558508 * 2
def baseEnd_2558508 : Nat := 875829574915720706255761

theorem tailTrace_2558508 : CollatzResearch.WordTrace tailWord_2558508 prefixEnd_2558508 875829574915720706255761 := by
  unfold tailWord_2558508
  simp only [CollatzResearch.WordTrace]
  refine ⟨46658226507484974611738089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62210968676646632815650785 46658226507484974611738089)
  ·
    refine ⟨34993669880613730958803567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46658226507484974611738089 34993669880613730958803567)
    ·
      refine ⟨52490504820920596438205351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34993669880613730958803567 52490504820920596438205351)
      ·
        refine ⟨78735757231380894657308027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52490504820920596438205351 78735757231380894657308027)
        ·
          refine ⟨118103635847071341985962041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78735757231380894657308027 118103635847071341985962041)
          ·
            refine ⟨88577726885303506489471531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118103635847071341985962041 88577726885303506489471531)
            ·
              refine ⟨132866590327955259734207297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88577726885303506489471531 132866590327955259734207297)
              ·
                refine ⟨99649942745966444800655473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132866590327955259734207297 99649942745966444800655473)
                ·
                  refine ⟨74737457059474833600491605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99649942745966444800655473 74737457059474833600491605)
                  ·
                    refine ⟨875829574915720706255761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74737457059474833600491605 875829574915720706255761)
                    ·
                      rfl

theorem cell22_2558508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2558508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558508 prefixEnd_2558508 := by exact prefixLift 2558508
  have htrace : WordTrace (prefixWord ++ tailWord_2558508) baseStart_2558508 baseEnd_2558508 := by
    simpa [prefixWord, tailWord_2558508, baseEnd_2558508] using wordTrace_append hprefix tailTrace_2558508
  have hstable : (prefixWord ++ tailWord_2558508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558508).length < 2 ^ (prefixWord ++ tailWord_2558508).sum := by decide
  have hdescent : baseEnd_2558508 < baseStart_2558508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558615 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2558615 : Nat := 118140960795 + 2558615 * 2 ^ 59
def prefixEnd_2558615 : Nat := 4983230072969 + 3 ^ 40 * 2558615 * 2
def baseEnd_2558615 : Nat := 875866203202408093830433

theorem tailTrace_2558615 : CollatzResearch.WordTrace tailWord_2558615 prefixEnd_2558615 875866203202408093830433 := by
  unfold tailWord_2558615
  simp only [CollatzResearch.WordTrace]
  refine ⟨93320355625582306497621299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62213570417054870998414199 93320355625582306497621299)
  ·
    refine ⟨139980533438373459746431949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93320355625582306497621299 139980533438373459746431949)
    ·
      refine ⟨52492700039390047404911981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139980533438373459746431949 52492700039390047404911981)
      ·
        refine ⟨19684762514771267776841993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52492700039390047404911981 19684762514771267776841993)
        ·
          refine ⟨14763571886078450832631495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19684762514771267776841993 14763571886078450832631495)
          ·
            refine ⟨22145357829117676248947243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14763571886078450832631495 22145357829117676248947243)
            ·
              refine ⟨33218036743676514373420865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22145357829117676248947243 33218036743676514373420865)
              ·
                refine ⟨24913527557757385780065649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33218036743676514373420865 24913527557757385780065649)
                ·
                  refine ⟨18685145668318039335049237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24913527557757385780065649 18685145668318039335049237)
                  ·
                    refine ⟨875866203202408093830433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18685145668318039335049237 875866203202408093830433)
                    ·
                      rfl

theorem cell22_2558615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2558615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558615 prefixEnd_2558615 := by exact prefixLift 2558615
  have htrace : WordTrace (prefixWord ++ tailWord_2558615) baseStart_2558615 baseEnd_2558615 := by
    simpa [prefixWord, tailWord_2558615, baseEnd_2558615] using wordTrace_append hprefix tailTrace_2558615
  have hstable : (prefixWord ++ tailWord_2558615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558615).length < 2 ^ (prefixWord ++ tailWord_2558615).sum := by decide
  have hdescent : baseEnd_2558615 < baseStart_2558615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558617 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_2558617 : Nat := 118140960795 + 2558617 * 2 ^ 59
def prefixEnd_2558617 : Nat := 4983230072969 + 3 ^ 40 * 2558617 * 2
def baseEnd_2558617 : Nat := 875866887843280755280427

theorem tailTrace_2558617 : CollatzResearch.WordTrace tailWord_2558617 prefixEnd_2558617 875866887843280755280427 := by
  unfold tailWord_2558617
  simp only [CollatzResearch.WordTrace]
  refine ⟨93320428571575060839194105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62213619047716707226129403 93320428571575060839194105)
  ·
    refine ⟨69990321428681295629395579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93320428571575060839194105 69990321428681295629395579)
    ·
      refine ⟨104985482143021943444093369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69990321428681295629395579 104985482143021943444093369)
      ·
        refine ⟨78739111607266457583070027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104985482143021943444093369 78739111607266457583070027)
        ·
          refine ⟨118108667410899686374605041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78739111607266457583070027 118108667410899686374605041)
          ·
            refine ⟨88581500558174764780953781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118108667410899686374605041 88581500558174764780953781)
            ·
              refine ⟨8304515677328884198214417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88581500558174764780953781 8304515677328884198214417)
              ·
                refine ⟨6228386757996663148660813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8304515677328884198214417 6228386757996663148660813)
                ·
                  refine ⟨2335645034248748680747805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6228386757996663148660813 2335645034248748680747805)
                  ·
                    refine ⟨875866887843280755280427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335645034248748680747805 875866887843280755280427)
                    ·
                      rfl

theorem cell22_2558617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_2558617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558617 prefixEnd_2558617 := by exact prefixLift 2558617
  have htrace : WordTrace (prefixWord ++ tailWord_2558617) baseStart_2558617 baseEnd_2558617 := by
    simpa [prefixWord, tailWord_2558617, baseEnd_2558617] using wordTrace_append hprefix tailTrace_2558617
  have hstable : (prefixWord ++ tailWord_2558617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558617).length < 2 ^ (prefixWord ++ tailWord_2558617).sum := by decide
  have hdescent : baseEnd_2558617 < baseStart_2558617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558647 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 7]
def baseStart_2558647 : Nat := 118140960795 + 2558647 * 2 ^ 59
def prefixEnd_2558647 : Nat := 4983230072969 + 3 ^ 40 * 2558647 * 2
def baseEnd_2558647 : Nat := 291959052485456892343445

theorem tailTrace_2558647 : CollatzResearch.WordTrace tailWord_2558647 prefixEnd_2558647 291959052485456892343445 := by
  unfold tailWord_2558647
  simp only [CollatzResearch.WordTrace]
  refine ⟨93321522761466375962786195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62214348507644250641857463 93321522761466375962786195)
  ·
    refine ⟨139982284142199563944179293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93321522761466375962786195 139982284142199563944179293)
    ·
      refine ⟨52493356553324836479067235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139982284142199563944179293 52493356553324836479067235)
      ·
        refine ⟨78740034829987254718600853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52493356553324836479067235 78740034829987254718600853)
        ·
          refine ⟨3690939132655652564934415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78740034829987254718600853 3690939132655652564934415)
          ·
            refine ⟨5536408698983478847401623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690939132655652564934415 5536408698983478847401623)
            ·
              refine ⟨8304613048475218271102435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5536408698983478847401623 8304613048475218271102435)
              ·
                refine ⟨12456919572712827406653653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8304613048475218271102435 12456919572712827406653653)
                ·
                  refine ⟨291959052485456892343445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12456919572712827406653653 291959052485456892343445)
                  ·
                    rfl

theorem cell22_2558647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 7].length) (baseStart_2558647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558647 prefixEnd_2558647 := by exact prefixLift 2558647
  have htrace : WordTrace (prefixWord ++ tailWord_2558647) baseStart_2558647 baseEnd_2558647 := by
    simpa [prefixWord, tailWord_2558647, baseEnd_2558647] using wordTrace_append hprefix tailTrace_2558647
  have hstable : (prefixWord ++ tailWord_2558647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558647).length < 2 ^ (prefixWord ++ tailWord_2558647).sum := by decide
  have hdescent : baseEnd_2558647 < baseStart_2558647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558664 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_2558664 : Nat := 118140960795 + 2558664 * 2 ^ 59
def prefixEnd_2558664 : Nat := 4983230072969 + 3 ^ 40 * 2558664 * 2
def baseEnd_2558664 : Nat := 291960992301262766451761

theorem tailTrace_2558664 : CollatzResearch.WordTrace tailWord_2558664 prefixEnd_2558664 291960992301262766451761 := by
  unfold tailWord_2558664
  simp only [CollatzResearch.WordTrace]
  refine ⟨46661071401202393933077523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62214761868269858577436697 46661071401202393933077523)
  ·
    refine ⟨69991607101803590899616285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46661071401202393933077523 69991607101803590899616285)
    ·
      refine ⟨26246852663176346587356107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69991607101803590899616285 26246852663176346587356107)
      ·
        refine ⟨39370278994764519881034161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26246852663176346587356107 39370278994764519881034161)
        ·
          refine ⟨29527709246073389910775621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39370278994764519881034161 29527709246073389910775621)
          ·
            refine ⟨5536445483638760608270429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29527709246073389910775621 5536445483638760608270429)
            ·
              refine ⟨2076167056364535228101411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5536445483638760608270429 2076167056364535228101411)
              ·
                refine ⟨3114250584546802842152117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076167056364535228101411 3114250584546802842152117)
                ·
                  refine ⟨291960992301262766451761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3114250584546802842152117 291960992301262766451761)
                  ·
                    rfl

theorem cell22_2558664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_2558664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558664 prefixEnd_2558664 := by exact prefixLift 2558664
  have htrace : WordTrace (prefixWord ++ tailWord_2558664) baseStart_2558664 baseEnd_2558664 := by
    simpa [prefixWord, tailWord_2558664, baseEnd_2558664] using wordTrace_append hprefix tailTrace_2558664
  have hstable : (prefixWord ++ tailWord_2558664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558664).length < 2 ^ (prefixWord ++ tailWord_2558664).sum := by decide
  have hdescent : baseEnd_2558664 < baseStart_2558664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558769 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_2558769 : Nat := 118140960795 + 2558769 * 2 ^ 59
def prefixEnd_2558769 : Nat := 4983230072969 + 3 ^ 40 * 2558769 * 2
def baseEnd_2558769 : Nat := 875918920549603025479961

theorem tailTrace_2558769 : CollatzResearch.WordTrace tailWord_2558769 prefixEnd_2558769 875918920549603025479961 := by
  unfold tailWord_2558769
  simp only [CollatzResearch.WordTrace]
  refine ⟨93325972467024390798727361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62217314978016260532484907 93325972467024390798727361)
  ·
    refine ⟨69994479350268293099045521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93325972467024390798727361 69994479350268293099045521)
    ·
      refine ⟨52495859512701219824284141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69994479350268293099045521 52495859512701219824284141)
      ·
        refine ⟨19685947317262957434106553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52495859512701219824284141 19685947317262957434106553)
        ·
          refine ⟨14764460487947218075579915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19685947317262957434106553 14764460487947218075579915)
          ·
            refine ⟨22146690731920827113369873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14764460487947218075579915 22146690731920827113369873)
            ·
              refine ⟨16610018048940620335027405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22146690731920827113369873 16610018048940620335027405)
              ·
                refine ⟨6228756768352732625635277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16610018048940620335027405 6228756768352732625635277)
                ·
                  refine ⟨2335783788132274734613229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6228756768352732625635277 2335783788132274734613229)
                  ·
                    refine ⟨875918920549603025479961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335783788132274734613229 875918920549603025479961)
                    ·
                      rfl

theorem cell22_2558769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_2558769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558769 prefixEnd_2558769 := by exact prefixLift 2558769
  have htrace : WordTrace (prefixWord ++ tailWord_2558769) baseStart_2558769 baseEnd_2558769 := by
    simpa [prefixWord, tailWord_2558769, baseEnd_2558769] using wordTrace_append hprefix tailTrace_2558769
  have hstable : (prefixWord ++ tailWord_2558769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558769).length < 2 ^ (prefixWord ++ tailWord_2558769).sum := by decide
  have hdescent : baseEnd_2558769 < baseStart_2558769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558788 : List Nat := [2, 3, 4, 2, 1, 1, 3, 6]
def baseStart_2558788 : Nat := 118140960795 + 2558788 * 2 ^ 59
def prefixEnd_2558788 : Nat := 4983230072969 + 3 ^ 40 * 2558788 * 2
def baseEnd_2558788 : Nat := 97325047181988145472767

theorem tailTrace_2558788 : CollatzResearch.WordTrace tailWord_2558788 prefixEnd_2558788 97325047181988145472767 := by
  unfold tailWord_2558788
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663332726977778521834509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62217776969303704695779345 46663332726977778521834509)
  ·
    refine ⟨17498749772616666945687941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46663332726977778521834509 17498749772616666945687941)
    ·
      refine ⟨3281015582365625052316489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17498749772616666945687941 3281015582365625052316489)
      ·
        refine ⟨2460761686774218789237367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3281015582365625052316489 2460761686774218789237367)
        ·
          refine ⟨3691142530161328183856051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460761686774218789237367 3691142530161328183856051)
          ·
            refine ⟨5536713795241992275784077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691142530161328183856051 5536713795241992275784077)
            ·
              refine ⟨2076267673215747103419029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5536713795241992275784077 2076267673215747103419029)
              ·
                refine ⟨97325047181988145472767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2076267673215747103419029 97325047181988145472767)
                ·
                  rfl

theorem cell22_2558788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_2558788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558788 prefixEnd_2558788 := by exact prefixLift 2558788
  have htrace : WordTrace (prefixWord ++ tailWord_2558788) baseStart_2558788 baseEnd_2558788 := by
    simpa [prefixWord, tailWord_2558788, baseEnd_2558788] using wordTrace_append hprefix tailTrace_2558788
  have hstable : (prefixWord ++ tailWord_2558788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558788).length < 2 ^ (prefixWord ++ tailWord_2558788).sum := by decide
  have hdescent : baseEnd_2558788 < baseStart_2558788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558790 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2558790 : Nat := 118140960795 + 2558790 * 2 ^ 59
def prefixEnd_2558790 : Nat := 4983230072969 + 3 ^ 40 * 2558790 * 2
def baseEnd_2558790 : Nat := 875926109278765970704897

theorem tailTrace_2558790 : CollatzResearch.WordTrace tailWord_2558790 prefixEnd_2558790 875926109278765970704897 := by
  unfold tailWord_2558790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916460574998384730788807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62217825599965540923494549 2916460574998384730788807)
  ·
    refine ⟨4374690862497577096183211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2916460574998384730788807 4374690862497577096183211)
    ·
      refine ⟨6562036293746365644274817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374690862497577096183211 6562036293746365644274817)
      ·
        refine ⟨4921527220309774233206113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6562036293746365644274817 4921527220309774233206113)
        ·
          refine ⟨3691145415232330674904585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4921527220309774233206113 3691145415232330674904585)
          ·
            refine ⟨2768359061424248006178439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691145415232330674904585 2768359061424248006178439)
            ·
              refine ⟨4152538592136372009267659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768359061424248006178439 4152538592136372009267659)
              ·
                refine ⟨6228807888204558013901489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152538592136372009267659 6228807888204558013901489)
                ·
                  refine ⟨4671605916153418510426117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6228807888204558013901489 4671605916153418510426117)
                  ·
                    refine ⟨875926109278765970704897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671605916153418510426117 875926109278765970704897)
                    ·
                      rfl

theorem cell22_2558790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2558790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558790 prefixEnd_2558790 := by exact prefixLift 2558790
  have htrace : WordTrace (prefixWord ++ tailWord_2558790) baseStart_2558790 baseEnd_2558790 := by
    simpa [prefixWord, tailWord_2558790, baseEnd_2558790] using wordTrace_append hprefix tailTrace_2558790
  have hstable : (prefixWord ++ tailWord_2558790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558790).length < 2 ^ (prefixWord ++ tailWord_2558790).sum := by decide
  have hdescent : baseEnd_2558790 < baseStart_2558790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558827 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 6]
def baseStart_2558827 : Nat := 118140960795 + 2558827 * 2 ^ 59
def prefixEnd_2558827 : Nat := 4983230072969 + 3 ^ 40 * 2558827 * 2
def baseEnd_2558827 : Nat := 291979591711636735843261

theorem tailTrace_2558827 : CollatzResearch.WordTrace tailWord_2558827 prefixEnd_2558827 291979591711636735843261 := by
  unfold tailWord_2558827
  simp only [CollatzResearch.WordTrace]
  refine ⟨93328087900814266704338735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62218725267209511136225823 93328087900814266704338735)
  ·
    refine ⟨139992131851221400056508103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93328087900814266704338735 139992131851221400056508103)
    ·
      refine ⟨209988197776832100084762155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139992131851221400056508103 209988197776832100084762155)
      ·
        refine ⟨314982296665248150127143233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209988197776832100084762155 314982296665248150127143233)
        ·
          refine ⟨236236722498936112595357425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314982296665248150127143233 236236722498936112595357425)
          ·
            refine ⟨177177541874202084446518069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236236722498936112595357425 177177541874202084446518069)
            ·
              refine ⟨16610394550706445416861069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177177541874202084446518069 16610394550706445416861069)
              ·
                refine ⟨6228897956514917031322901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16610394550706445416861069 6228897956514917031322901)
                ·
                  refine ⟨291979591711636735843261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6228897956514917031322901 291979591711636735843261)
                  ·
                    rfl

theorem cell22_2558827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_2558827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558827 prefixEnd_2558827 := by exact prefixLift 2558827
  have htrace : WordTrace (prefixWord ++ tailWord_2558827) baseStart_2558827 baseEnd_2558827 := by
    simpa [prefixWord, tailWord_2558827, baseEnd_2558827] using wordTrace_append hprefix tailTrace_2558827
  have hstable : (prefixWord ++ tailWord_2558827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558827).length < 2 ^ (prefixWord ++ tailWord_2558827).sum := by decide
  have hdescent : baseEnd_2558827 < baseStart_2558827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558859 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 4, 3]
def baseStart_2558859 : Nat := 118140960795 + 2558859 * 2 ^ 59
def prefixEnd_2558859 : Nat := 4983230072969 + 3 ^ 40 * 2558859 * 2
def baseEnd_2558859 : Nat := 875949729388872790729685

theorem tailTrace_2558859 : CollatzResearch.WordTrace tailWord_2558859 prefixEnd_2558859 875949729388872790729685 := by
  unfold tailWord_2558859
  simp only [CollatzResearch.WordTrace]
  refine ⟨93329255036698336169503631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62219503357798890779669087 93329255036698336169503631)
  ·
    refine ⟨139993882555047504254255447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93329255036698336169503631 139993882555047504254255447)
    ·
      refine ⟨209990823832571256381383171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139993882555047504254255447 209990823832571256381383171)
      ·
        refine ⟨314986235748856884572074757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209990823832571256381383171 314986235748856884572074757)
        ·
          refine ⟨59059919202910665857264017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314986235748856884572074757 59059919202910665857264017)
          ·
            refine ⟨44294939402182999392948013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59059919202910665857264017 44294939402182999392948013)
            ·
              refine ⟨16610602275818624772355505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44294939402182999392948013 16610602275818624772355505)
              ·
                refine ⟨12457951706863968579266629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16610602275818624772355505 12457951706863968579266629)
                ·
                  refine ⟨2335865945036994108612493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12457951706863968579266629 2335865945036994108612493)
                  ·
                    refine ⟨875949729388872790729685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2335865945036994108612493 875949729388872790729685)
                    ·
                      rfl

theorem cell22_2558859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3].length) (baseStart_2558859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558859 prefixEnd_2558859 := by exact prefixLift 2558859
  have htrace : WordTrace (prefixWord ++ tailWord_2558859) baseStart_2558859 baseEnd_2558859 := by
    simpa [prefixWord, tailWord_2558859, baseEnd_2558859] using wordTrace_append hprefix tailTrace_2558859
  have hstable : (prefixWord ++ tailWord_2558859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558859).length < 2 ^ (prefixWord ++ tailWord_2558859).sum := by decide
  have hdescent : baseEnd_2558859 < baseStart_2558859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558951 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 5]
def baseStart_2558951 : Nat := 118140960795 + 2558951 * 2 ^ 59
def prefixEnd_2558951 : Nat := 4983230072969 + 3 ^ 40 * 2558951 * 2
def baseEnd_2558951 : Nat := 291993740956338405809801

theorem tailTrace_2558951 : CollatzResearch.WordTrace tailWord_2558951 prefixEnd_2558951 291993740956338405809801 := by
  unfold tailWord_2558951
  simp only [CollatzResearch.WordTrace]
  refine ⟨93332610552365035881852707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62221740368243357254568471 93332610552365035881852707)
  ·
    refine ⟨139998915828547553822779061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93332610552365035881852707 139998915828547553822779061)
    ·
      refine ⟨13124898358926333170885537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139998915828547553822779061 13124898358926333170885537)
      ·
        refine ⟨9843673769194749878164153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13124898358926333170885537 9843673769194749878164153)
        ·
          refine ⟨7382755326896062408623115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9843673769194749878164153 7382755326896062408623115)
          ·
            refine ⟨11074132990344093612934673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382755326896062408623115 11074132990344093612934673)
            ·
              refine ⟨8305599742758070209701005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11074132990344093612934673 8305599742758070209701005)
              ·
                refine ⟨3114599903534276328637877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8305599742758070209701005 3114599903534276328637877)
                ·
                  refine ⟨291993740956338405809801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3114599903534276328637877 291993740956338405809801)
                  ·
                    rfl

theorem cell22_2558951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 5].length) (baseStart_2558951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558951 prefixEnd_2558951 := by exact prefixLift 2558951
  have htrace : WordTrace (prefixWord ++ tailWord_2558951) baseStart_2558951 baseEnd_2558951 := by
    simpa [prefixWord, tailWord_2558951, baseEnd_2558951] using wordTrace_append hprefix tailTrace_2558951
  have hstable : (prefixWord ++ tailWord_2558951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558951).length < 2 ^ (prefixWord ++ tailWord_2558951).sum := by decide
  have hdescent : baseEnd_2558951 < baseStart_2558951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558981 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2558981 : Nat := 118140960795 + 2558981 * 2 ^ 59
def prefixEnd_2558981 : Nat := 4983230072969 + 3 ^ 40 * 2558981 * 2
def baseEnd_2558981 : Nat := 875991492482105139179311

theorem tailTrace_2558981 : CollatzResearch.WordTrace tailWord_2558981 prefixEnd_2558981 875991492482105139179311 := by
  unfold tailWord_2558981
  simp only [CollatzResearch.WordTrace]
  refine ⟨93333704742256351005444797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62222469828170900670296531 93333704742256351005444797)
  ·
    refine ⟨35000139278346131627041799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93333704742256351005444797 35000139278346131627041799)
    ·
      refine ⟨52500208917519197440562699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35000139278346131627041799 52500208917519197440562699)
      ·
        refine ⟨78750313376278796160844049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52500208917519197440562699 78750313376278796160844049)
        ·
          refine ⟨59062735032209097120633037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78750313376278796160844049 59062735032209097120633037)
          ·
            refine ⟨22148525637078411420237389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59062735032209097120633037 22148525637078411420237389)
            ·
              refine ⟨8305697113904404282589021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22148525637078411420237389 8305697113904404282589021)
              ·
                refine ⟨3114636417714151605970883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8305697113904404282589021 3114636417714151605970883)
                ·
                  refine ⟨4671954626571227408956325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114636417714151605970883 4671954626571227408956325)
                  ·
                    refine ⟨875991492482105139179311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671954626571227408956325 875991492482105139179311)
                    ·
                      rfl

theorem cell22_2558981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2558981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2558981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2558981 prefixEnd_2558981 := by exact prefixLift 2558981
  have htrace : WordTrace (prefixWord ++ tailWord_2558981) baseStart_2558981 baseEnd_2558981 := by
    simpa [prefixWord, tailWord_2558981, baseEnd_2558981] using wordTrace_append hprefix tailTrace_2558981
  have hstable : (prefixWord ++ tailWord_2558981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558981).length < 2 ^ (prefixWord ++ tailWord_2558981).sum := by decide
  have hdescent : baseEnd_2558981 < baseStart_2558981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559011 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 1, 5]
def baseStart_2559011 : Nat := 118140960795 + 2559011 * 2 ^ 59
def prefixEnd_2559011 : Nat := 4983230072969 + 3 ^ 40 * 2559011 * 2
def baseEnd_2559011 : Nat := 876001762095195060929219

theorem tailTrace_2559011 : CollatzResearch.WordTrace tailWord_2559011 prefixEnd_2559011 876001762095195060929219 := by
  unfold tailWord_2559011
  simp only [CollatzResearch.WordTrace]
  refine ⟨93334798932147666129036887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62223199288098444086024591 93334798932147666129036887)
  ·
    refine ⟨140002198398221499193555331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93334798932147666129036887 140002198398221499193555331)
    ·
      refine ⟨210003297597332248790332997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140002198398221499193555331 210003297597332248790332997)
      ·
        refine ⟨39375618299499796648187437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210003297597332248790332997 39375618299499796648187437)
        ·
          refine ⟨14765856862312423743070289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39375618299499796648187437 14765856862312423743070289)
          ·
            refine ⟨11074392646734317807302717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14765856862312423743070289 11074392646734317807302717)
            ·
              refine ⟨4152897242525369177738519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11074392646734317807302717 4152897242525369177738519)
              ·
                refine ⟨6229345863788053766607779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152897242525369177738519 6229345863788053766607779)
                ·
                  refine ⟨9344018795682080649911669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6229345863788053766607779 9344018795682080649911669)
                  ·
                    refine ⟨876001762095195060929219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9344018795682080649911669 876001762095195060929219)
                    ·
                      rfl

theorem cell22_2559011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_2559011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559011 prefixEnd_2559011 := by exact prefixLift 2559011
  have htrace : WordTrace (prefixWord ++ tailWord_2559011) baseStart_2559011 baseEnd_2559011 := by
    simpa [prefixWord, tailWord_2559011, baseEnd_2559011] using wordTrace_append hprefix tailTrace_2559011
  have hstable : (prefixWord ++ tailWord_2559011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559011).length < 2 ^ (prefixWord ++ tailWord_2559011).sum := by decide
  have hdescent : baseEnd_2559011 < baseStart_2559011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559015 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2559015 : Nat := 118140960795 + 2559015 * 2 ^ 59
def prefixEnd_2559015 : Nat := 4983230072969 + 3 ^ 40 * 2559015 * 2
def baseEnd_2559015 : Nat := 876003131376940383829207

theorem tailTrace_2559015 : CollatzResearch.WordTrace tailWord_2559015 prefixEnd_2559015 876003131376940383829207 := by
  unfold tailWord_2559015
  simp only [CollatzResearch.WordTrace]
  refine ⟨93334944824133174812182499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62223296549422116541454999 93334944824133174812182499)
  ·
    refine ⟨140002417236199762218273749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93334944824133174812182499 140002417236199762218273749)
    ·
      refine ⟨3281306653973431926990791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 140002417236199762218273749 3281306653973431926990791)
      ·
        refine ⟨4921959980960147890486187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281306653973431926990791 4921959980960147890486187)
        ·
          refine ⟨7382939971440221835729281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921959980960147890486187 7382939971440221835729281)
          ·
            refine ⟨5537204978580166376796961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382939971440221835729281 5537204978580166376796961)
            ·
              refine ⟨4152903733935124782597721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537204978580166376796961 4152903733935124782597721)
              ·
                refine ⟨3114677800451343586948291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152903733935124782597721 3114677800451343586948291)
                ·
                  refine ⟨4672016700677015380422437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114677800451343586948291 4672016700677015380422437)
                  ·
                    refine ⟨876003131376940383829207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672016700677015380422437 876003131376940383829207)
                    ·
                      rfl

theorem cell22_2559015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2559015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559015 prefixEnd_2559015 := by exact prefixLift 2559015
  have htrace : WordTrace (prefixWord ++ tailWord_2559015) baseStart_2559015 baseEnd_2559015 := by
    simpa [prefixWord, tailWord_2559015, baseEnd_2559015] using wordTrace_append hprefix tailTrace_2559015
  have hstable : (prefixWord ++ tailWord_2559015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559015).length < 2 ^ (prefixWord ++ tailWord_2559015).sum := by decide
  have hdescent : baseEnd_2559015 < baseStart_2559015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559024 : List Nat := [2, 1, 1, 1, 2, 4, 3, 8]
def baseStart_2559024 : Nat := 118140960795 + 2559024 * 2 ^ 59
def prefixEnd_2559024 : Nat := 4983230072969 + 3 ^ 40 * 2559024 * 2
def baseEnd_2559024 : Nat := 97334023584540817817131

theorem tailTrace_2559024 : CollatzResearch.WordTrace tailWord_2559024 prefixEnd_2559024 97334023584540817817131 := by
  unfold tailWord_2559024
  simp only [CollatzResearch.WordTrace]
  refine ⟨46667636540550284674630063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62223515387400379566173417 46667636540550284674630063)
  ·
    refine ⟨70001454810825427011945095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46667636540550284674630063 70001454810825427011945095)
    ·
      refine ⟨105002182216238140517917643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70001454810825427011945095 105002182216238140517917643)
      ·
        refine ⟨157503273324357210776876465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105002182216238140517917643 157503273324357210776876465)
        ·
          refine ⟨118127454993267908082657349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157503273324357210776876465 118127454993267908082657349)
          ·
            refine ⟨22148897811237732765498253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118127454993267908082657349 22148897811237732765498253)
            ·
              refine ⟨8305836679214149787061845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22148897811237732765498253 8305836679214149787061845)
              ·
                refine ⟨97334023584540817817131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8305836679214149787061845 97334023584540817817131)
                ·
                  rfl

theorem cell22_2559024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_2559024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559024 prefixEnd_2559024 := by exact prefixLift 2559024
  have htrace : WordTrace (prefixWord ++ tailWord_2559024) baseStart_2559024 baseEnd_2559024 := by
    simpa [prefixWord, tailWord_2559024, baseEnd_2559024] using wordTrace_append hprefix tailTrace_2559024
  have hstable : (prefixWord ++ tailWord_2559024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559024).length < 2 ^ (prefixWord ++ tailWord_2559024).sum := by decide
  have hdescent : baseEnd_2559024 < baseStart_2559024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559026 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2559026 : Nat := 118140960795 + 2559026 * 2 ^ 59
def prefixEnd_2559026 : Nat := 4983230072969 + 3 ^ 40 * 2559026 * 2
def baseEnd_2559026 : Nat := 876006896901740021804173

theorem tailTrace_2559026 : CollatzResearch.WordTrace tailWord_2559026 prefixEnd_2559026 876006896901740021804173 := by
  unfold tailWord_2559026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23333836506773330922708233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62223564018062215793888621 23333836506773330922708233)
  ·
    refine ⟨17500377380079998192031175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23333836506773330922708233 17500377380079998192031175)
    ·
      refine ⟨26250566070119997288046763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17500377380079998192031175 26250566070119997288046763)
      ·
        refine ⟨39375849105179995932070145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26250566070119997288046763 39375849105179995932070145)
        ·
          refine ⟨29531886828884996949052609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39375849105179995932070145 29531886828884996949052609)
          ·
            refine ⟨22148915121663747711789457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29531886828884996949052609 22148915121663747711789457)
            ·
              refine ⟨16611686341247810783842093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22148915121663747711789457 16611686341247810783842093)
              ·
                refine ⟨6229382377967929043940785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16611686341247810783842093 6229382377967929043940785)
                ·
                  refine ⟨4672036783475946782955589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6229382377967929043940785 4672036783475946782955589)
                  ·
                    refine ⟨876006896901740021804173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672036783475946782955589 876006896901740021804173)
                    ·
                      rfl

theorem cell22_2559026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2559026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559026 prefixEnd_2559026 := by exact prefixLift 2559026
  have htrace : WordTrace (prefixWord ++ tailWord_2559026) baseStart_2559026 baseEnd_2559026 := by
    simpa [prefixWord, tailWord_2559026, baseEnd_2559026] using wordTrace_append hprefix tailTrace_2559026
  have hstable : (prefixWord ++ tailWord_2559026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559026).length < 2 ^ (prefixWord ++ tailWord_2559026).sum := by decide
  have hdescent : baseEnd_2559026 < baseStart_2559026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559030 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2559030 : Nat := 118140960795 + 2559030 * 2 ^ 59
def prefixEnd_2559030 : Nat := 4983230072969 + 3 ^ 40 * 2559030 * 2
def baseEnd_2559030 : Nat := 292002755394495114901387

theorem tailTrace_2559030 : CollatzResearch.WordTrace tailWord_2559030 prefixEnd_2559030 292002755394495114901387 := by
  unfold tailWord_2559030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833468244942427023373659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62223661279385888249319029 5833468244942427023373659)
  ·
    refine ⟨8750202367413640535060489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5833468244942427023373659 8750202367413640535060489)
    ·
      refine ⟨6562651775560230401295367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8750202367413640535060489 6562651775560230401295367)
      ·
        refine ⟨9843977663340345601943051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6562651775560230401295367 9843977663340345601943051)
        ·
          refine ⟨14765966495010518402914577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9843977663340345601943051 14765966495010518402914577)
          ·
            refine ⟨11074474871257888802185933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14765966495010518402914577 11074474871257888802185933)
            ·
              refine ⟨4152928076721708300819725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11074474871257888802185933 4152928076721708300819725)
              ·
                refine ⟨1557348028770640612807397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4152928076721708300819725 1557348028770640612807397)
                ·
                  refine ⟨292002755394495114901387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557348028770640612807397 292002755394495114901387)
                  ·
                    rfl

theorem cell22_2559030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2559030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559030 prefixEnd_2559030 := by exact prefixLift 2559030
  have htrace : WordTrace (prefixWord ++ tailWord_2559030) baseStart_2559030 baseEnd_2559030 := by
    simpa [prefixWord, tailWord_2559030, baseEnd_2559030] using wordTrace_append hprefix tailTrace_2559030
  have hstable : (prefixWord ++ tailWord_2559030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559030).length < 2 ^ (prefixWord ++ tailWord_2559030).sum := by decide
  have hdescent : baseEnd_2559030 < baseStart_2559030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559090 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_2559090 : Nat := 118140960795 + 2559090 * 2 ^ 59
def prefixEnd_2559090 : Nat := 4983230072969 + 3 ^ 40 * 2559090 * 2
def baseEnd_2559090 : Nat := 876028805409665188203977

theorem tailTrace_2559090 : CollatzResearch.WordTrace tailWord_2559090 prefixEnd_2559090 876028805409665188203977 := by
  unfold tailWord_2559090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23334420074715365655290681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62225120199240975080775149 23334420074715365655290681)
  ·
    refine ⟨17500815056036524241468011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23334420074715365655290681 17500815056036524241468011)
    ·
      refine ⟨26251222584054786362202017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17500815056036524241468011 26251222584054786362202017)
      ·
        refine ⟨19688416938041089771651513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26251222584054786362202017 19688416938041089771651513)
        ·
          refine ⟨14766312703530817328738635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19688416938041089771651513 14766312703530817328738635)
          ·
            refine ⟨22149469055296225993107953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14766312703530817328738635 22149469055296225993107953)
            ·
              refine ⟨16612101791472169494830965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22149469055296225993107953 16612101791472169494830965)
              ·
                refine ⟨1557384542950515890140403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16612101791472169494830965 1557384542950515890140403)
                ·
                  refine ⟨2336076814425773835210605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557384542950515890140403 2336076814425773835210605)
                  ·
                    refine ⟨876028805409665188203977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336076814425773835210605 876028805409665188203977)
                    ·
                      rfl

theorem cell22_2559090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_2559090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559090 prefixEnd_2559090 := by exact prefixLift 2559090
  have htrace : WordTrace (prefixWord ++ tailWord_2559090) baseStart_2559090 baseEnd_2559090 := by
    simpa [prefixWord, tailWord_2559090, baseEnd_2559090] using wordTrace_append hprefix tailTrace_2559090
  have hstable : (prefixWord ++ tailWord_2559090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559090).length < 2 ^ (prefixWord ++ tailWord_2559090).sum := by decide
  have hdescent : baseEnd_2559090 < baseStart_2559090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559101 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2559101 : Nat := 118140960795 + 2559101 * 2 ^ 59
def prefixEnd_2559101 : Nat := 4983230072969 + 3 ^ 40 * 2559101 * 2
def baseEnd_2559101 : Nat := 876032570934464826178943

theorem tailTrace_2559101 : CollatzResearch.WordTrace tailWord_2559101 prefixEnd_2559101 876032570934464826178943 := by
  unfold tailWord_2559101
  simp only [CollatzResearch.WordTrace]
  refine ⟨93338081501821611499813157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62225387667881074333208771 93338081501821611499813157)
  ·
    refine ⟨17500890281591552156214967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93338081501821611499813157 17500890281591552156214967)
    ·
      refine ⟨26251335422387328234322451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17500890281591552156214967 26251335422387328234322451)
      ·
        refine ⟨39377003133580992351483677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26251335422387328234322451 39377003133580992351483677)
        ·
          refine ⟨14766376175092872131806379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39377003133580992351483677 14766376175092872131806379)
          ·
            refine ⟨22149564262639308197709569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14766376175092872131806379 22149564262639308197709569)
            ·
              refine ⟨16612173196979481148282177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22149564262639308197709569 16612173196979481148282177)
              ·
                refine ⟨12459129897734610861211633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16612173196979481148282177 12459129897734610861211633)
                ·
                  refine ⟨9344347423300958145908725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12459129897734610861211633 9344347423300958145908725)
                  ·
                    refine ⟨876032570934464826178943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9344347423300958145908725 876032570934464826178943)
                    ·
                      rfl

theorem cell22_2559101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2559101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559101 prefixEnd_2559101 := by exact prefixLift 2559101
  have htrace : WordTrace (prefixWord ++ tailWord_2559101) baseStart_2559101 baseEnd_2559101 := by
    simpa [prefixWord, tailWord_2559101, baseEnd_2559101] using wordTrace_append hprefix tailTrace_2559101
  have hstable : (prefixWord ++ tailWord_2559101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559101).length < 2 ^ (prefixWord ++ tailWord_2559101).sum := by decide
  have hdescent : baseEnd_2559101 < baseStart_2559101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559118 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2559118 : Nat := 118140960795 + 2559118 * 2 ^ 59
def prefixEnd_2559118 : Nat := 4983230072969 + 3 ^ 40 * 2559118 * 2
def baseEnd_2559118 : Nat := 876038390381882448503891

theorem tailTrace_2559118 : CollatzResearch.WordTrace tailWord_2559118 prefixEnd_2559118 876038390381882448503891 := by
  unfold tailWord_2559118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11667337692845002925397751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62225801028506682268788005 11667337692845002925397751)
  ·
    refine ⟨17501006539267504388096627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11667337692845002925397751 17501006539267504388096627)
    ·
      refine ⟨26251509808901256582144941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17501006539267504388096627 26251509808901256582144941)
      ·
        refine ⟨9844316178337971218304353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26251509808901256582144941 9844316178337971218304353)
        ·
          refine ⟨7383237133753478413728265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9844316178337971218304353 7383237133753478413728265)
          ·
            refine ⟨5537427850315108810296199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383237133753478413728265 5537427850315108810296199)
            ·
              refine ⟨8306141775472663215444299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537427850315108810296199 8306141775472663215444299)
              ·
                refine ⟨12459212663208994823166449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306141775472663215444299 12459212663208994823166449)
                ·
                  refine ⟨9344409497406746117374837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12459212663208994823166449 9344409497406746117374837)
                  ·
                    refine ⟨876038390381882448503891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9344409497406746117374837 876038390381882448503891)
                    ·
                      rfl

theorem cell22_2559118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2559118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559118 prefixEnd_2559118 := by exact prefixLift 2559118
  have htrace : WordTrace (prefixWord ++ tailWord_2559118) baseStart_2559118 baseEnd_2559118 := by
    simpa [prefixWord, tailWord_2559118, baseEnd_2559118] using wordTrace_append hprefix tailTrace_2559118
  have hstable : (prefixWord ++ tailWord_2559118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559118).length < 2 ^ (prefixWord ++ tailWord_2559118).sum := by decide
  have hdescent : baseEnd_2559118 < baseStart_2559118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559133 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2559133 : Nat := 118140960795 + 2559133 * 2 ^ 59
def prefixEnd_2559133 : Nat := 4983230072969 + 3 ^ 40 * 2559133 * 2
def baseEnd_2559133 : Nat := 876043525188427409378845

theorem tailTrace_2559133 : CollatzResearch.WordTrace tailWord_2559133 prefixEnd_2559133 876043525188427409378845 := by
  unfold tailWord_2559133
  simp only [CollatzResearch.WordTrace]
  refine ⟨93339248637705680964978053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62226165758470453976652035 93339248637705680964978053)
  ·
    refine ⟨17501109119569815180933385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93339248637705680964978053 17501109119569815180933385)
    ·
      refine ⟨13125831839677361385700039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17501109119569815180933385 13125831839677361385700039)
      ·
        refine ⟨19688747759516042078550059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13125831839677361385700039 19688747759516042078550059)
        ·
          refine ⟨29533121639274063117825089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19688747759516042078550059 29533121639274063117825089)
          ·
            refine ⟨22149841229455547338368817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29533121639274063117825089 22149841229455547338368817)
            ·
              refine ⟨16612380922091660503776613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22149841229455547338368817 16612380922091660503776613)
              ·
                refine ⟨3114821422892186344458115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16612380922091660503776613 3114821422892186344458115)
                ·
                  refine ⟨4672232134338279516687173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114821422892186344458115 4672232134338279516687173)
                  ·
                    refine ⟨876043525188427409378845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672232134338279516687173 876043525188427409378845)
                    ·
                      rfl

theorem cell22_2559133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2559133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559133 prefixEnd_2559133 := by exact prefixLift 2559133
  have htrace : WordTrace (prefixWord ++ tailWord_2559133) baseStart_2559133 baseEnd_2559133 := by
    simpa [prefixWord, tailWord_2559133, baseEnd_2559133] using wordTrace_append hprefix tailTrace_2559133
  have hstable : (prefixWord ++ tailWord_2559133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559133).length < 2 ^ (prefixWord ++ tailWord_2559133).sum := by decide
  have hdescent : baseEnd_2559133 < baseStart_2559133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559163 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 2, 3]
def baseStart_2559163 : Nat := 118140960795 + 2559163 * 2 ^ 59
def prefixEnd_2559163 : Nat := 4983230072969 + 3 ^ 40 * 2559163 * 2
def baseEnd_2559163 : Nat := 876053794801517331128753

theorem tailTrace_2559163 : CollatzResearch.WordTrace tailWord_2559163 prefixEnd_2559163 876053794801517331128753 := by
  unfold tailWord_2559163
  simp only [CollatzResearch.WordTrace]
  refine ⟨93340342827596996088570143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62226895218397997392380095 93340342827596996088570143)
  ·
    refine ⟨140010514241395494132855215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93340342827596996088570143 140010514241395494132855215)
    ·
      refine ⟨210015771362093241199282823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140010514241395494132855215 210015771362093241199282823)
      ·
        refine ⟨315023657043139861798924235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210015771362093241199282823 315023657043139861798924235)
        ·
          refine ⟨472535485564709792698386353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315023657043139861798924235 472535485564709792698386353)
          ·
            refine ⟨354401614173532344523789765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472535485564709792698386353 354401614173532344523789765)
            ·
              refine ⟨66450302657537314598210581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 354401614173532344523789765 66450302657537314598210581)
              ·
                refine ⟨3114857937072061621791121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66450302657537314598210581 3114857937072061621791121)
                ·
                  refine ⟨2336143452804046216343341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114857937072061621791121 2336143452804046216343341)
                  ·
                    refine ⟨876053794801517331128753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336143452804046216343341 876053794801517331128753)
                    ·
                      rfl

theorem cell22_2559163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3].length) (baseStart_2559163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559163 prefixEnd_2559163 := by exact prefixLift 2559163
  have htrace : WordTrace (prefixWord ++ tailWord_2559163) baseStart_2559163 baseEnd_2559163 := by
    simpa [prefixWord, tailWord_2559163, baseEnd_2559163] using wordTrace_append hprefix tailTrace_2559163
  have hstable : (prefixWord ++ tailWord_2559163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559163).length < 2 ^ (prefixWord ++ tailWord_2559163).sum := by decide
  have hdescent : baseEnd_2559163 < baseStart_2559163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559300 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_2559300 : Nat := 118140960795 + 2559300 * 2 ^ 59
def prefixEnd_2559300 : Nat := 4983230072969 + 3 ^ 40 * 2559300 * 2
def baseEnd_2559300 : Nat := 292033564233764880151111

theorem tailTrace_2559300 : CollatzResearch.WordTrace tailWord_2559300 prefixEnd_2559300 292033564233764880151111 := by
  unfold tailWord_2559300
  simp only [CollatzResearch.WordTrace]
  refine ⟨46672669814050334243153677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62230226418733778990871569 46672669814050334243153677)
  ·
    refine ⟨17502251180268875341182629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46672669814050334243153677 17502251180268875341182629)
    ·
      refine ⟨3281672096300414126471743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17502251180268875341182629 3281672096300414126471743)
      ·
        refine ⟨4922508144450621189707615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281672096300414126471743 4922508144450621189707615)
        ·
          refine ⟨7383762216675931784561423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922508144450621189707615 7383762216675931784561423)
          ·
            refine ⟨11075643325013897676842135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383762216675931784561423 11075643325013897676842135)
            ·
              refine ⟨16613464987520846515263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11075643325013897676842135 16613464987520846515263203)
              ·
                refine ⟨24920197481281269772894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16613464987520846515263203 24920197481281269772894805)
                ·
                  refine ⟨292033564233764880151111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24920197481281269772894805 292033564233764880151111)
                  ·
                    rfl

theorem cell22_2559300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_2559300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559300 prefixEnd_2559300 := by exact prefixLift 2559300
  have htrace : WordTrace (prefixWord ++ tailWord_2559300) baseStart_2559300 baseEnd_2559300 := by
    simpa [prefixWord, tailWord_2559300, baseEnd_2559300] using wordTrace_append hprefix tailTrace_2559300
  have hstable : (prefixWord ++ tailWord_2559300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559300).length < 2 ^ (prefixWord ++ tailWord_2559300).sum := by decide
  have hdescent : baseEnd_2559300 < baseStart_2559300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559313 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2559313 : Nat := 118140960795 + 2559313 * 2 ^ 59
def prefixEnd_2559313 : Nat := 4983230072969 + 3 ^ 40 * 2559313 * 2
def baseEnd_2559313 : Nat := 876105142866966939878293

theorem tailTrace_2559313 : CollatzResearch.WordTrace tailWord_2559313 prefixEnd_2559313 876105142866966939878293 := by
  unfold tailWord_2559313
  simp only [CollatzResearch.WordTrace]
  refine ⟨93345813777053571706530593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62230542518035714471020395 93345813777053571706530593)
  ·
    refine ⟨70009360332790178779897945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93345813777053571706530593 70009360332790178779897945)
    ·
      refine ⟨52507020249592634084923459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70009360332790178779897945 52507020249592634084923459)
      ·
        refine ⟨78760530374388951127385189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52507020249592634084923459 78760530374388951127385189)
        ·
          refine ⟨14767599445197928336384723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78760530374388951127385189 14767599445197928336384723)
          ·
            refine ⟨22151399167796892504577085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14767599445197928336384723 22151399167796892504577085)
            ·
              refine ⟨8306774687923834689216407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22151399167796892504577085 8306774687923834689216407)
              ·
                refine ⟨12460162031885752033824611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306774687923834689216407 12460162031885752033824611)
                ·
                  refine ⟨18690243047828628050736917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12460162031885752033824611 18690243047828628050736917)
                  ·
                    refine ⟨876105142866966939878293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18690243047828628050736917 876105142866966939878293)
                    ·
                      rfl

theorem cell22_2559313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2559313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559313 prefixEnd_2559313 := by exact prefixLift 2559313
  have htrace : WordTrace (prefixWord ++ tailWord_2559313) baseStart_2559313 baseEnd_2559313 := by
    simpa [prefixWord, tailWord_2559313, baseEnd_2559313] using wordTrace_append hprefix tailTrace_2559313
  have hstable : (prefixWord ++ tailWord_2559313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559313).length < 2 ^ (prefixWord ++ tailWord_2559313).sum := by decide
  have hdescent : baseEnd_2559313 < baseStart_2559313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559317 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 4]
def baseStart_2559317 : Nat := 118140960795 + 2559317 * 2 ^ 59
def prefixEnd_2559317 : Nat := 4983230072969 + 3 ^ 40 * 2559317 * 2
def baseEnd_2559317 : Nat := 292035504049570754259427

theorem tailTrace_2559317 : CollatzResearch.WordTrace tailWord_2559317 prefixEnd_2559317 292035504049570754259427 := by
  unfold tailWord_2559317
  simp only [CollatzResearch.WordTrace]
  refine ⟨93345959669039080389676205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62230639779359386926450803 93345959669039080389676205)
  ·
    refine ⟨35004734875889655146128577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93345959669039080389676205 35004734875889655146128577)
    ·
      refine ⟨26253551156917241359596433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35004734875889655146128577 26253551156917241359596433)
      ·
        refine ⟨19690163367687931019697325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26253551156917241359596433 19690163367687931019697325)
        ·
          refine ⟨7383811262882974132386497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19690163367687931019697325 7383811262882974132386497)
          ·
            refine ⟨5537858447162230599289873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383811262882974132386497 5537858447162230599289873)
            ·
              refine ⟨4153393835371672949467405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537858447162230599289873 4153393835371672949467405)
              ·
                refine ⟨1557522688264377356050277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4153393835371672949467405 1557522688264377356050277)
                ·
                  refine ⟨292035504049570754259427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557522688264377356050277 292035504049570754259427)
                  ·
                    rfl

theorem cell22_2559317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_2559317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559317 prefixEnd_2559317 := by exact prefixLift 2559317
  have htrace : WordTrace (prefixWord ++ tailWord_2559317) baseStart_2559317 baseEnd_2559317 := by
    simpa [prefixWord, tailWord_2559317, baseEnd_2559317] using wordTrace_append hprefix tailTrace_2559317
  have hstable : (prefixWord ++ tailWord_2559317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559317).length < 2 ^ (prefixWord ++ tailWord_2559317).sum := by decide
  have hdescent : baseEnd_2559317 < baseStart_2559317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559328 : List Nat := [2, 1, 1, 3, 4, 2, 9]
def baseStart_2559328 : Nat := 118140960795 + 2559328 * 2 ^ 59
def prefixEnd_2559328 : Nat := 4983230072969 + 3 ^ 40 * 2559328 * 2
def baseEnd_2559328 : Nat := 32448528802722662990861

theorem tailTrace_2559328 : CollatzResearch.WordTrace tailWord_2559328 prefixEnd_2559328 32448528802722662990861 := by
  unfold tailWord_2559328
  simp only [CollatzResearch.WordTrace]
  refine ⟨46673180435999614634163319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62230907247999486178884425 46673180435999614634163319)
  ·
    refine ⟨70009770653999421951244979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46673180435999614634163319 70009770653999421951244979)
    ·
      refine ⟨105014655980999132926867469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70009770653999421951244979 105014655980999132926867469)
      ·
        refine ⟨39380495992874674847575301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105014655980999132926867469 39380495992874674847575301)
        ·
          refine ⟨7383842998664001533920369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39380495992874674847575301 7383842998664001533920369)
          ·
            refine ⟨5537882248998001150440277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383842998664001533920369 5537882248998001150440277)
            ·
              refine ⟨32448528802722662990861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5537882248998001150440277 32448528802722662990861)
              ·
                rfl

theorem cell22_2559328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 9].length) (baseStart_2559328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559328 prefixEnd_2559328 := by exact prefixLift 2559328
  have htrace : WordTrace (prefixWord ++ tailWord_2559328) baseStart_2559328 baseEnd_2559328 := by
    simpa [prefixWord, tailWord_2559328, baseEnd_2559328] using wordTrace_append hprefix tailTrace_2559328
  have hstable : (prefixWord ++ tailWord_2559328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559328).length < 2 ^ (prefixWord ++ tailWord_2559328).sum := by decide
  have hdescent : baseEnd_2559328 < baseStart_2559328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559330 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2559330 : Nat := 118140960795 + 2559330 * 2 ^ 59
def prefixEnd_2559330 : Nat := 4983230072969 + 3 ^ 40 * 2559330 * 2
def baseEnd_2559330 : Nat := 876110962314384562203241

theorem tailTrace_2559330 : CollatzResearch.WordTrace tailWord_2559330 prefixEnd_2559330 876110962314384562203241 := by
  unfold tailWord_2559330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336608454497995902474861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62230955878661322406599629 23336608454497995902474861)
  ·
    refine ⟨8751228170436748463428073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23336608454497995902474861 8751228170436748463428073)
    ·
      refine ⟨6563421127827561347571055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8751228170436748463428073 6563421127827561347571055)
      ·
        refine ⟨9845131691741342021356583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563421127827561347571055 9845131691741342021356583)
        ·
          refine ⟨14767697537612013032034875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845131691741342021356583 14767697537612013032034875)
          ·
            refine ⟨22151546306418019548052313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14767697537612013032034875 22151546306418019548052313)
            ·
              refine ⟨16613659729813514661039235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22151546306418019548052313 16613659729813514661039235)
              ·
                refine ⟨24920489594720271991558853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16613659729813514661039235 24920489594720271991558853)
                ·
                  refine ⟨4672591799010050998417285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24920489594720271991558853 4672591799010050998417285)
                  ·
                    refine ⟨876110962314384562203241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672591799010050998417285 876110962314384562203241)
                    ·
                      rfl

theorem cell22_2559330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2559330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559330 prefixEnd_2559330 := by exact prefixLift 2559330
  have htrace : WordTrace (prefixWord ++ tailWord_2559330) baseStart_2559330 baseEnd_2559330 := by
    simpa [prefixWord, tailWord_2559330, baseEnd_2559330] using wordTrace_append hprefix tailTrace_2559330
  have hstable : (prefixWord ++ tailWord_2559330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559330).length < 2 ^ (prefixWord ++ tailWord_2559330).sum := by decide
  have hdescent : baseEnd_2559330 < baseStart_2559330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559332 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2559332 : Nat := 118140960795 + 2559332 * 2 ^ 59
def prefixEnd_2559332 : Nat := 4983230072969 + 3 ^ 40 * 2559332 * 2
def baseEnd_2559332 : Nat := 876111646955257223653235

theorem tailTrace_2559332 : CollatzResearch.WordTrace tailWord_2559332 prefixEnd_2559332 876111646955257223653235 := by
  unfold tailWord_2559332
  simp only [CollatzResearch.WordTrace]
  refine ⟨46673253381992368975736125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62231004509323158634314833 46673253381992368975736125)
  ·
    refine ⟨17502470018247138365901047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46673253381992368975736125 17502470018247138365901047)
    ·
      refine ⟨26253705027370707548851571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17502470018247138365901047 26253705027370707548851571)
      ·
        refine ⟨39380557541056061323277357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26253705027370707548851571 39380557541056061323277357)
        ·
          refine ⟨14767709077896022996229009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39380557541056061323277357 14767709077896022996229009)
          ·
            refine ⟨11075781808422017247171757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14767709077896022996229009 11075781808422017247171757)
            ·
              refine ⟨4153418178158256467689409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11075781808422017247171757 4153418178158256467689409)
              ·
                refine ⟨3115063633618692350767057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153418178158256467689409 3115063633618692350767057)
                ·
                  refine ⟨2336297725214019263075293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115063633618692350767057 2336297725214019263075293)
                  ·
                    refine ⟨876111646955257223653235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336297725214019263075293 876111646955257223653235)
                    ·
                      rfl

theorem cell22_2559332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2559332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559332 prefixEnd_2559332 := by exact prefixLift 2559332
  have htrace : WordTrace (prefixWord ++ tailWord_2559332) baseStart_2559332 baseEnd_2559332 := by
    simpa [prefixWord, tailWord_2559332, baseEnd_2559332] using wordTrace_append hprefix tailTrace_2559332
  have hstable : (prefixWord ++ tailWord_2559332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559332).length < 2 ^ (prefixWord ++ tailWord_2559332).sum := by decide
  have hdescent : baseEnd_2559332 < baseStart_2559332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559349 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2559349 : Nat := 118140960795 + 2559349 * 2 ^ 59
def prefixEnd_2559349 : Nat := 4983230072969 + 3 ^ 40 * 2559349 * 2
def baseEnd_2559349 : Nat := 876117466402674845978183

theorem tailTrace_2559349 : CollatzResearch.WordTrace tailWord_2559349 prefixEnd_2559349 876117466402674845978183 := by
  unfold tailWord_2559349
  simp only [CollatzResearch.WordTrace]
  refine ⟨93347126804923149854841101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62231417869948766569894067 93347126804923149854841101)
  ·
    refine ⟨35005172551846181195565413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93347126804923149854841101 35005172551846181195565413)
    ·
      refine ⟨6563469853471158974168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35005172551846181195565413 6563469853471158974168515)
      ·
        refine ⟨9845204780206738461252773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563469853471158974168515 9845204780206738461252773)
        ·
          refine ⟨1845975896288763461484895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9845204780206738461252773 1845975896288763461484895)
          ·
            refine ⟨2768963844433145192227343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845975896288763461484895 2768963844433145192227343)
            ·
              refine ⟨4153445766649717788341015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768963844433145192227343 4153445766649717788341015)
              ·
                refine ⟨6230168649974576682511523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153445766649717788341015 6230168649974576682511523)
                ·
                  refine ⟨9345252974961865023767285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230168649974576682511523 9345252974961865023767285)
                  ·
                    refine ⟨876117466402674845978183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9345252974961865023767285 876117466402674845978183)
                    ·
                      rfl

theorem cell22_2559349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2559349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559349 prefixEnd_2559349 := by exact prefixLift 2559349
  have htrace : WordTrace (prefixWord ++ tailWord_2559349) baseStart_2559349 baseEnd_2559349 := by
    simpa [prefixWord, tailWord_2559349, baseEnd_2559349] using wordTrace_append hprefix tailTrace_2559349
  have hstable : (prefixWord ++ tailWord_2559349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559349).length < 2 ^ (prefixWord ++ tailWord_2559349).sum := by decide
  have hdescent : baseEnd_2559349 < baseStart_2559349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559362 : List Nat := [3, 4, 2, 1, 1, 2, 1, 8]
def baseStart_2559362 : Nat := 118140960795 + 2559362 * 2 ^ 59
def prefixEnd_2559362 : Nat := 4983230072969 + 3 ^ 40 * 2559362 * 2
def baseEnd_2559362 : Nat := 97346879618705238378127

theorem tailTrace_2559362 : CollatzResearch.WordTrace tailWord_2559362 prefixEnd_2559362 97346879618705238378127 := by
  unfold tailWord_2559362
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336900238469013268766085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62231733969250702050042893 23336900238469013268766085)
  ·
    refine ⟨4375668794712939987893641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23336900238469013268766085 4375668794712939987893641)
    ·
      refine ⟨3281751596034704990920231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4375668794712939987893641 3281751596034704990920231)
      ·
        refine ⟨4922627394052057486380347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281751596034704990920231 4922627394052057486380347)
        ·
          refine ⟨7383941091078086229570521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922627394052057486380347 7383941091078086229570521)
          ·
            refine ⟨5537955818308564672177891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383941091078086229570521 5537955818308564672177891)
            ·
              refine ⟨8306933727462847008266837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537955818308564672177891 8306933727462847008266837)
              ·
                refine ⟨97346879618705238378127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8306933727462847008266837 97346879618705238378127)
                ·
                  rfl

theorem cell22_2559362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_2559362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559362 prefixEnd_2559362 := by exact prefixLift 2559362
  have htrace : WordTrace (prefixWord ++ tailWord_2559362) baseStart_2559362 baseEnd_2559362 := by
    simpa [prefixWord, tailWord_2559362, baseEnd_2559362] using wordTrace_append hprefix tailTrace_2559362
  have hstable : (prefixWord ++ tailWord_2559362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559362).length < 2 ^ (prefixWord ++ tailWord_2559362).sum := by decide
  have hdescent : baseEnd_2559362 < baseStart_2559362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559394 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2559394 : Nat := 118140960795 + 2559394 * 2 ^ 59
def prefixEnd_2559394 : Nat := 4983230072969 + 3 ^ 40 * 2559394 * 2
def baseEnd_2559394 : Nat := 876132870822309728603045

theorem tailTrace_2559394 : CollatzResearch.WordTrace tailWord_2559394 prefixEnd_2559394 876132870822309728603045 := by
  unfold tailWord_2559394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23337192022440030635057309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62232512059840081693486157 23337192022440030635057309)
  ·
    refine ⟨8751447008415011488146491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23337192022440030635057309 8751447008415011488146491)
    ·
      refine ⟨13127170512622517232219737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8751447008415011488146491 13127170512622517232219737)
      ·
        refine ⟨9845377884466887924164803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13127170512622517232219737 9845377884466887924164803)
        ·
          refine ⟨14768066826700331886247205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845377884466887924164803 14768066826700331886247205)
          ·
            refine ⟨2769012530006312228671351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14768066826700331886247205 2769012530006312228671351)
            ·
              refine ⟨4153518795009468343007027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769012530006312228671351 4153518795009468343007027)
              ·
                refine ⟨6230278192514202514510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153518795009468343007027 6230278192514202514510541)
                ·
                  refine ⟨2336354322192825942941453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6230278192514202514510541 2336354322192825942941453)
                  ·
                    refine ⟨876132870822309728603045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336354322192825942941453 876132870822309728603045)
                    ·
                      rfl

theorem cell22_2559394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2559394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559394 prefixEnd_2559394 := by exact prefixLift 2559394
  have htrace : WordTrace (prefixWord ++ tailWord_2559394) baseStart_2559394 baseEnd_2559394 := by
    simpa [prefixWord, tailWord_2559394, baseEnd_2559394] using wordTrace_append hprefix tailTrace_2559394
  have hstable : (prefixWord ++ tailWord_2559394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559394).length < 2 ^ (prefixWord ++ tailWord_2559394).sum := by decide
  have hdescent : baseEnd_2559394 < baseStart_2559394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559555 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_2559555 : Nat := 118140960795 + 2559555 * 2 ^ 59
def prefixEnd_2559555 : Nat := 4983230072969 + 3 ^ 40 * 2559555 * 2
def baseEnd_2559555 : Nat := 876187984412558975327551

theorem tailTrace_2559555 : CollatzResearch.WordTrace tailWord_2559555 prefixEnd_2559555 876187984412558975327551 := by
  unfold tailWord_2559555
  simp only [CollatzResearch.WordTrace]
  refine ⟨93354640242176847036840119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62236426828117898024560079 93354640242176847036840119)
  ·
    refine ⟨140031960363265270555260179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93354640242176847036840119 140031960363265270555260179)
    ·
      refine ⟨210047940544897905832890269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140031960363265270555260179 210047940544897905832890269)
      ·
        refine ⟨78767977704336714687333851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210047940544897905832890269 78767977704336714687333851)
        ·
          refine ⟨118151966556505072031000777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78767977704336714687333851 118151966556505072031000777)
          ·
            refine ⟨88613974917378804023250583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118151966556505072031000777 88613974917378804023250583)
            ·
              refine ⟨132920962376068206034875875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88613974917378804023250583 132920962376068206034875875)
              ·
                refine ⟨199381443564102309052313813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132920962376068206034875875 199381443564102309052313813)
                ·
                  refine ⟨4673002583533647868413605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 199381443564102309052313813 4673002583533647868413605)
                  ·
                    refine ⟨876187984412558975327551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673002583533647868413605 876187984412558975327551)
                    ·
                      rfl

theorem cell22_2559555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_2559555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559555 prefixEnd_2559555 := by exact prefixLift 2559555
  have htrace : WordTrace (prefixWord ++ tailWord_2559555) baseStart_2559555 baseEnd_2559555 := by
    simpa [prefixWord, tailWord_2559555, baseEnd_2559555] using wordTrace_append hprefix tailTrace_2559555
  have hstable : (prefixWord ++ tailWord_2559555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559555).length < 2 ^ (prefixWord ++ tailWord_2559555).sum := by decide
  have hdescent : baseEnd_2559555 < baseStart_2559555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559572 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2559572 : Nat := 118140960795 + 2559572 * 2 ^ 59
def prefixEnd_2559572 : Nat := 4983230072969 + 3 ^ 40 * 2559572 * 2
def baseEnd_2559572 : Nat := 876193803859976597652499

theorem tailTrace_2559572 : CollatzResearch.WordTrace tailWord_2559572 prefixEnd_2559572 876193803859976597652499 := by
  unfold tailWord_2559572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46677630141557629470104485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62236840188743505960139313 46677630141557629470104485)
  ·
    refine ⟨8752055651542055525644591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46677630141557629470104485 8752055651542055525644591)
    ·
      refine ⟨13128083477313083288466887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8752055651542055525644591 13128083477313083288466887)
      ·
        refine ⟨19692125215969624932700331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13128083477313083288466887 19692125215969624932700331)
        ·
          refine ⟨29538187823954437399050497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19692125215969624932700331 29538187823954437399050497)
          ·
            refine ⟨22153640867965828049287873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29538187823954437399050497 22153640867965828049287873)
            ·
              refine ⟨16615230650974371036965905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22153640867965828049287873 16615230650974371036965905)
              ·
                refine ⟨12461422988230778277724429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16615230650974371036965905 12461422988230778277724429)
                ·
                  refine ⟨4673033620586541854146661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12461422988230778277724429 4673033620586541854146661)
                  ·
                    refine ⟨876193803859976597652499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673033620586541854146661 876193803859976597652499)
                    ·
                      rfl

theorem cell22_2559572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2559572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559572 prefixEnd_2559572 := by exact prefixLift 2559572
  have htrace : WordTrace (prefixWord ++ tailWord_2559572) baseStart_2559572 baseEnd_2559572 := by
    simpa [prefixWord, tailWord_2559572, baseEnd_2559572] using wordTrace_append hprefix tailTrace_2559572
  have hstable : (prefixWord ++ tailWord_2559572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559572).length < 2 ^ (prefixWord ++ tailWord_2559572).sum := by decide
  have hdescent : baseEnd_2559572 < baseStart_2559572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559589 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2559589 : Nat := 118140960795 + 2559589 * 2 ^ 59
def prefixEnd_2559589 : Nat := 4983230072969 + 3 ^ 40 * 2559589 * 2
def baseEnd_2559589 : Nat := 876199623307394219977447

theorem tailTrace_2559589 : CollatzResearch.WordTrace tailWord_2559589 prefixEnd_2559589 876199623307394219977447 := by
  unfold tailWord_2559589
  simp only [CollatzResearch.WordTrace]
  refine ⟨93355880324053670843577821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62237253549369113895718547 93355880324053670843577821)
  ·
    refine ⟨35008455121520126566341683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93355880324053670843577821 35008455121520126566341683)
    ·
      refine ⟨52512682682280189849512525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35008455121520126566341683 52512682682280189849512525)
      ·
        refine ⟨19692256005855071193567197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52512682682280189849512525 19692256005855071193567197)
        ·
          refine ⟨7384596002195651697587699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19692256005855071193567197 7384596002195651697587699)
          ·
            refine ⟨11076894003293477546381549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7384596002195651697587699 11076894003293477546381549)
            ·
              refine ⟨4153835251235054079893081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11076894003293477546381549 4153835251235054079893081)
              ·
                refine ⟨3115376438426290559919811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153835251235054079893081 3115376438426290559919811)
                ·
                  refine ⟨4673064657639435839879717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115376438426290559919811 4673064657639435839879717)
                  ·
                    refine ⟨876199623307394219977447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673064657639435839879717 876199623307394219977447)
                    ·
                      rfl

theorem cell22_2559589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2559589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559589 prefixEnd_2559589 := by exact prefixLift 2559589
  have htrace : WordTrace (prefixWord ++ tailWord_2559589) baseStart_2559589 baseEnd_2559589 := by
    simpa [prefixWord, tailWord_2559589, baseEnd_2559589] using wordTrace_append hprefix tailTrace_2559589
  have hstable : (prefixWord ++ tailWord_2559589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559589).length < 2 ^ (prefixWord ++ tailWord_2559589).sum := by decide
  have hdescent : baseEnd_2559589 < baseStart_2559589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559602 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2559602 : Nat := 118140960795 + 2559602 * 2 ^ 59
def prefixEnd_2559602 : Nat := 4983230072969 + 3 ^ 40 * 2559602 * 2
def baseEnd_2559602 : Nat := 876204073473066519402407

theorem tailTrace_2559602 : CollatzResearch.WordTrace tailWord_2559602 prefixEnd_2559602 876204073473066519402407 := by
  unfold tailWord_2559602
  simp only [CollatzResearch.WordTrace]
  refine ⟨23339088618251643515950265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62237569648671049375867373 23339088618251643515950265)
  ·
    refine ⟨17504316463688732636962699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23339088618251643515950265 17504316463688732636962699)
    ·
      refine ⟨26256474695533098955444049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17504316463688732636962699 26256474695533098955444049)
      ·
        refine ⟨19692356021649824216583037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26256474695533098955444049 19692356021649824216583037)
        ·
          refine ⟨7384633508118684081218639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19692356021649824216583037 7384633508118684081218639)
          ·
            refine ⟨11076950262178026121827959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7384633508118684081218639 11076950262178026121827959)
            ·
              refine ⟨16615425393267039182741939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11076950262178026121827959 16615425393267039182741939)
              ·
                refine ⟨24923138089900558774112909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16615425393267039182741939 24923138089900558774112909)
                ·
                  refine ⟨9346176783712709540292341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24923138089900558774112909 9346176783712709540292341)
                  ·
                    refine ⟨876204073473066519402407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9346176783712709540292341 876204073473066519402407)
                    ·
                      rfl

theorem cell22_2559602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2559602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559602 prefixEnd_2559602 := by exact prefixLift 2559602
  have htrace : WordTrace (prefixWord ++ tailWord_2559602) baseStart_2559602 baseEnd_2559602 := by
    simpa [prefixWord, tailWord_2559602, baseEnd_2559602] using wordTrace_append hprefix tailTrace_2559602
  have hstable : (prefixWord ++ tailWord_2559602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559602).length < 2 ^ (prefixWord ++ tailWord_2559602).sum := by decide
  have hdescent : baseEnd_2559602 < baseStart_2559602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559636 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2559636 : Nat := 118140960795 + 2559636 * 2 ^ 59
def prefixEnd_2559636 : Nat := 4983230072969 + 3 ^ 40 * 2559636 * 2
def baseEnd_2559636 : Nat := 876215712367901764052303

theorem tailTrace_2559636 : CollatzResearch.WordTrace tailWord_2559636 prefixEnd_2559636 876215712367901764052303 := by
  unfold tailWord_2559636
  simp only [CollatzResearch.WordTrace]
  refine ⟨46678797277441698935269381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62238396369922265247025841 46678797277441698935269381)
  ·
    refine ⟨8752274489520318550363009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46678797277441698935269381 8752274489520318550363009)
    ·
      refine ⟨6564205867140238912772257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8752274489520318550363009 6564205867140238912772257)
      ·
        refine ⟨4923154400355179184579193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6564205867140238912772257 4923154400355179184579193)
        ·
          refine ⟨3692365800266384388434395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923154400355179184579193 3692365800266384388434395)
          ·
            refine ⟨5538548700399576582651593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692365800266384388434395 5538548700399576582651593)
            ·
              refine ⟨4153911525299682436988695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538548700399576582651593 4153911525299682436988695)
              ·
                refine ⟨6230867287949523655483043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153911525299682436988695 6230867287949523655483043)
                ·
                  refine ⟨9346300931924285483224565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230867287949523655483043 9346300931924285483224565)
                  ·
                    refine ⟨876215712367901764052303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9346300931924285483224565 876215712367901764052303)
                    ·
                      rfl

theorem cell22_2559636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2559636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559636 prefixEnd_2559636 := by exact prefixLift 2559636
  have htrace : WordTrace (prefixWord ++ tailWord_2559636) baseStart_2559636 baseEnd_2559636 := by
    simpa [prefixWord, tailWord_2559636, baseEnd_2559636] using wordTrace_append hprefix tailTrace_2559636
  have hstable : (prefixWord ++ tailWord_2559636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559636).length < 2 ^ (prefixWord ++ tailWord_2559636).sum := by decide
  have hdescent : baseEnd_2559636 < baseStart_2559636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559649 : List Nat := [1, 2, 3, 3, 2, 2, 3, 6]
def baseStart_2559649 : Nat := 118140960795 + 2559649 * 2 ^ 59
def prefixEnd_2559649 : Nat := 4983230072969 + 3 ^ 40 * 2559649 * 2
def baseEnd_2559649 : Nat := 97357795837063784830807

theorem tailTrace_2559649 : CollatzResearch.WordTrace tailWord_2559649 prefixEnd_2559649 97357795837063784830807 := by
  unfold tailWord_2559649
  simp only [CollatzResearch.WordTrace]
  refine ⟨93358068703836301090762001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62238712469224200727174667 93358068703836301090762001)
  ·
    refine ⟨70018551527877225818071501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93358068703836301090762001 70018551527877225818071501)
    ·
      refine ⟨26256956822953959681776813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70018551527877225818071501 26256956822953959681776813)
      ·
        refine ⟨9846358808607734880666305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26256956822953959681776813 9846358808607734880666305)
        ·
          refine ⟨7384769106455801160499729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9846358808607734880666305 7384769106455801160499729)
          ·
            refine ⟨5538576829841850870374797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7384769106455801160499729 5538576829841850870374797)
            ·
              refine ⟨2076966311190694076390549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5538576829841850870374797 2076966311190694076390549)
              ·
                refine ⟨97357795837063784830807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2076966311190694076390549 97357795837063784830807)
                ·
                  rfl

theorem cell22_2559649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 6].length) (baseStart_2559649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559649 prefixEnd_2559649 := by exact prefixLift 2559649
  have htrace : WordTrace (prefixWord ++ tailWord_2559649) baseStart_2559649 baseEnd_2559649 := by
    simpa [prefixWord, tailWord_2559649, baseEnd_2559649] using wordTrace_append hprefix tailTrace_2559649
  have hstable : (prefixWord ++ tailWord_2559649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559649).length < 2 ^ (prefixWord ++ tailWord_2559649).sum := by decide
  have hdescent : baseEnd_2559649 < baseStart_2559649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559670 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2559670 : Nat := 118140960795 + 2559670 * 2 ^ 59
def prefixEnd_2559670 : Nat := 4983230072969 + 3 ^ 40 * 2559670 * 2
def baseEnd_2559670 : Nat := 876227351262737008702199

theorem tailTrace_2559670 : CollatzResearch.WordTrace tailWord_2559670 prefixEnd_2559670 876227351262737008702199 := by
  unfold tailWord_2559670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834927164797513854829779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62239223091173481118184309 5834927164797513854829779)
  ·
    refine ⟨8752390747196270782244669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5834927164797513854829779 8752390747196270782244669)
    ·
      refine ⟨3282146530198601543341751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8752390747196270782244669 3282146530198601543341751)
      ·
        refine ⟨4923219795297902315012627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282146530198601543341751 4923219795297902315012627)
        ·
          refine ⟨7384829692946853472518941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923219795297902315012627 7384829692946853472518941)
          ·
            refine ⟨2769311134855070052194603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7384829692946853472518941 2769311134855070052194603)
            ·
              refine ⟨4153966702282605078291905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769311134855070052194603 4153966702282605078291905)
              ·
                refine ⟨3115475026711953808718929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153966702282605078291905 3115475026711953808718929)
                ·
                  refine ⟨2336606270033965356539197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115475026711953808718929 2336606270033965356539197)
                  ·
                    refine ⟨876227351262737008702199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336606270033965356539197 876227351262737008702199)
                    ·
                      rfl

theorem cell22_2559670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2559670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559670 prefixEnd_2559670 := by exact prefixLift 2559670
  have htrace : WordTrace (prefixWord ++ tailWord_2559670) baseStart_2559670 baseEnd_2559670 := by
    simpa [prefixWord, tailWord_2559670, baseEnd_2559670] using wordTrace_append hprefix tailTrace_2559670
  have hstable : (prefixWord ++ tailWord_2559670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559670).length < 2 ^ (prefixWord ++ tailWord_2559670).sum := by decide
  have hdescent : baseEnd_2559670 < baseStart_2559670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559677 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2559677 : Nat := 118140960795 + 2559677 * 2 ^ 59
def prefixEnd_2559677 : Nat := 4983230072969 + 3 ^ 40 * 2559677 * 2
def baseEnd_2559677 : Nat := 292076582501930441259059

theorem tailTrace_2559677 : CollatzResearch.WordTrace tailWord_2559677 prefixEnd_2559677 292076582501930441259059 := by
  unfold tailWord_2559677
  simp only [CollatzResearch.WordTrace]
  refine ⟨93359089947734861872781285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62239393298489907915187523 93359089947734861872781285)
  ·
    refine ⟨17504829365200286601146491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93359089947734861872781285 17504829365200286601146491)
    ·
      refine ⟨26257244047800429901719737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17504829365200286601146491 26257244047800429901719737)
      ·
        refine ⟨19692933035850322426289803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26257244047800429901719737 19692933035850322426289803)
        ·
          refine ⟨29539399553775483639434705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19692933035850322426289803 29539399553775483639434705)
          ·
            refine ⟨22154549665331612729576029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29539399553775483639434705 22154549665331612729576029)
            ·
              refine ⟨8307956124499354773591011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22154549665331612729576029 8307956124499354773591011)
              ·
                refine ⟨12461934186749032160386517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307956124499354773591011 12461934186749032160386517)
                ·
                  refine ⟨292076582501930441259059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12461934186749032160386517 292076582501930441259059)
                  ·
                    rfl

theorem cell22_2559677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2559677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559677 prefixEnd_2559677 := by exact prefixLift 2559677
  have htrace : WordTrace (prefixWord ++ tailWord_2559677) baseStart_2559677 baseEnd_2559677 := by
    simpa [prefixWord, tailWord_2559677, baseEnd_2559677] using wordTrace_append hprefix tailTrace_2559677
  have hstable : (prefixWord ++ tailWord_2559677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559677).length < 2 ^ (prefixWord ++ tailWord_2559677).sum := by decide
  have hdescent : baseEnd_2559677 < baseStart_2559677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559715 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 1, 3]
def baseStart_2559715 : Nat := 118140960795 + 2559715 * 2 ^ 59
def prefixEnd_2559715 : Nat := 4983230072969 + 3 ^ 40 * 2559715 * 2
def baseEnd_2559715 : Nat := 876242755682371891327061

theorem tailTrace_2559715 : CollatzResearch.WordTrace tailWord_2559715 prefixEnd_2559715 876242755682371891327061 := by
  unfold tailWord_2559715
  simp only [CollatzResearch.WordTrace]
  refine ⟨93360475921597194362664599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62240317281064796241776399 93360475921597194362664599)
  ·
    refine ⟨140040713882395791543996899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93360475921597194362664599 140040713882395791543996899)
    ·
      refine ⟨210061070823593687315995349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140040713882395791543996899 210061070823593687315995349)
      ·
        refine ⟨4923306347427977046468641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 210061070823593687315995349 4923306347427977046468641)
        ·
          refine ⟨3692479760570982784851481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923306347427977046468641 3692479760570982784851481)
          ·
            refine ⟨2769359820428237088638611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692479760570982784851481 2769359820428237088638611)
            ·
              refine ⟨4154039730642355632957917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769359820428237088638611 4154039730642355632957917)
              ·
                refine ⟨1557764898990883362359219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4154039730642355632957917 1557764898990883362359219)
                ·
                  refine ⟨2336647348486325043538829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557764898990883362359219 2336647348486325043538829)
                  ·
                    refine ⟨876242755682371891327061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336647348486325043538829 876242755682371891327061)
                    ·
                      rfl

theorem cell22_2559715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 3].length) (baseStart_2559715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559715 prefixEnd_2559715 := by exact prefixLift 2559715
  have htrace : WordTrace (prefixWord ++ tailWord_2559715) baseStart_2559715 baseEnd_2559715 := by
    simpa [prefixWord, tailWord_2559715, baseEnd_2559715] using wordTrace_append hprefix tailTrace_2559715
  have hstable : (prefixWord ++ tailWord_2559715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559715).length < 2 ^ (prefixWord ++ tailWord_2559715).sum := by decide
  have hdescent : baseEnd_2559715 < baseStart_2559715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559722 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_2559722 : Nat := 118140960795 + 2559722 * 2 ^ 59
def prefixEnd_2559722 : Nat := 4983230072969 + 3 ^ 40 * 2559722 * 2
def baseEnd_2559722 : Nat := 292081717308475402134013

theorem tailTrace_2559722 : CollatzResearch.WordTrace tailWord_2559722 prefixEnd_2559722 292081717308475402134013 := by
  unfold tailWord_2559722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23340182808142958639542355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62240487488381223038779613 23340182808142958639542355)
  ·
    refine ⟨35010274212214437959313533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23340182808142958639542355 35010274212214437959313533)
    ·
      refine ⟨13128852829580414234742575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35010274212214437959313533 13128852829580414234742575)
      ·
        refine ⟨19693279244370621352113863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13128852829580414234742575 19693279244370621352113863)
        ·
          refine ⟨29539918866555932028170795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19693279244370621352113863 29539918866555932028170795)
          ·
            refine ⟨44309878299833898042256193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29539918866555932028170795 44309878299833898042256193)
            ·
              refine ⟨33232408724875423531692145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44309878299833898042256193 33232408724875423531692145)
              ·
                refine ⟨24924306543656567648769109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33232408724875423531692145 24924306543656567648769109)
                ·
                  refine ⟨292081717308475402134013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24924306543656567648769109 292081717308475402134013)
                  ·
                    rfl

theorem cell22_2559722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_2559722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559722 prefixEnd_2559722 := by exact prefixLift 2559722
  have htrace : WordTrace (prefixWord ++ tailWord_2559722) baseStart_2559722 baseEnd_2559722 := by
    simpa [prefixWord, tailWord_2559722, baseEnd_2559722] using wordTrace_append hprefix tailTrace_2559722
  have hstable : (prefixWord ++ tailWord_2559722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559722).length < 2 ^ (prefixWord ++ tailWord_2559722).sum := by decide
  have hdescent : baseEnd_2559722 < baseStart_2559722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559724 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_2559724 : Nat := 118140960795 + 2559724 * 2 ^ 59
def prefixEnd_2559724 : Nat := 4983230072969 + 3 ^ 40 * 2559724 * 2
def baseEnd_2559724 : Nat := 876245836566298867852033

theorem tailTrace_2559724 : CollatzResearch.WordTrace tailWord_2559724 prefixEnd_2559724 876245836566298867852033 := by
  unfold tailWord_2559724
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680402089282294449871113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62240536119043059266494817 46680402089282294449871113)
  ·
    refine ⟨35010301566961720837403335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46680402089282294449871113 35010301566961720837403335)
    ·
      refine ⟨52515452350442581256105003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35010301566961720837403335 52515452350442581256105003)
      ·
        refine ⟨78773178525663871884157505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52515452350442581256105003 78773178525663871884157505)
        ·
          refine ⟨59079883894247903913118129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78773178525663871884157505 59079883894247903913118129)
          ·
            refine ⟨44309912920685927934838597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59079883894247903913118129 44309912920685927934838597)
            ·
              refine ⟨8308108672628611487782237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44309912920685927934838597 8308108672628611487782237)
              ·
                refine ⟨3115540752235729307918339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8308108672628611487782237 3115540752235729307918339)
                ·
                  refine ⟨4673311128353593961877509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115540752235729307918339 4673311128353593961877509)
                  ·
                    refine ⟨876245836566298867852033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673311128353593961877509 876245836566298867852033)
                    ·
                      rfl

theorem cell22_2559724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_2559724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559724 prefixEnd_2559724 := by exact prefixLift 2559724
  have htrace : WordTrace (prefixWord ++ tailWord_2559724) baseStart_2559724 baseEnd_2559724 := by
    simpa [prefixWord, tailWord_2559724, baseEnd_2559724] using wordTrace_append hprefix tailTrace_2559724
  have hstable : (prefixWord ++ tailWord_2559724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559724).length < 2 ^ (prefixWord ++ tailWord_2559724).sum := by decide
  have hdescent : baseEnd_2559724 < baseStart_2559724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559816 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_2559816 : Nat := 118140960795 + 2559816 * 2 ^ 59
def prefixEnd_2559816 : Nat := 4983230072969 + 3 ^ 40 * 2559816 * 2
def baseEnd_2559816 : Nat := 876277330046441294551751

theorem tailTrace_2559816 : CollatzResearch.WordTrace tailWord_2559816 prefixEnd_2559816 876277330046441294551751 := by
  unfold tailWord_2559816
  simp only [CollatzResearch.WordTrace]
  refine ⟨46682079847115644306045651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62242773129487525741394201 46682079847115644306045651)
  ·
    refine ⟨70023119770673466459068477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46682079847115644306045651 70023119770673466459068477)
    ·
      refine ⟨26258669914002549922150679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70023119770673466459068477 26258669914002549922150679)
      ·
        refine ⟨39388004871003824883226019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26258669914002549922150679 39388004871003824883226019)
        ·
          refine ⟨59082007306505737324839029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39388004871003824883226019 59082007306505737324839029)
          ·
            refine ⟨5538938184984912874203659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59082007306505737324839029 5538938184984912874203659)
            ·
              refine ⟨8308407277477369311305489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538938184984912874203659 8308407277477369311305489)
              ·
                refine ⟨6231305458108026983479117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8308407277477369311305489 6231305458108026983479117)
                ·
                  refine ⟨2336739546790510118804669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6231305458108026983479117 2336739546790510118804669)
                  ·
                    refine ⟨876277330046441294551751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336739546790510118804669 876277330046441294551751)
                    ·
                      rfl

theorem cell22_2559816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_2559816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559816 prefixEnd_2559816 := by exact prefixLift 2559816
  have htrace : WordTrace (prefixWord ++ tailWord_2559816) baseStart_2559816 baseEnd_2559816 := by
    simpa [prefixWord, tailWord_2559816, baseEnd_2559816] using wordTrace_append hprefix tailTrace_2559816
  have hstable : (prefixWord ++ tailWord_2559816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559816).length < 2 ^ (prefixWord ++ tailWord_2559816).sum := by decide
  have hdescent : baseEnd_2559816 < baseStart_2559816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559833 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 1, 3]
def baseStart_2559833 : Nat := 118140960795 + 2559833 * 2 ^ 59
def prefixEnd_2559833 : Nat := 4983230072969 + 3 ^ 40 * 2559833 * 2
def baseEnd_2559833 : Nat := 876283149493858916876699

theorem tailTrace_2559833 : CollatzResearch.WordTrace tailWord_2559833 prefixEnd_2559833 876283149493858916876699 := by
  unfold tailWord_2559833
  simp only [CollatzResearch.WordTrace]
  refine ⟨93364779735169700515460153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62243186490113133676973435 93364779735169700515460153)
  ·
    refine ⟨70023584801377275386595115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93364779735169700515460153 70023584801377275386595115)
    ·
      refine ⟨105035377202065913079892673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70023584801377275386595115 105035377202065913079892673)
      ·
        refine ⟨78776532901549434809919505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105035377202065913079892673 78776532901549434809919505)
        ·
          refine ⟨59082399676162076107439629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78776532901549434809919505 59082399676162076107439629)
          ·
            refine ⟨22155899878560778540289861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59082399676162076107439629 22155899878560778540289861)
            ·
              refine ⟨4154231227230145976304349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22155899878560778540289861 4154231227230145976304349)
              ·
                refine ⟨1557836710211304741114131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4154231227230145976304349 1557836710211304741114131)
                ·
                  refine ⟨2336755065316957111671197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557836710211304741114131 2336755065316957111671197)
                  ·
                    refine ⟨876283149493858916876699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336755065316957111671197 876283149493858916876699)
                    ·
                      rfl

theorem cell22_2559833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_2559833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559833 prefixEnd_2559833 := by exact prefixLift 2559833
  have htrace : WordTrace (prefixWord ++ tailWord_2559833) baseStart_2559833 baseEnd_2559833 := by
    simpa [prefixWord, tailWord_2559833, baseEnd_2559833] using wordTrace_append hprefix tailTrace_2559833
  have hstable : (prefixWord ++ tailWord_2559833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559833).length < 2 ^ (prefixWord ++ tailWord_2559833).sum := by decide
  have hdescent : baseEnd_2559833 < baseStart_2559833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559850 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2559850 : Nat := 118140960795 + 2559850 * 2 ^ 59
def prefixEnd_2559850 : Nat := 4983230072969 + 3 ^ 40 * 2559850 * 2
def baseEnd_2559850 : Nat := 876288968941276539201647

theorem tailTrace_2559850 : CollatzResearch.WordTrace tailWord_2559850 prefixEnd_2559850 876288968941276539201647 := by
  unfold tailWord_2559850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23341349944027028104707251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62243599850738741612552669 23341349944027028104707251)
  ·
    refine ⟨35012024916040542157060877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23341349944027028104707251 35012024916040542157060877)
    ·
      refine ⟨13129509343515203308897829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35012024916040542157060877 13129509343515203308897829)
      ·
        refine ⟨2461783001909100620418343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13129509343515203308897829 2461783001909100620418343)
        ·
          refine ⟨3692674502863650930627515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461783001909100620418343 3692674502863650930627515)
          ·
            refine ⟨5539011754295476395941273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692674502863650930627515 5539011754295476395941273)
            ·
              refine ⟨4154258815721607296955955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539011754295476395941273 4154258815721607296955955)
              ·
                refine ⟨6231388223582410945433933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154258815721607296955955 6231388223582410945433933)
                ·
                  refine ⟨2336770583843404104537725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6231388223582410945433933 2336770583843404104537725)
                  ·
                    refine ⟨876288968941276539201647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336770583843404104537725 876288968941276539201647)
                    ·
                      rfl

theorem cell22_2559850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2559850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559850 prefixEnd_2559850 := by exact prefixLift 2559850
  have htrace : WordTrace (prefixWord ++ tailWord_2559850) baseStart_2559850 baseEnd_2559850 := by
    simpa [prefixWord, tailWord_2559850, baseEnd_2559850] using wordTrace_append hprefix tailTrace_2559850
  have hstable : (prefixWord ++ tailWord_2559850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559850).length < 2 ^ (prefixWord ++ tailWord_2559850).sum := by decide
  have hdescent : baseEnd_2559850 < baseStart_2559850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559876 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2559876 : Nat := 118140960795 + 2559876 * 2 ^ 59
def prefixEnd_2559876 : Nat := 4983230072969 + 3 ^ 40 * 2559876 * 2
def baseEnd_2559876 : Nat := 876297869272621138051567

theorem tailTrace_2559876 : CollatzResearch.WordTrace tailWord_2559876 prefixEnd_2559876 876297869272621138051567 := by
  unfold tailWord_2559876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46683174037006959429637741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62244232049342612572850321 46683174037006959429637741)
  ·
    refine ⟨17506190263877609786114153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46683174037006959429637741 17506190263877609786114153)
    ·
      refine ⟨13129642697908207339585615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17506190263877609786114153 13129642697908207339585615)
      ·
        refine ⟨19694464046862311009378423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13129642697908207339585615 19694464046862311009378423)
        ·
          refine ⟨29541696070293466514067635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19694464046862311009378423 29541696070293466514067635)
          ·
            refine ⟨44312544105440199771101453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29541696070293466514067635 44312544105440199771101453)
            ·
              refine ⟨16617204039540074914163045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44312544105440199771101453 16617204039540074914163045)
              ·
                refine ⟨3115725757413764046405571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16617204039540074914163045 3115725757413764046405571)
                ·
                  refine ⟨4673588636120646069608357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115725757413764046405571 4673588636120646069608357)
                  ·
                    refine ⟨876297869272621138051567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673588636120646069608357 876297869272621138051567)
                    ·
                      rfl

theorem cell22_2559876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2559876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559876 prefixEnd_2559876 := by exact prefixLift 2559876
  have htrace : WordTrace (prefixWord ++ tailWord_2559876) baseStart_2559876 baseEnd_2559876 := by
    simpa [prefixWord, tailWord_2559876, baseEnd_2559876] using wordTrace_append hprefix tailTrace_2559876
  have hstable : (prefixWord ++ tailWord_2559876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559876).length < 2 ^ (prefixWord ++ tailWord_2559876).sum := by decide
  have hdescent : baseEnd_2559876 < baseStart_2559876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559889 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2559889 : Nat := 118140960795 + 2559889 * 2 ^ 59
def prefixEnd_2559889 : Nat := 4983230072969 + 3 ^ 40 * 2559889 * 2
def baseEnd_2559889 : Nat := 876302319438293437476527

theorem tailTrace_2559889 : CollatzResearch.WordTrace tailWord_2559889 prefixEnd_2559889 876302319438293437476527 := by
  unfold tailWord_2559889
  simp only [CollatzResearch.WordTrace]
  refine ⟨93366822222966822079498721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62244548148644548052999147 93366822222966822079498721)
  ·
    refine ⟨70025116667225116559624041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93366822222966822079498721 70025116667225116559624041)
    ·
      refine ⟨52518837500418837419718031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70025116667225116559624041 52518837500418837419718031)
      ·
        refine ⟨78778256250628256129577047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52518837500418837419718031 78778256250628256129577047)
        ·
          refine ⟨118167384375942384194365571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78778256250628256129577047 118167384375942384194365571)
          ·
            refine ⟨177251076563913576291548357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118167384375942384194365571 177251076563913576291548357)
            ·
              refine ⟨33234576855733795554665317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177251076563913576291548357 33234576855733795554665317)
              ·
                refine ⟨6231483160450086666499747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33234576855733795554665317 6231483160450086666499747)
                ·
                  refine ⟨9347224740675129999749621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231483160450086666499747 9347224740675129999749621)
                  ·
                    refine ⟨876302319438293437476527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9347224740675129999749621 876302319438293437476527)
                    ·
                      rfl

theorem cell22_2559889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2559889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559889 prefixEnd_2559889 := by exact prefixLift 2559889
  have htrace : WordTrace (prefixWord ++ tailWord_2559889) baseStart_2559889 baseEnd_2559889 := by
    simpa [prefixWord, tailWord_2559889, baseEnd_2559889] using wordTrace_append hprefix tailTrace_2559889
  have hstable : (prefixWord ++ tailWord_2559889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559889).length < 2 ^ (prefixWord ++ tailWord_2559889).sum := by decide
  have hdescent : baseEnd_2559889 < baseStart_2559889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559919 : List Nat := [1, 1, 2, 1, 2, 2, 6, 7]
def baseStart_2559919 : Nat := 118140960795 + 2559919 * 2 ^ 59
def prefixEnd_2559919 : Nat := 4983230072969 + 3 ^ 40 * 2559919 * 2
def baseEnd_2559919 : Nat := 97368065450153706580715

theorem tailTrace_2559919 : CollatzResearch.WordTrace tailWord_2559919 prefixEnd_2559919 97368065450153706580715 := by
  unfold tailWord_2559919
  simp only [CollatzResearch.WordTrace]
  refine ⟨93367916412858137203090811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62245277608572091468727207 93367916412858137203090811)
  ·
    refine ⟨140051874619287205804636217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93367916412858137203090811 140051874619287205804636217)
    ·
      refine ⟨105038905964465404353477163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140051874619287205804636217 105038905964465404353477163)
      ·
        refine ⟨157558358946698106530215745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105038905964465404353477163 157558358946698106530215745)
        ·
          refine ⟨118168769210023579897661809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157558358946698106530215745 118168769210023579897661809)
          ·
            refine ⟨88626576907517684923246357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118168769210023579897661809 88626576907517684923246357)
            ·
              refine ⟨4154370792539891480777173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88626576907517684923246357 4154370792539891480777173)
              ·
                refine ⟨97368065450153706580715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4154370792539891480777173 97368065450153706580715)
                ·
                  rfl

theorem cell22_2559919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 7].length) (baseStart_2559919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559919 prefixEnd_2559919 := by exact prefixLift 2559919
  have htrace : WordTrace (prefixWord ++ tailWord_2559919) baseStart_2559919 baseEnd_2559919 := by
    simpa [prefixWord, tailWord_2559919, baseEnd_2559919] using wordTrace_append hprefix tailTrace_2559919
  have hstable : (prefixWord ++ tailWord_2559919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559919).length < 2 ^ (prefixWord ++ tailWord_2559919).sum := by decide
  have hdescent : baseEnd_2559919 < baseStart_2559919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559970 : List Nat := [3, 3, 3, 1, 2, 2, 1, 7]
def baseStart_2559970 : Nat := 118140960795 + 2559970 * 2 ^ 59
def prefixEnd_2559970 : Nat := 4983230072969 + 3 ^ 40 * 2559970 * 2
def baseEnd_2559970 : Nat := 97370005265959580689031

theorem tailTrace_2559970 : CollatzResearch.WordTrace tailWord_2559970 prefixEnd_2559970 97370005265959580689031 := by
  unfold tailWord_2559970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23342444133918343228299341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62246517690448915275464909 23342444133918343228299341)
  ·
    refine ⟨8753416550219378710612253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23342444133918343228299341 8753416550219378710612253)
    ·
      refine ⟨3282531206332267016479595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8753416550219378710612253 3282531206332267016479595)
      ·
        refine ⟨4923796809498400524719393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282531206332267016479595 4923796809498400524719393)
        ·
          refine ⟨3692847607123800393539545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923796809498400524719393 3692847607123800393539545)
          ·
            refine ⟨2769635705342850295154659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692847607123800393539545 2769635705342850295154659)
            ·
              refine ⟨4154453558014275442731989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769635705342850295154659 4154453558014275442731989)
              ·
                refine ⟨97370005265959580689031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4154453558014275442731989 97370005265959580689031)
                ·
                  rfl

theorem cell22_2559970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_2559970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2559970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2559970 prefixEnd_2559970 := by exact prefixLift 2559970
  have htrace : WordTrace (prefixWord ++ tailWord_2559970) baseStart_2559970 baseEnd_2559970 := by
    simpa [prefixWord, tailWord_2559970, baseEnd_2559970] using wordTrace_append hprefix tailTrace_2559970
  have hstable : (prefixWord ++ tailWord_2559970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559970).length < 2 ^ (prefixWord ++ tailWord_2559970).sum := by decide
  have hdescent : baseEnd_2559970 < baseStart_2559970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560026 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_2560026 : Nat := 118140960795 + 2560026 * 2 ^ 59
def prefixEnd_2560026 : Nat := 4983230072969 + 3 ^ 40 * 2560026 * 2
def baseEnd_2560026 : Nat := 292116405779356915600369

theorem tailTrace_2560026 : CollatzResearch.WordTrace tailWord_2560026 prefixEnd_2560026 292116405779356915600369 := by
  unfold tailWord_2560026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23342954755867623619308983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62247879348980329651490621 23342954755867623619308983)
  ·
    refine ⟨35014432133801435428963475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23342954755867623619308983 35014432133801435428963475)
    ·
      refine ⟨52521648200702153143445213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35014432133801435428963475 52521648200702153143445213)
      ·
        refine ⟨19695618075263307428791955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52521648200702153143445213 19695618075263307428791955)
        ·
          refine ⟨29543427112894961143187933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19695618075263307428791955 29543427112894961143187933)
          ·
            refine ⟨11078785167335610428695475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29543427112894961143187933 11078785167335610428695475)
            ·
              refine ⟨16618177751003415643043213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11078785167335610428695475 16618177751003415643043213)
              ·
                refine ⟨6231816656626280866141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16618177751003415643043213 6231816656626280866141205)
                ·
                  refine ⟨292116405779356915600369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6231816656626280866141205 292116405779356915600369)
                  ·
                    rfl

theorem cell22_2560026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_2560026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560026 prefixEnd_2560026 := by exact prefixLift 2560026
  have htrace : WordTrace (prefixWord ++ tailWord_2560026) baseStart_2560026 baseEnd_2560026 := by
    simpa [prefixWord, tailWord_2560026, baseEnd_2560026] using wordTrace_append hprefix tailTrace_2560026
  have hstable : (prefixWord ++ tailWord_2560026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560026).length < 2 ^ (prefixWord ++ tailWord_2560026).sum := by decide
  have hdescent : baseEnd_2560026 < baseStart_2560026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560077 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2560077 : Nat := 118140960795 + 2560077 * 2 ^ 59
def prefixEnd_2560077 : Nat := 4983230072969 + 3 ^ 40 * 2560077 * 2
def baseEnd_2560077 : Nat := 292122225226774537925317

theorem tailTrace_2560077 : CollatzResearch.WordTrace tailWord_2560077 prefixEnd_2560077 292122225226774537925317 := by
  unfold tailWord_2560077
  simp only [CollatzResearch.WordTrace]
  refine ⟨93373679146285730187342485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62249119430857153458228323 93373679146285730187342485)
  ·
    refine ⟨4376891209982143602531679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93373679146285730187342485 4376891209982143602531679)
    ·
      refine ⟨6565336814973215403797519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376891209982143602531679 6565336814973215403797519)
      ·
        refine ⟨9848005222459823105696279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565336814973215403797519 9848005222459823105696279)
        ·
          refine ⟨14772007833689734658544419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9848005222459823105696279 14772007833689734658544419)
          ·
            refine ⟨22158011750534601987816629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14772007833689734658544419 22158011750534601987816629)
            ·
              refine ⟨2077313601612618936357809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22158011750534601987816629 2077313601612618936357809)
              ·
                refine ⟨1557985201209464202268357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077313601612618936357809 1557985201209464202268357)
                ·
                  refine ⟨292122225226774537925317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557985201209464202268357 292122225226774537925317)
                  ·
                    rfl

theorem cell22_2560077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2560077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2560077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2560077 prefixEnd_2560077 := by exact prefixLift 2560077
  have htrace : WordTrace (prefixWord ++ tailWord_2560077) baseStart_2560077 baseEnd_2560077 := by
    simpa [prefixWord, tailWord_2560077, baseEnd_2560077] using wordTrace_append hprefix tailTrace_2560077
  have hstable : (prefixWord ++ tailWord_2560077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560077).length < 2 ^ (prefixWord ++ tailWord_2560077).sum := by decide
  have hdescent : baseEnd_2560077 < baseStart_2560077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
