import V185TrunkScan23Chunk0985

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5836947 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 3, 6]
def baseStart_5836947 : Nat := 118140960795 + 5836947 * 2 ^ 59
def prefixEnd_5836947 : Nat := 4983230072969 + 3 ^ 40 * 5836947 * 2
def baseEnd_5836947 : Nat := 999053121939693217239625

theorem tailTrace_5836947 : CollatzResearch.WordTrace tailWord_5836947 prefixEnd_5836947 999053121939693217239625 := by
  unfold tailWord_5836947
  simp only [CollatzResearch.WordTrace]
  refine ⟨212890946784745365027741095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141927297856496910018494063 212890946784745365027741095)
  ·
    refine ⟨319336420177118047541611643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212890946784745365027741095 319336420177118047541611643)
    ·
      refine ⟨479004630265677071312417465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319336420177118047541611643 479004630265677071312417465)
      ·
        refine ⟨359253472699257803484313099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479004630265677071312417465 359253472699257803484313099)
        ·
          refine ⟨538880209048886705226469649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359253472699257803484313099 538880209048886705226469649)
          ·
            refine ⟨404160156786665028919852237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538880209048886705226469649 404160156786665028919852237)
            ·
              refine ⟨151560058794999385844944589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404160156786665028919852237 151560058794999385844944589)
              ·
                refine ⟨56835022048124769691854221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151560058794999385844944589 56835022048124769691854221)
                ·
                  refine ⟨21313133268046788634445333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56835022048124769691854221 21313133268046788634445333)
                  ·
                    refine ⟨999053121939693217239625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21313133268046788634445333 999053121939693217239625)
                    ·
                      rfl

theorem cell23_5836947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_5836947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836947 prefixEnd_5836947 := by exact prefixLift 5836947
  have htrace : WordTrace (prefixWord ++ tailWord_5836947) baseStart_5836947 baseEnd_5836947 := by
    simpa [prefixWord, tailWord_5836947, baseEnd_5836947] using wordTrace_append hprefix tailTrace_5836947
  have hstable : (prefixWord ++ tailWord_5836947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836947).length < 2 ^ (prefixWord ++ tailWord_5836947).sum := by decide
  have hdescent : baseEnd_5836947 < baseStart_5836947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836965 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 1, 1, 3]
def baseStart_5836965 : Nat := 118140960795 + 5836965 * 2 ^ 59
def prefixEnd_5836965 : Nat := 4983230072969 + 3 ^ 40 * 5836965 * 2
def baseEnd_5836965 : Nat := 2997168608470860581293793

theorem tailTrace_5836965 : CollatzResearch.WordTrace tailWord_5836965 prefixEnd_5836965 2997168608470860581293793 := by
  unfold tailWord_5836965
  simp only [CollatzResearch.WordTrace]
  refine ⟨212891603298680154101896349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141927735532453436067930899 212891603298680154101896349)
  ·
    refine ⟨79834351237005057788211131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212891603298680154101896349 79834351237005057788211131)
    ·
      refine ⟨119751526855507586682316697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79834351237005057788211131 119751526855507586682316697)
      ·
        refine ⟨89813645141630690011737523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119751526855507586682316697 89813645141630690011737523)
        ·
          refine ⟨134720467712446035017606285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89813645141630690011737523 134720467712446035017606285)
          ·
            refine ⟨50520175392167263131602357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134720467712446035017606285 50520175392167263131602357)
            ·
              refine ⟨4736266443015680918587721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50520175392167263131602357 4736266443015680918587721)
              ·
                refine ⟨3552199832261760688940791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4736266443015680918587721 3552199832261760688940791)
                ·
                  refine ⟨5328299748392641033411187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552199832261760688940791 5328299748392641033411187)
                  ·
                    refine ⟨7992449622588961550116781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328299748392641033411187 7992449622588961550116781)
                    ·
                      refine ⟨2997168608470860581293793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992449622588961550116781 2997168608470860581293793)
                      ·
                        rfl

theorem cell23_5836965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_5836965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836965 prefixEnd_5836965 := by exact prefixLift 5836965
  have htrace : WordTrace (prefixWord ++ tailWord_5836965) baseStart_5836965 baseEnd_5836965 := by
    simpa [prefixWord, tailWord_5836965, baseEnd_5836965] using wordTrace_append hprefix tailTrace_5836965
  have hstable : (prefixWord ++ tailWord_5836965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836965).length < 2 ^ (prefixWord ++ tailWord_5836965).sum := by decide
  have hdescent : baseEnd_5836965 < baseStart_5836965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5836984 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_5836984 : Nat := 118140960795 + 5836984 * 2 ^ 59
def prefixEnd_5836984 : Nat := 4983230072969 + 3 ^ 40 * 5836984 * 2
def baseEnd_5836984 : Nat := 2997178364603296006956205

theorem tailTrace_5836984 : CollatzResearch.WordTrace tailWord_5836984 prefixEnd_5836984 2997178364603296006956205 := by
  unfold tailWord_5836984
  simp only [CollatzResearch.WordTrace]
  refine ⟨106446148142805660173419003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141928197523740880231225337 106446148142805660173419003)
  ·
    refine ⟨159669222214208490260128505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106446148142805660173419003 159669222214208490260128505)
    ·
      refine ⟨119751916660656367695096379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159669222214208490260128505 119751916660656367695096379)
      ·
        refine ⟨179627874990984551542644569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119751916660656367695096379 179627874990984551542644569)
        ·
          refine ⟨134720906243238413656983427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179627874990984551542644569 134720906243238413656983427)
          ·
            refine ⟨202081359364857620485475141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134720906243238413656983427 202081359364857620485475141)
            ·
              refine ⟨37890254880910803841026589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202081359364857620485475141 37890254880910803841026589)
              ·
                refine ⟨14208845580341551440384971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37890254880910803841026589 14208845580341551440384971)
                ·
                  refine ⟨21313268370512327160577457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14208845580341551440384971 21313268370512327160577457)
                  ·
                    refine ⟨15984951277884245370433093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21313268370512327160577457 15984951277884245370433093)
                    ·
                      refine ⟨2997178364603296006956205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15984951277884245370433093 2997178364603296006956205)
                      ·
                        rfl

theorem cell23_5836984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_5836984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5836984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5836984 prefixEnd_5836984 := by exact prefixLift 5836984
  have htrace : WordTrace (prefixWord ++ tailWord_5836984) baseStart_5836984 baseEnd_5836984 := by
    simpa [prefixWord, tailWord_5836984, baseEnd_5836984] using wordTrace_append hprefix tailTrace_5836984
  have hstable : (prefixWord ++ tailWord_5836984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5836984).length < 2 ^ (prefixWord ++ tailWord_5836984).sum := by decide
  have hdescent : baseEnd_5836984 < baseStart_5836984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5836984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837061 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_5837061 : Nat := 118140960795 + 5837061 * 2 ^ 59
def prefixEnd_5837061 : Nat := 4983230072969 + 3 ^ 40 * 5837061 * 2
def baseEnd_5837061 : Nat := 2997217902613692205693351

theorem tailTrace_5837061 : CollatzResearch.WordTrace tailWord_5837061 prefixEnd_5837061 2997217902613692205693351 := by
  unfold tailWord_5837061
  simp only [CollatzResearch.WordTrace]
  refine ⟨212895104706332362497391037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141930069804221574998260691 212895104706332362497391037)
  ·
    refine ⟨79835664264874635936521639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212895104706332362497391037 79835664264874635936521639)
    ·
      refine ⟨119753496397311953904782459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79835664264874635936521639 119753496397311953904782459)
      ·
        refine ⟨179630244595967930857173689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119753496397311953904782459 179630244595967930857173689)
        ·
          refine ⟨134722683446975948142880267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179630244595967930857173689 134722683446975948142880267)
          ·
            refine ⟨202084025170463922214320401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134722683446975948142880267 202084025170463922214320401)
            ·
              refine ⟨151563018877847941660740301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202084025170463922214320401 151563018877847941660740301)
              ·
                refine ⟨56836132079192978122777613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151563018877847941660740301 56836132079192978122777613)
                ·
                  refine ⟨21313549529697366796041605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56836132079192978122777613 21313549529697366796041605)
                  ·
                    refine ⟨3996290536818256274257801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21313549529697366796041605 3996290536818256274257801)
                    ·
                      refine ⟨2997217902613692205693351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996290536818256274257801 2997217902613692205693351)
                      ·
                        rfl

theorem cell23_5837061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_5837061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837061 prefixEnd_5837061 := by exact prefixLift 5837061
  have htrace : WordTrace (prefixWord ++ tailWord_5837061) baseStart_5837061 baseEnd_5837061 := by
    simpa [prefixWord, tailWord_5837061, baseEnd_5837061] using wordTrace_append hprefix tailTrace_5837061
  have hstable : (prefixWord ++ tailWord_5837061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837061).length < 2 ^ (prefixWord ++ tailWord_5837061).sum := by decide
  have hdescent : baseEnd_5837061 < baseStart_5837061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837065 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 1, 3, 2]
def baseStart_5837065 : Nat := 118140960795 + 5837065 * 2 ^ 59
def prefixEnd_5837065 : Nat := 4983230072969 + 3 ^ 40 * 5837065 * 2
def baseEnd_5837065 : Nat := 2997219956536310190043333

theorem tailTrace_5837065 : CollatzResearch.WordTrace tailWord_5837065 prefixEnd_5837065 2997219956536310190043333 := by
  unfold tailWord_5837065
  simp only [CollatzResearch.WordTrace]
  refine ⟨212895250598317871180536649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141930167065545247453691099 212895250598317871180536649)
  ·
    refine ⟨159671437948738403385402487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212895250598317871180536649 159671437948738403385402487)
    ·
      refine ⟨239507156923107605078103731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159671437948738403385402487 239507156923107605078103731)
      ·
        refine ⟨359260735384661407617155597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239507156923107605078103731 359260735384661407617155597)
        ·
          refine ⟨134722775769248027856433349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359260735384661407617155597 134722775769248027856433349)
          ·
            refine ⟨25260520456734005223081253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134722775769248027856433349 25260520456734005223081253)
            ·
              refine ⟨4736347585637625979327735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25260520456734005223081253 4736347585637625979327735)
              ·
                refine ⟨7104521378456438968991603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736347585637625979327735 7104521378456438968991603)
                ·
                  refine ⟨10656782067684658453487405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104521378456438968991603 10656782067684658453487405)
                  ·
                    refine ⟨3996293275381746920057777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10656782067684658453487405 3996293275381746920057777)
                    ·
                      refine ⟨2997219956536310190043333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996293275381746920057777 2997219956536310190043333)
                      ·
                        rfl

theorem cell23_5837065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 3, 2].length) (baseStart_5837065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837065 prefixEnd_5837065 := by exact prefixLift 5837065
  have htrace : WordTrace (prefixWord ++ tailWord_5837065) baseStart_5837065 baseEnd_5837065 := by
    simpa [prefixWord, tailWord_5837065, baseEnd_5837065] using wordTrace_append hprefix tailTrace_5837065
  have hstable : (prefixWord ++ tailWord_5837065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837065).length < 2 ^ (prefixWord ++ tailWord_5837065).sum := by decide
  have hdescent : baseEnd_5837065 < baseStart_5837065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837144 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_5837144 : Nat := 118140960795 + 5837144 * 2 ^ 59
def prefixEnd_5837144 : Nat := 4983230072969 + 3 ^ 40 * 5837144 * 2
def baseEnd_5837144 : Nat := 999086840502671793651823

theorem tailTrace_5837144 : CollatzResearch.WordTrace tailWord_5837144 prefixEnd_5837144 999086840502671793651823 := by
  unfold tailWord_5837144
  simp only [CollatzResearch.WordTrace]
  refine ⟨106449065982515833836331243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141932087976687778448441657 106449065982515833836331243)
  ·
    refine ⟨159673598973773750754496865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106449065982515833836331243 159673598973773750754496865)
    ·
      refine ⟨119755199230330313065872649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159673598973773750754496865 119755199230330313065872649)
      ·
        refine ⟨89816399422747734799404487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119755199230330313065872649 89816399422747734799404487)
        ·
          refine ⟨134724599134121602199106731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89816399422747734799404487 134724599134121602199106731)
          ·
            refine ⟨202086898701182403298660097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134724599134121602199106731 202086898701182403298660097)
            ·
              refine ⟨151565174025886802473995073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202086898701182403298660097 151565174025886802473995073)
              ·
                refine ⟨113673880519415101855496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151565174025886802473995073 113673880519415101855496305)
                ·
                  refine ⟨85255410389561326391622229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113673880519415101855496305 85255410389561326391622229)
                  ·
                    refine ⟨999086840502671793651823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85255410389561326391622229 999086840502671793651823)
                    ·
                      rfl

theorem cell23_5837144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_5837144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837144 prefixEnd_5837144 := by exact prefixLift 5837144
  have htrace : WordTrace (prefixWord ++ tailWord_5837144) baseStart_5837144 baseEnd_5837144 := by
    simpa [prefixWord, tailWord_5837144, baseEnd_5837144] using wordTrace_append hprefix tailTrace_5837144
  have hstable : (prefixWord ++ tailWord_5837144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837144).length < 2 ^ (prefixWord ++ tailWord_5837144).sum := by decide
  have hdescent : baseEnd_5837144 < baseStart_5837144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837150 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5837150 : Nat := 118140960795 + 5837150 * 2 ^ 59
def prefixEnd_5837150 : Nat := 4983230072969 + 3 ^ 40 * 5837150 * 2
def baseEnd_5837150 : Nat := 2997263602391942357480443

theorem tailTrace_5837150 : CollatzResearch.WordTrace tailWord_5837150 prefixEnd_5837150 2997263602391942357480443 := by
  unfold tailWord_5837150
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612293850376241337172613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141932233868673287131587269 26612293850376241337172613)
  ·
    refine ⟨4989805096945545250719865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26612293850376241337172613 4989805096945545250719865)
    ·
      refine ⟨3742353822709158938039899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4989805096945545250719865 3742353822709158938039899)
      ·
        refine ⟨5613530734063738407059849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742353822709158938039899 5613530734063738407059849)
        ·
          refine ⟨4210148050547803805294887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613530734063738407059849 4210148050547803805294887)
          ·
            refine ⟨6315222075821705707942331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210148050547803805294887 6315222075821705707942331)
            ·
              refine ⟨9472833113732558561913497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315222075821705707942331 9472833113732558561913497)
              ·
                refine ⟨7104624835299418921435123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9472833113732558561913497 7104624835299418921435123)
                ·
                  refine ⟨10656937252949128382152685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104624835299418921435123 10656937252949128382152685)
                  ·
                    refine ⟨3996351469855923143307257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10656937252949128382152685 3996351469855923143307257)
                    ·
                      refine ⟨2997263602391942357480443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996351469855923143307257 2997263602391942357480443)
                      ·
                        rfl

theorem cell23_5837150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5837150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837150 prefixEnd_5837150 := by exact prefixLift 5837150
  have htrace : WordTrace (prefixWord ++ tailWord_5837150) baseStart_5837150 baseEnd_5837150 := by
    simpa [prefixWord, tailWord_5837150, baseEnd_5837150] using wordTrace_append hprefix tailTrace_5837150
  have hstable : (prefixWord ++ tailWord_5837150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837150).length < 2 ^ (prefixWord ++ tailWord_5837150).sum := by decide
  have hdescent : baseEnd_5837150 < baseStart_5837150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837161 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_5837161 : Nat := 118140960795 + 5837161 * 2 ^ 59
def prefixEnd_5837161 : Nat := 4983230072969 + 3 ^ 40 * 5837161 * 2
def baseEnd_5837161 : Nat := 999089750226380604814297

theorem tailTrace_5837161 : CollatzResearch.WordTrace tailWord_5837161 prefixEnd_5837161 999089750226380604814297 := by
  unfold tailWord_5837161
  simp only [CollatzResearch.WordTrace]
  refine ⟨212898752005970079576031337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141932501337313386384020891 212898752005970079576031337)
  ·
    refine ⟨159674064004477559682023503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212898752005970079576031337 159674064004477559682023503)
    ·
      refine ⟨239511096006716339523035255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159674064004477559682023503 239511096006716339523035255)
      ·
        refine ⟨359266644010074509284552883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239511096006716339523035255 359266644010074509284552883)
        ·
          refine ⟨538899966015111763926829325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359266644010074509284552883 538899966015111763926829325)
          ·
            refine ⟨202087487255666911472560997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538899966015111763926829325 202087487255666911472560997)
            ·
              refine ⟨37891403860437545901105187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202087487255666911472560997 37891403860437545901105187)
              ·
                refine ⟨56837105790656318851657781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37891403860437545901105187 56837105790656318851657781)
                ·
                  refine ⟨5328478667874029892342917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56837105790656318851657781 5328478667874029892342917)
                  ·
                    refine ⟨999089750226380604814297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328478667874029892342917 999089750226380604814297)
                    ·
                      rfl

theorem cell23_5837161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_5837161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837161 prefixEnd_5837161 := by exact prefixLift 5837161
  have htrace : WordTrace (prefixWord ++ tailWord_5837161) baseStart_5837161 baseEnd_5837161 := by
    simpa [prefixWord, tailWord_5837161, baseEnd_5837161] using wordTrace_append hprefix tailTrace_5837161
  have hstable : (prefixWord ++ tailWord_5837161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837161).length < 2 ^ (prefixWord ++ tailWord_5837161).sum := by decide
  have hdescent : baseEnd_5837161 < baseStart_5837161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837168 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_5837168 : Nat := 118140960795 + 5837168 * 2 ^ 59
def prefixEnd_5837168 : Nat := 4983230072969 + 3 ^ 40 * 5837168 * 2
def baseEnd_5837168 : Nat := 2997272845043723287055359

theorem tailTrace_5837168 : CollatzResearch.WordTrace tailWord_5837168 prefixEnd_5837168 2997272845043723287055359 := by
  unfold tailWord_5837168
  simp only [CollatzResearch.WordTrace]
  refine ⟨106449503658472359885768079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141932671544629813181024105 106449503658472359885768079)
  ·
    refine ⟨159674255487708539828652119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106449503658472359885768079 159674255487708539828652119)
    ·
      refine ⟨239511383231562809742978179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159674255487708539828652119 239511383231562809742978179)
      ·
        refine ⟨359267074847344214614467269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239511383231562809742978179 359267074847344214614467269)
        ·
          refine ⟨67362576533877040240212613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359267074847344214614467269 67362576533877040240212613)
          ·
            refine ⟨12630483100101945045039865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67362576533877040240212613 12630483100101945045039865)
            ·
              refine ⟨9472862325076458783779899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12630483100101945045039865 9472862325076458783779899)
              ·
                refine ⟨14209293487614688175669849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9472862325076458783779899 14209293487614688175669849)
                ·
                  refine ⟨10656970115711016131752387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14209293487614688175669849 10656970115711016131752387)
                  ·
                    refine ⟨15985455173566524197628581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10656970115711016131752387 15985455173566524197628581)
                    ·
                      refine ⟨2997272845043723287055359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15985455173566524197628581 2997272845043723287055359)
                      ·
                        rfl

theorem cell23_5837168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_5837168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837168 prefixEnd_5837168 := by exact prefixLift 5837168
  have htrace : WordTrace (prefixWord ++ tailWord_5837168) baseStart_5837168 baseEnd_5837168 := by
    simpa [prefixWord, tailWord_5837168, baseEnd_5837168] using wordTrace_append hprefix tailTrace_5837168
  have hstable : (prefixWord ++ tailWord_5837168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837168).length < 2 ^ (prefixWord ++ tailWord_5837168).sum := by decide
  have hdescent : baseEnd_5837168 < baseStart_5837168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837171 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3]
def baseStart_5837171 : Nat := 118140960795 + 5837171 * 2 ^ 59
def prefixEnd_5837171 : Nat := 4983230072969 + 3 ^ 40 * 5837171 * 2
def baseEnd_5837171 : Nat := 2997274385485686775317845

theorem tailTrace_5837171 : CollatzResearch.WordTrace tailWord_5837171 prefixEnd_5837171 2997274385485686775317845 := by
  unfold tailWord_5837171
  simp only [CollatzResearch.WordTrace]
  refine ⟨212899116735933851283895367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141932744490622567522596911 212899116735933851283895367)
  ·
    refine ⟨319348675103900776925843051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212899116735933851283895367 319348675103900776925843051)
    ·
      refine ⟨479023012655851165388764577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319348675103900776925843051 479023012655851165388764577)
      ·
        refine ⟨359267259491888374041573433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479023012655851165388764577 359267259491888374041573433)
        ·
          refine ⟨269450444618916280531180075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359267259491888374041573433 269450444618916280531180075)
          ·
            refine ⟨404175666928374420796770113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269450444618916280531180075 404175666928374420796770113)
            ·
              refine ⟨303131750196280815597577585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404175666928374420796770113 303131750196280815597577585)
              ·
                refine ⟨227348812647210611698183189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303131750196280815597577585 227348812647210611698183189)
                ·
                  refine ⟨10656975592837997423352337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227348812647210611698183189 10656975592837997423352337)
                  ·
                    refine ⟨7992731694628498067514253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10656975592837997423352337 7992731694628498067514253)
                    ·
                      refine ⟨2997274385485686775317845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992731694628498067514253 2997274385485686775317845)
                      ·
                        rfl

theorem cell23_5837171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_5837171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837171 prefixEnd_5837171 := by exact prefixLift 5837171
  have htrace : WordTrace (prefixWord ++ tailWord_5837171) baseStart_5837171 baseEnd_5837171 := by
    simpa [prefixWord, tailWord_5837171, baseEnd_5837171] using wordTrace_append hprefix tailTrace_5837171
  have hstable : (prefixWord ++ tailWord_5837171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837171).length < 2 ^ (prefixWord ++ tailWord_5837171).sum := by decide
  have hdescent : baseEnd_5837171 < baseStart_5837171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837186 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_5837186 : Nat := 118140960795 + 5837186 * 2 ^ 59
def prefixEnd_5837186 : Nat := 4983230072969 + 3 ^ 40 * 5837186 * 2
def baseEnd_5837186 : Nat := 333031343077278246292253

theorem tailTrace_5837186 : CollatzResearch.WordTrace tailWord_5837186 prefixEnd_5837186 333031343077278246292253 := by
  unfold tailWord_5837186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53224915957719877211422853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141933109220586339230460941 53224915957719877211422853)
  ·
    refine ⟨9979671742072476977141785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53224915957719877211422853 9979671742072476977141785)
    ·
      refine ⟨7484753806554357732856339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9979671742072476977141785 7484753806554357732856339)
      ·
        refine ⟨11227130709831536599284509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7484753806554357732856339 11227130709831536599284509)
        ·
          refine ⟨4210174016186826224731691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11227130709831536599284509 4210174016186826224731691)
          ·
            refine ⟨6315261024280239337097537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210174016186826224731691 6315261024280239337097537)
            ·
              refine ⟨4736445768210179502823153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315261024280239337097537 4736445768210179502823153)
              ·
                refine ⟨3552334326157634627117365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4736445768210179502823153 3552334326157634627117365)
                ·
                  refine ⟨333031343077278246292253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3552334326157634627117365 333031343077278246292253)
                  ·
                    rfl

theorem cell23_5837186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_5837186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837186 prefixEnd_5837186 := by exact prefixLift 5837186
  have htrace : WordTrace (prefixWord ++ tailWord_5837186) baseStart_5837186 baseEnd_5837186 := by
    simpa [prefixWord, tailWord_5837186, baseEnd_5837186] using wordTrace_append hprefix tailTrace_5837186
  have hstable : (prefixWord ++ tailWord_5837186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837186).length < 2 ^ (prefixWord ++ tailWord_5837186).sum := by decide
  have hdescent : baseEnd_5837186 < baseStart_5837186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837188 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5837188 : Nat := 118140960795 + 5837188 * 2 ^ 59
def prefixEnd_5837188 : Nat := 4983230072969 + 3 ^ 40 * 5837188 * 2
def baseEnd_5837188 : Nat := 2997283114656813208805267

theorem tailTrace_5837188 : CollatzResearch.WordTrace tailWord_5837188 prefixEnd_5837188 2997283114656813208805267 := by
  unfold tailWord_5837188
  simp only [CollatzResearch.WordTrace]
  refine ⟨106449868388436131593632109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141933157851248175458176145 106449868388436131593632109)
  ·
    refine ⟨39918700645663549347612041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106449868388436131593632109 39918700645663549347612041)
    ·
      refine ⟨29939025484247662010709031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39918700645663549347612041 29939025484247662010709031)
      ·
        refine ⟨44908538226371493016063547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29939025484247662010709031 44908538226371493016063547)
        ·
          refine ⟨67362807339557239524095321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44908538226371493016063547 67362807339557239524095321)
          ·
            refine ⟨50522105504667929643071491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67362807339557239524095321 50522105504667929643071491)
            ·
              refine ⟨75783158257001894464607237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50522105504667929643071491 75783158257001894464607237)
              ·
                refine ⟨14209342173187855212113857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75783158257001894464607237 14209342173187855212113857)
                ·
                  refine ⟨10657006629890891409085393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14209342173187855212113857 10657006629890891409085393)
                  ·
                    refine ⟨7992754972418168556814045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10657006629890891409085393 7992754972418168556814045)
                    ·
                      refine ⟨2997283114656813208805267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7992754972418168556814045 2997283114656813208805267)
                      ·
                        rfl

theorem cell23_5837188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5837188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837188 prefixEnd_5837188 := by exact prefixLift 5837188
  have htrace : WordTrace (prefixWord ++ tailWord_5837188) baseStart_5837188 baseEnd_5837188 := by
    simpa [prefixWord, tailWord_5837188, baseEnd_5837188] using wordTrace_append hprefix tailTrace_5837188
  have hstable : (prefixWord ++ tailWord_5837188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837188).length < 2 ^ (prefixWord ++ tailWord_5837188).sum := by decide
  have hdescent : baseEnd_5837188 < baseStart_5837188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837195 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 1, 4]
def baseStart_5837195 : Nat := 118140960795 + 5837195 * 2 ^ 59
def prefixEnd_5837195 : Nat := 4983230072969 + 3 ^ 40 * 5837195 * 2
def baseEnd_5837195 : Nat := 999095569673798227139245

theorem tailTrace_5837195 : CollatzResearch.WordTrace tailWord_5837195 prefixEnd_5837195 999095569673798227139245 := by
  unfold tailWord_5837195
  simp only [CollatzResearch.WordTrace]
  refine ⟨212899992087846903382769039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141933328058564602255179359 212899992087846903382769039)
  ·
    refine ⟨319349988131770355074153559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212899992087846903382769039 319349988131770355074153559)
    ·
      refine ⟨479024982197655532611230339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319349988131770355074153559 479024982197655532611230339)
      ·
        refine ⟨718537473296483298916845509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479024982197655532611230339 718537473296483298916845509)
        ·
          refine ⟨134725776243090618546908533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 718537473296483298916845509 134725776243090618546908533)
          ·
            refine ⟨12630541522789745488772675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134725776243090618546908533 12630541522789745488772675)
            ·
              refine ⟨18945812284184618233159013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12630541522789745488772675 18945812284184618233159013)
              ·
                refine ⟨3552339803284615918717315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18945812284184618233159013 3552339803284615918717315)
                ·
                  refine ⟨5328509704926923878075973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552339803284615918717315 5328509704926923878075973)
                  ·
                    refine ⟨999095569673798227139245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328509704926923878075973 999095569673798227139245)
                    ·
                      rfl

theorem cell23_5837195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 4].length) (baseStart_5837195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837195 prefixEnd_5837195 := by exact prefixLift 5837195
  have htrace : WordTrace (prefixWord ++ tailWord_5837195) baseStart_5837195 baseEnd_5837195 := by
    simpa [prefixWord, tailWord_5837195, baseEnd_5837195] using wordTrace_append hprefix tailTrace_5837195
  have hstable : (prefixWord ++ tailWord_5837195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837195).length < 2 ^ (prefixWord ++ tailWord_5837195).sum := by decide
  have hdescent : baseEnd_5837195 < baseStart_5837195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837208 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 6]
def baseStart_5837208 : Nat := 118140960795 + 5837208 * 2 ^ 59
def prefixEnd_5837208 : Nat := 4983230072969 + 3 ^ 40 * 5837208 * 2
def baseEnd_5837208 : Nat := 333032598252211458950575

theorem tailTrace_5837208 : CollatzResearch.WordTrace tailWord_5837208 prefixEnd_5837208 333032598252211458950575 := by
  unfold tailWord_5837208
  simp only [CollatzResearch.WordTrace]
  refine ⟨106450233118399903301496139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141933644157866537735328185 106450233118399903301496139)
  ·
    refine ⟨159675349677599854952244209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106450233118399903301496139 159675349677599854952244209)
    ·
      refine ⟨119756512258199891214183157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159675349677599854952244209 119756512258199891214183157)
      ·
        refine ⟨11227173024206239801329671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119756512258199891214183157 11227173024206239801329671)
        ·
          refine ⟨16840759536309359701994507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11227173024206239801329671 16840759536309359701994507)
          ·
            refine ⟨25261139304464039552991761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16840759536309359701994507 25261139304464039552991761)
            ·
              refine ⟨18945854478348029664743821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25261139304464039552991761 18945854478348029664743821)
              ·
                refine ⟨7104695429380511124278933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18945854478348029664743821 7104695429380511124278933)
                ·
                  refine ⟨333032598252211458950575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7104695429380511124278933 333032598252211458950575)
                  ·
                    rfl

theorem cell23_5837208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 6].length) (baseStart_5837208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837208 prefixEnd_5837208 := by exact prefixLift 5837208
  have htrace : WordTrace (prefixWord ++ tailWord_5837208) baseStart_5837208 baseEnd_5837208 := by
    simpa [prefixWord, tailWord_5837208, baseEnd_5837208] using wordTrace_append hprefix tailTrace_5837208
  have hstable : (prefixWord ++ tailWord_5837208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837208).length < 2 ^ (prefixWord ++ tailWord_5837208).sum := by decide
  have hdescent : baseEnd_5837208 < baseStart_5837208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837221 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_5837221 : Nat := 118140960795 + 5837221 * 2 ^ 59
def prefixEnd_5837221 : Nat := 4983230072969 + 3 ^ 40 * 5837221 * 2
def baseEnd_5837221 : Nat := 999100019839470526564205

theorem tailTrace_5837221 : CollatzResearch.WordTrace tailWord_5837221 prefixEnd_5837221 999100019839470526564205 := by
  unfold tailWord_5837221
  simp only [CollatzResearch.WordTrace]
  refine ⟨212900940385752709823215517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141933960257168473215477011 212900940385752709823215517)
  ·
    refine ⟨79837852644657266183705819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212900940385752709823215517 79837852644657266183705819)
    ·
      refine ⟨119756778966985899275558729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79837852644657266183705819 119756778966985899275558729)
      ·
        refine ⟨89817584225239424456669047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119756778966985899275558729 89817584225239424456669047)
        ·
          refine ⟨134726376337859136685003571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89817584225239424456669047 134726376337859136685003571)
          ·
            refine ⟨202089564506788705027505357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134726376337859136685003571 202089564506788705027505357)
            ·
              refine ⟨75783586690045764385314509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202089564506788705027505357 75783586690045764385314509)
              ·
                refine ⟨28418845008767161644492941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75783586690045764385314509 28418845008767161644492941)
                ·
                  refine ⟨10657066878287685616684853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28418845008767161644492941 10657066878287685616684853)
                  ·
                    refine ⟨999100019839470526564205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10657066878287685616684853 999100019839470526564205)
                    ·
                      rfl

theorem cell23_5837221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_5837221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837221 prefixEnd_5837221 := by exact prefixLift 5837221
  have htrace : WordTrace (prefixWord ++ tailWord_5837221) baseStart_5837221 baseEnd_5837221 := by
    simpa [prefixWord, tailWord_5837221, baseEnd_5837221] using wordTrace_append hprefix tailTrace_5837221
  have hstable : (prefixWord ++ tailWord_5837221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837221).length < 2 ^ (prefixWord ++ tailWord_5837221).sum := by decide
  have hdescent : baseEnd_5837221 < baseStart_5837221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837229 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_5837229 : Nat := 118140960795 + 5837229 * 2 ^ 59
def prefixEnd_5837229 : Nat := 4983230072969 + 3 ^ 40 * 5837229 * 2
def baseEnd_5837229 : Nat := 999101389121215849464193

theorem tailTrace_5837229 : CollatzResearch.WordTrace tailWord_5837229 prefixEnd_5837229 999101389121215849464193 := by
  unfold tailWord_5837229
  simp only [CollatzResearch.WordTrace]
  refine ⟨212901232169723727189506741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141934154779815818126337827 212901232169723727189506741)
  ·
    refine ⟨19959490515911599424016257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212901232169723727189506741 19959490515911599424016257)
    ·
      refine ⟨14969617886933699568012193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19959490515911599424016257 14969617886933699568012193)
      ·
        refine ⟨11227213415200274676009145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14969617886933699568012193 11227213415200274676009145)
        ·
          refine ⟨8420410061400206007006859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11227213415200274676009145 8420410061400206007006859)
          ·
            refine ⟨12630615092100309010510289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8420410061400206007006859 12630615092100309010510289)
            ·
              refine ⟨9472961319075231757882717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12630615092100309010510289 9472961319075231757882717)
              ·
                refine ⟨3552360494653211909206019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9472961319075231757882717 3552360494653211909206019)
                ·
                  refine ⟨5328540741979817863809029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552360494653211909206019 5328540741979817863809029)
                  ·
                    refine ⟨999101389121215849464193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328540741979817863809029 999101389121215849464193)
                    ·
                      rfl

theorem cell23_5837229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_5837229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837229 prefixEnd_5837229 := by exact prefixLift 5837229
  have htrace : WordTrace (prefixWord ++ tailWord_5837229) baseStart_5837229 baseEnd_5837229 := by
    simpa [prefixWord, tailWord_5837229, baseEnd_5837229] using wordTrace_append hprefix tailTrace_5837229
  have hstable : (prefixWord ++ tailWord_5837229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837229).length < 2 ^ (prefixWord ++ tailWord_5837229).sum := by decide
  have hdescent : baseEnd_5837229 < baseStart_5837229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837281 : List Nat := [1, 2, 3, 1, 2, 2, 3, 9]
def baseStart_5837281 : Nat := 118140960795 + 5837281 * 2 ^ 59
def prefixEnd_5837281 : Nat := 4983230072969 + 3 ^ 40 * 5837281 * 2
def baseEnd_5837281 : Nat := 111012254383617827590457

theorem tailTrace_5837281 : CollatzResearch.WordTrace tailWord_5837281 prefixEnd_5837281 111012254383617827590457 := by
  unfold tailWord_5837281
  simp only [CollatzResearch.WordTrace]
  refine ⟨212903128765535340070399697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141935419177023560046933131 212903128765535340070399697)
  ·
    refine ⟨159677346574151505052799773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212903128765535340070399697 159677346574151505052799773)
    ·
      refine ⟨59879004965306814394799915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159677346574151505052799773 59879004965306814394799915)
      ·
        refine ⟨89818507447960221592199873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59879004965306814394799915 89818507447960221592199873)
        ·
          refine ⟨67363880585970166194149905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89818507447960221592199873 67363880585970166194149905)
          ·
            refine ⟨50522910439477624645612429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67363880585970166194149905 50522910439477624645612429)
            ·
              refine ⟨18946091414804109242104661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50522910439477624645612429 18946091414804109242104661)
              ·
                refine ⟨111012254383617827590457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18946091414804109242104661 111012254383617827590457)
                ·
                  rfl

theorem cell23_5837281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 9].length) (baseStart_5837281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837281 prefixEnd_5837281 := by exact prefixLift 5837281
  have htrace : WordTrace (prefixWord ++ tailWord_5837281) baseStart_5837281 baseEnd_5837281 := by
    simpa [prefixWord, tailWord_5837281, baseEnd_5837281] using wordTrace_append hprefix tailTrace_5837281
  have hstable : (prefixWord ++ tailWord_5837281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837281).length < 2 ^ (prefixWord ++ tailWord_5837281).sum := by decide
  have hdescent : baseEnd_5837281 < baseStart_5837281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837311 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 7]
def baseStart_5837311 : Nat := 118140960795 + 5837311 * 2 ^ 59
def prefixEnd_5837311 : Nat := 4983230072969 + 3 ^ 40 * 5837311 * 2
def baseEnd_5837311 : Nat := 999115424259105409189067

theorem tailTrace_5837311 : CollatzResearch.WordTrace tailWord_5837311 prefixEnd_5837311 999115424259105409189067 := by
  unfold tailWord_5837311
  simp only [CollatzResearch.WordTrace]
  refine ⟨212904222955426655193991787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141936148636951103462661191 212904222955426655193991787)
  ·
    refine ⟨319356334433139982790987681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212904222955426655193991787 319356334433139982790987681)
    ·
      refine ⟨239517250824854987093240761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319356334433139982790987681 239517250824854987093240761)
      ·
        refine ⟨179637938118641240319930571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239517250824854987093240761 179637938118641240319930571)
        ·
          refine ⟨269456907177961860479895857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179637938118641240319930571 269456907177961860479895857)
          ·
            refine ⟨202092680383471395359921893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269456907177961860479895857 202092680383471395359921893)
            ·
              refine ⟨37892377571900886629985355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202092680383471395359921893 37892377571900886629985355)
              ·
                refine ⟨56838566357851329944978033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37892377571900886629985355 56838566357851329944978033)
                ·
                  refine ⟨42628924768388497458733525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56838566357851329944978033 42628924768388497458733525)
                  ·
                    refine ⟨999115424259105409189067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42628924768388497458733525 999115424259105409189067)
                    ·
                      rfl

theorem cell23_5837311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_5837311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837311 prefixEnd_5837311 := by exact prefixLift 5837311
  have htrace : WordTrace (prefixWord ++ tailWord_5837311) baseStart_5837311 baseEnd_5837311 := by
    simpa [prefixWord, tailWord_5837311, baseEnd_5837311] using wordTrace_append hprefix tailTrace_5837311
  have hstable : (prefixWord ++ tailWord_5837311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837311).length < 2 ^ (prefixWord ++ tailWord_5837311).sum := by decide
  have hdescent : baseEnd_5837311 < baseStart_5837311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837319 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 2, 4]
def baseStart_5837319 : Nat := 118140960795 + 5837319 * 2 ^ 59
def prefixEnd_5837319 : Nat := 4983230072969 + 3 ^ 40 * 5837319 * 2
def baseEnd_5837319 : Nat := 999116793540850732089055

theorem tailTrace_5837319 : CollatzResearch.WordTrace tailWord_5837319 prefixEnd_5837319 999116793540850732089055 := by
  unfold tailWord_5837319
  simp only [CollatzResearch.WordTrace]
  refine ⟨212904514739397672560283011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141936343159598448373522007 212904514739397672560283011)
  ·
    refine ⟨319356772109096508840424517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212904514739397672560283011 319356772109096508840424517)
    ·
      refine ⟨59879394770455595407579597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319356772109096508840424517 59879394770455595407579597)
      ·
        refine ⟨22454773038920848277842349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59879394770455595407579597 22454773038920848277842349)
        ·
          refine ⟨8420539889595318104190881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22454773038920848277842349 8420539889595318104190881)
          ·
            refine ⟨6315404917196488578143161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8420539889595318104190881 6315404917196488578143161)
            ·
              refine ⟨4736553687897366433607371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315404917196488578143161 4736553687897366433607371)
              ·
                refine ⟨7104830531846049650411057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736553687897366433607371 7104830531846049650411057)
                ·
                  refine ⟨5328622898884537237808293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7104830531846049650411057 5328622898884537237808293)
                  ·
                    refine ⟨999116793540850732089055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328622898884537237808293 999116793540850732089055)
                    ·
                      rfl

theorem cell23_5837319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_5837319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837319 prefixEnd_5837319 := by exact prefixLift 5837319
  have htrace : WordTrace (prefixWord ++ tailWord_5837319) baseStart_5837319 baseEnd_5837319 := by
    simpa [prefixWord, tailWord_5837319, baseEnd_5837319] using wordTrace_append hprefix tailTrace_5837319
  have hstable : (prefixWord ++ tailWord_5837319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837319).length < 2 ^ (prefixWord ++ tailWord_5837319).sum := by decide
  have hdescent : baseEnd_5837319 < baseStart_5837319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837321 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_5837321 : Nat := 118140960795 + 5837321 * 2 ^ 59
def prefixEnd_5837321 : Nat := 4983230072969 + 3 ^ 40 * 5837321 * 2
def baseEnd_5837321 : Nat := 2997351407583861188442155

theorem tailTrace_5837321 : CollatzResearch.WordTrace tailWord_5837321 prefixEnd_5837321 2997351407583861188442155 := by
  unfold tailWord_5837321
  simp only [CollatzResearch.WordTrace]
  refine ⟨212904587685390426901855817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141936391790260284601237211 212904587685390426901855817)
  ·
    refine ⟨159678440764042820176391863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212904587685390426901855817 159678440764042820176391863)
    ·
      refine ⟨239517661146064230264587795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159678440764042820176391863 239517661146064230264587795)
      ·
        refine ⟨359276491719096345396881693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239517661146064230264587795 359276491719096345396881693)
        ·
          refine ⟨134728684394661129523830635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359276491719096345396881693 134728684394661129523830635)
          ·
            refine ⟨202093026591991694285745953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134728684394661129523830635 202093026591991694285745953)
            ·
              refine ⟨151569769943993770714309465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202093026591991694285745953 151569769943993770714309465)
              ·
                refine ⟨113677327457995328035732099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151569769943993770714309465 113677327457995328035732099)
                ·
                  refine ⟨170515991186992992053598149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113677327457995328035732099 170515991186992992053598149)
                  ·
                    refine ⟨31971748347561186010049653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170515991186992992053598149 31971748347561186010049653)
                    ·
                      refine ⟨2997351407583861188442155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31971748347561186010049653 2997351407583861188442155)
                      ·
                        rfl

theorem cell23_5837321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_5837321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837321 prefixEnd_5837321 := by exact prefixLift 5837321
  have htrace : WordTrace (prefixWord ++ tailWord_5837321) baseStart_5837321 baseEnd_5837321 := by
    simpa [prefixWord, tailWord_5837321, baseEnd_5837321] using wordTrace_append hprefix tailTrace_5837321
  have hstable : (prefixWord ++ tailWord_5837321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837321).length < 2 ^ (prefixWord ++ tailWord_5837321).sum := by decide
  have hdescent : baseEnd_5837321 < baseStart_5837321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837365 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_5837365 : Nat := 118140960795 + 5837365 * 2 ^ 59
def prefixEnd_5837365 : Nat := 4983230072969 + 3 ^ 40 * 5837365 * 2
def baseEnd_5837365 : Nat := 2997374000732659016291953

theorem tailTrace_5837365 : CollatzResearch.WordTrace tailWord_5837365 prefixEnd_5837365 2997374000732659016291953 := by
  unfold tailWord_5837365
  simp only [CollatzResearch.WordTrace]
  refine ⟨212906192497231022416457549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141937461664820681610971699 212906192497231022416457549)
  ·
    refine ⟨79839822186461633406171581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212906192497231022416457549 79839822186461633406171581)
    ·
      refine ⟨29939933319923112527314343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79839822186461633406171581 29939933319923112527314343)
      ·
        refine ⟨44909899979884668790971515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29939933319923112527314343 44909899979884668790971515)
        ·
          refine ⟨67364849969827003186457273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44909899979884668790971515 67364849969827003186457273)
          ·
            refine ⟨50523637477370252389842955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67364849969827003186457273 50523637477370252389842955)
            ·
              refine ⟨75785456216055378584764433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50523637477370252389842955 75785456216055378584764433)
              ·
                refine ⟨56839092162041533938573325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75785456216055378584764433 56839092162041533938573325)
                ·
                  refine ⟨21314659560765575226964997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56839092162041533938573325 21314659560765575226964997)
                  ·
                    refine ⟨3996498667643545355055937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21314659560765575226964997 3996498667643545355055937)
                    ·
                      refine ⟨2997374000732659016291953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996498667643545355055937 2997374000732659016291953)
                      ·
                        rfl

theorem cell23_5837365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_5837365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837365 prefixEnd_5837365 := by exact prefixLift 5837365
  have htrace : WordTrace (prefixWord ++ tailWord_5837365) baseStart_5837365 baseEnd_5837365 := by
    simpa [prefixWord, tailWord_5837365, baseEnd_5837365] using wordTrace_append hprefix tailTrace_5837365
  have hstable : (prefixWord ++ tailWord_5837365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837365).length < 2 ^ (prefixWord ++ tailWord_5837365).sum := by decide
  have hdescent : baseEnd_5837365 < baseStart_5837365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837368 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_5837368 : Nat := 118140960795 + 5837368 * 2 ^ 59
def prefixEnd_5837368 : Nat := 4983230072969 + 3 ^ 40 * 5837368 * 2
def baseEnd_5837368 : Nat := 2997375541174622504554439

theorem tailTrace_5837368 : CollatzResearch.WordTrace tailWord_5837368 prefixEnd_5837368 2997375541174622504554439 := by
  unfold tailWord_5837368
  simp only [CollatzResearch.WordTrace]
  refine ⟨106453150958110076964408379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141937534610813435952544505 106453150958110076964408379)
  ·
    refine ⟨159679726437165115446612569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106453150958110076964408379 159679726437165115446612569)
    ·
      refine ⟨119759794827873836584959427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159679726437165115446612569 119759794827873836584959427)
      ·
        refine ⟨179639692241810754877439141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119759794827873836584959427 179639692241810754877439141)
        ·
          refine ⟨33682442295339516539519839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179639692241810754877439141 33682442295339516539519839)
          ·
            refine ⟨50523663443009274809279759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33682442295339516539519839 50523663443009274809279759)
            ·
              refine ⟨75785495164513912213919639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50523663443009274809279759 75785495164513912213919639)
              ·
                refine ⟨113678242746770868320879459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75785495164513912213919639 113678242746770868320879459)
                ·
                  refine ⟨170517364120156302481319189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113678242746770868320879459 170517364120156302481319189)
                  ·
                    refine ⟨7993001443132326678811837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170517364120156302481319189 7993001443132326678811837)
                    ·
                      refine ⟨2997375541174622504554439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7993001443132326678811837 2997375541174622504554439)
                      ·
                        rfl

theorem cell23_5837368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_5837368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837368 prefixEnd_5837368 := by exact prefixLift 5837368
  have htrace : WordTrace (prefixWord ++ tailWord_5837368) baseStart_5837368 baseEnd_5837368 := by
    simpa [prefixWord, tailWord_5837368, baseEnd_5837368] using wordTrace_append hprefix tailTrace_5837368
  have hstable : (prefixWord ++ tailWord_5837368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837368).length < 2 ^ (prefixWord ++ tailWord_5837368).sum := by decide
  have hdescent : baseEnd_5837368 < baseStart_5837368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837388 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 7]
def baseStart_5837388 : Nat := 118140960795 + 5837388 * 2 ^ 59
def prefixEnd_5837388 : Nat := 4983230072969 + 3 ^ 40 * 5837388 * 2
def baseEnd_5837388 : Nat := 333042867865301380700483

theorem tailTrace_5837388 : CollatzResearch.WordTrace tailWord_5837388 prefixEnd_5837388 333042867865301380700483 := by
  unfold tailWord_5837388
  simp only [CollatzResearch.WordTrace]
  refine ⟨106453515688073848672272409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141938020917431798229696545 106453515688073848672272409)
  ·
    refine ⟨79840136766055386504204307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106453515688073848672272409 79840136766055386504204307)
    ·
      refine ⟨119760205149083079756306461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79840136766055386504204307 119760205149083079756306461)
      ·
        refine ⟨44910076930906154908614923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119760205149083079756306461 44910076930906154908614923)
        ·
          refine ⟨67365115396359232362922385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44910076930906154908614923 67365115396359232362922385)
          ·
            refine ⟨50523836547269424272191789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67365115396359232362922385 50523836547269424272191789)
            ·
              refine ⟨18946438705226034102071921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50523836547269424272191789 18946438705226034102071921)
              ·
                refine ⟨14209829028919525576553941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18946438705226034102071921 14209829028919525576553941)
                ·
                  refine ⟨333042867865301380700483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14209829028919525576553941 333042867865301380700483)
                  ·
                    rfl

theorem cell23_5837388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_5837388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837388 prefixEnd_5837388 := by exact prefixLift 5837388
  have htrace : WordTrace (prefixWord ++ tailWord_5837388) baseStart_5837388 baseEnd_5837388 := by
    simpa [prefixWord, tailWord_5837388, baseEnd_5837388] using wordTrace_append hprefix tailTrace_5837388
  have hstable : (prefixWord ++ tailWord_5837388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837388).length < 2 ^ (prefixWord ++ tailWord_5837388).sum := by decide
  have hdescent : baseEnd_5837388 < baseStart_5837388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837422 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_5837422 : Nat := 118140960795 + 5837422 * 2 ^ 59
def prefixEnd_5837422 : Nat := 4983230072969 + 3 ^ 40 * 5837422 * 2
def baseEnd_5837422 : Nat := 333044807681107254808799

theorem tailTrace_5837422 : CollatzResearch.WordTrace tailWord_5837422 prefixEnd_5837422 333044807681107254808799 := by
  unfold tailWord_5837422
  simp only [CollatzResearch.WordTrace]
  refine ⟨26613533932253065143910315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141938847638683014100855013 26613533932253065143910315)
  ·
    refine ⟨39920300898379597715865473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26613533932253065143910315 39920300898379597715865473)
    ·
      refine ⟨29940225673784698286899105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39920300898379597715865473 29940225673784698286899105)
      ·
        refine ⟨22455169255338523715174329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29940225673784698286899105 22455169255338523715174329)
        ·
          refine ⟨16841376941503892786380747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22455169255338523715174329 16841376941503892786380747)
          ·
            refine ⟨25262065412255839179571121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16841376941503892786380747 25262065412255839179571121)
            ·
              refine ⟨18946549059191879384678341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25262065412255839179571121 18946549059191879384678341)
              ·
                refine ⟨3552477948598477384627189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18946549059191879384678341 3552477948598477384627189)
                ·
                  refine ⟨333044807681107254808799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3552477948598477384627189 333044807681107254808799)
                  ·
                    rfl

theorem cell23_5837422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_5837422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837422 prefixEnd_5837422 := by exact prefixLift 5837422
  have htrace : WordTrace (prefixWord ++ tailWord_5837422) baseStart_5837422 baseEnd_5837422 := by
    simpa [prefixWord, tailWord_5837422, baseEnd_5837422] using wordTrace_append hprefix tailTrace_5837422
  have hstable : (prefixWord ++ tailWord_5837422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837422).length < 2 ^ (prefixWord ++ tailWord_5837422).sum := by decide
  have hdescent : baseEnd_5837422 < baseStart_5837422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837472 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_5837472 : Nat := 118140960795 + 5837472 * 2 ^ 59
def prefixEnd_5837472 : Nat := 4983230072969 + 3 ^ 40 * 5837472 * 2
def baseEnd_5837472 : Nat := 2997428943162690097653961

theorem tailTrace_5837472 : CollatzResearch.WordTrace tailWord_5837472 prefixEnd_5837472 2997428943162690097653961 := by
  unfold tailWord_5837472
  simp only [CollatzResearch.WordTrace]
  refine ⟨106455047553921689845301335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141940063405228919793735113 106455047553921689845301335)
  ·
    refine ⟨159682571330882534767952003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106455047553921689845301335 159682571330882534767952003)
    ·
      refine ⟨239523856996323802151928005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159682571330882534767952003 239523856996323802151928005)
      ·
        refine ⟨44910723186810712903486501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239523856996323802151928005 44910723186810712903486501)
        ·
          refine ⟨8420760597527008669403719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44910723186810712903486501 8420760597527008669403719)
          ·
            refine ⟨12631140896290513004105579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8420760597527008669403719 12631140896290513004105579)
            ·
              refine ⟨18946711344435769506158369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12631140896290513004105579 18946711344435769506158369)
              ·
                refine ⟨14210033508326827129618777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18946711344435769506158369 14210033508326827129618777)
                ·
                  refine ⟨10657525131245120347214083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14210033508326827129618777 10657525131245120347214083)
                  ·
                    refine ⟨15986287696867680520821125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10657525131245120347214083 15986287696867680520821125)
                    ·
                      refine ⟨2997428943162690097653961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15986287696867680520821125 2997428943162690097653961)
                      ·
                        rfl

theorem cell23_5837472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_5837472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837472 prefixEnd_5837472 := by exact prefixLift 5837472
  have htrace : WordTrace (prefixWord ++ tailWord_5837472) baseStart_5837472 baseEnd_5837472 := by
    simpa [prefixWord, tailWord_5837472, baseEnd_5837472] using wordTrace_append hprefix tailTrace_5837472
  have hstable : (prefixWord ++ tailWord_5837472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837472).length < 2 ^ (prefixWord ++ tailWord_5837472).sum := by decide
  have hdescent : baseEnd_5837472 < baseStart_5837472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837545 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_5837545 : Nat := 118140960795 + 5837545 * 2 ^ 59
def prefixEnd_5837545 : Nat := 4983230072969 + 3 ^ 40 * 5837545 * 2
def baseEnd_5837545 : Nat := 2997466427250468312041125

theorem tailTrace_5837545 : CollatzResearch.WordTrace tailWord_5837545 prefixEnd_5837545 2997466427250468312041125 := by
  unfold tailWord_5837545
  simp only [CollatzResearch.WordTrace]
  refine ⟨212912757636578913158010089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141941838424385942105340059 212912757636578913158010089)
  ·
    refine ⟨159684568227434184868507567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212912757636578913158010089 159684568227434184868507567)
    ·
      refine ⟨239526852341151277302761351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159684568227434184868507567 239526852341151277302761351)
      ·
        refine ⟨359290278511726915954142027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239526852341151277302761351 359290278511726915954142027)
        ·
          refine ⟨538935417767590373931213041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359290278511726915954142027 538935417767590373931213041)
          ·
            refine ⟨404201563325692780448409781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538935417767590373931213041 404201563325692780448409781)
            ·
              refine ⟨37893896561783698167038417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 404201563325692780448409781 37893896561783698167038417)
              ·
                refine ⟨28420422421337773625278813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37893896561783698167038417 28420422421337773625278813)
                ·
                  refine ⟨10657658408001665109479555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28420422421337773625278813 10657658408001665109479555)
                  ·
                    refine ⟨15986487612002497664219333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10657658408001665109479555 15986487612002497664219333)
                    ·
                      refine ⟨2997466427250468312041125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15986487612002497664219333 2997466427250468312041125)
                      ·
                        rfl

theorem cell23_5837545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_5837545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837545 prefixEnd_5837545 := by exact prefixLift 5837545
  have htrace : WordTrace (prefixWord ++ tailWord_5837545) baseStart_5837545 baseEnd_5837545 := by
    simpa [prefixWord, tailWord_5837545, baseEnd_5837545] using wordTrace_append hprefix tailTrace_5837545
  have hstable : (prefixWord ++ tailWord_5837545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837545).length < 2 ^ (prefixWord ++ tailWord_5837545).sum := by decide
  have hdescent : baseEnd_5837545 < baseStart_5837545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837555 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 6, 4]
def baseStart_5837555 : Nat := 118140960795 + 5837555 * 2 ^ 59
def prefixEnd_5837555 : Nat := 4983230072969 + 3 ^ 40 * 5837555 * 2
def baseEnd_5837555 : Nat := 999157187352337757638693

theorem tailTrace_5837555 : CollatzResearch.WordTrace tailWord_5837555 prefixEnd_5837555 999157187352337757638693 := by
  unfold tailWord_5837555
  simp only [CollatzResearch.WordTrace]
  refine ⟨212913122366542684865874119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141942081577695123243916079 212913122366542684865874119)
  ·
    refine ⟨319369683549814027298811179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212913122366542684865874119 319369683549814027298811179)
    ·
      refine ⟨479054525324721040948216769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319369683549814027298811179 479054525324721040948216769)
      ·
        refine ⟨359290893993540780711162577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479054525324721040948216769 359290893993540780711162577)
        ·
          refine ⟨269468170495155585533371933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359290893993540780711162577 269468170495155585533371933)
          ·
            refine ⟨101050563935683344575014475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269468170495155585533371933 101050563935683344575014475)
            ·
              refine ⟨151575845903525016862521713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101050563935683344575014475 151575845903525016862521713)
              ·
                refine ⟨113681884427643762646891285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151575845903525016862521713 113681884427643762646891285)
                ·
                  refine ⟨5328838332545801374073029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113681884427643762646891285 5328838332545801374073029)
                  ·
                    refine ⟨999157187352337757638693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328838332545801374073029 999157187352337757638693)
                    ·
                      rfl

theorem cell23_5837555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 4].length) (baseStart_5837555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837555 prefixEnd_5837555 := by exact prefixLift 5837555
  have htrace : WordTrace (prefixWord ++ tailWord_5837555) baseStart_5837555 baseEnd_5837555 := by
    simpa [prefixWord, tailWord_5837555, baseEnd_5837555] using wordTrace_append hprefix tailTrace_5837555
  have hstable : (prefixWord ++ tailWord_5837555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837555).length < 2 ^ (prefixWord ++ tailWord_5837555).sum := by decide
  have hdescent : baseEnd_5837555 < baseStart_5837555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837566 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5837566 : Nat := 118140960795 + 5837566 * 2 ^ 59
def prefixEnd_5837566 : Nat := 4983230072969 + 3 ^ 40 * 5837566 * 2
def baseEnd_5837566 : Nat := 2997477210344212729878529

theorem tailTrace_5837566 : CollatzResearch.WordTrace tailWord_5837566 prefixEnd_5837566 2997477210344212729878529 := by
  unfold tailWord_5837566
  simp only [CollatzResearch.WordTrace]
  refine ⟨26614190446187854218065569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141942349046335222496349701 26614190446187854218065569)
  ·
    refine ⟨19960642834640890663549177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26614190446187854218065569 19960642834640890663549177)
    ·
      refine ⟨14970482125980667997661883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19960642834640890663549177 14970482125980667997661883)
      ·
        refine ⟨22455723188971001996492825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14970482125980667997661883 22455723188971001996492825)
        ·
          refine ⟨16841792391728251497369619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22455723188971001996492825 16841792391728251497369619)
          ·
            refine ⟨25262688587592377246054429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16841792391728251497369619 25262688587592377246054429)
            ·
              refine ⟨9473508220347141467270411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25262688587592377246054429 9473508220347141467270411)
              ·
                refine ⟨14210262330520712200905617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9473508220347141467270411 14210262330520712200905617)
                ·
                  refine ⟨10657696747890534150679213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14210262330520712200905617 10657696747890534150679213)
                  ·
                    refine ⟨3996636280458950306504705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10657696747890534150679213 3996636280458950306504705)
                    ·
                      refine ⟨2997477210344212729878529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996636280458950306504705 2997477210344212729878529)
                      ·
                        rfl

theorem cell23_5837566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5837566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837566 prefixEnd_5837566 := by exact prefixLift 5837566
  have htrace : WordTrace (prefixWord ++ tailWord_5837566) baseStart_5837566 baseEnd_5837566 := by
    simpa [prefixWord, tailWord_5837566, baseEnd_5837566] using wordTrace_append hprefix tailTrace_5837566
  have hstable : (prefixWord ++ tailWord_5837566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837566).length < 2 ^ (prefixWord ++ tailWord_5837566).sum := by decide
  have hdescent : baseEnd_5837566 < baseStart_5837566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837572 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_5837572 : Nat := 118140960795 + 5837572 * 2 ^ 59
def prefixEnd_5837572 : Nat := 4983230072969 + 3 ^ 40 * 5837572 * 2
def baseEnd_5837572 : Nat := 999160097076046568801167

theorem tailTrace_5837572 : CollatzResearch.WordTrace tailWord_5837572 prefixEnd_5837572 999160097076046568801167 := by
  unfold tailWord_5837572
  simp only [CollatzResearch.WordTrace]
  refine ⟨106456871203740548384621485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141942494938320731179495313 106456871203740548384621485)
  ·
    refine ⟨39921326701402705644233057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106456871203740548384621485 39921326701402705644233057)
    ·
      refine ⟨29940995026052029233174793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39921326701402705644233057 29940995026052029233174793)
      ·
        refine ⟨22455746269539021924881095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29940995026052029233174793 22455746269539021924881095)
        ·
          refine ⟨33683619404308532887321643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22455746269539021924881095 33683619404308532887321643)
          ·
            refine ⟨50525429106462799330982465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33683619404308532887321643 50525429106462799330982465)
            ·
              refine ⟨37894071829847099498236849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50525429106462799330982465 37894071829847099498236849)
              ·
                refine ⟨28420553872385324623677637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37894071829847099498236849 28420553872385324623677637)
                ·
                  refine ⟨5328853851072248366939557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28420553872385324623677637 5328853851072248366939557)
                  ·
                    refine ⟨999160097076046568801167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5328853851072248366939557 999160097076046568801167)
                    ·
                      rfl

theorem cell23_5837572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_5837572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837572 prefixEnd_5837572 := by exact prefixLift 5837572
  have htrace : WordTrace (prefixWord ++ tailWord_5837572) baseStart_5837572 baseEnd_5837572 := by
    simpa [prefixWord, tailWord_5837572, baseEnd_5837572] using wordTrace_append hprefix tailTrace_5837572
  have hstable : (prefixWord ++ tailWord_5837572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837572).length < 2 ^ (prefixWord ++ tailWord_5837572).sum := by decide
  have hdescent : baseEnd_5837572 < baseStart_5837572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837596 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5837596 : Nat := 118140960795 + 5837596 * 2 ^ 59
def prefixEnd_5837596 : Nat := 4983230072969 + 3 ^ 40 * 5837596 * 2
def baseEnd_5837596 : Nat := 2997492614763847612503391

theorem tailTrace_5837596 : CollatzResearch.WordTrace tailWord_5837596 prefixEnd_5837596 2997492614763847612503391 := by
  unfold tailWord_5837596
  simp only [CollatzResearch.WordTrace]
  refine ⟨106457308879697074434058321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141943078506262765912077761 106457308879697074434058321)
  ·
    refine ⟨79842981659772805825543741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106457308879697074434058321 79842981659772805825543741)
    ·
      refine ⟨29941118122414802184578903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79842981659772805825543741 29941118122414802184578903)
      ·
        refine ⟨44911677183622203276868355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29941118122414802184578903 44911677183622203276868355)
        ·
          refine ⟨67367515775433304915302533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44911677183622203276868355 67367515775433304915302533)
          ·
            refine ⟨12631409207893744671619225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67367515775433304915302533 12631409207893744671619225)
            ·
              refine ⟨9473556905920308503714419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12631409207893744671619225 9473556905920308503714419)
              ·
                refine ⟨14210335358880462755571629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9473556905920308503714419 14210335358880462755571629)
                ·
                  refine ⟨5328875759580173533339361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14210335358880462755571629 5328875759580173533339361)
                  ·
                    refine ⟨3996656819685130150004521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5328875759580173533339361 3996656819685130150004521)
                    ·
                      refine ⟨2997492614763847612503391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996656819685130150004521 2997492614763847612503391)
                      ·
                        rfl

theorem cell23_5837596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5837596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837596 prefixEnd_5837596 := by exact prefixLift 5837596
  have htrace : WordTrace (prefixWord ++ tailWord_5837596) baseStart_5837596 baseEnd_5837596 := by
    simpa [prefixWord, tailWord_5837596, baseEnd_5837596] using wordTrace_append hprefix tailTrace_5837596
  have hstable : (prefixWord ++ tailWord_5837596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837596).length < 2 ^ (prefixWord ++ tailWord_5837596).sum := by decide
  have hdescent : baseEnd_5837596 < baseStart_5837596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837613 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5837613 : Nat := 118140960795 + 5837613 * 2 ^ 59
def prefixEnd_5837613 : Nat := 4983230072969 + 3 ^ 40 * 5837613 * 2
def baseEnd_5837613 : Nat := 2997501343934974045990813

theorem tailTrace_5837613 : CollatzResearch.WordTrace tailWord_5837613 prefixEnd_5837613 2997501343934974045990813 := by
  unfold tailWord_5837613
  simp only [CollatzResearch.WordTrace]
  refine ⟨212915237800332560771485493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141943491866888373847656995 212915237800332560771485493)
  ·
    refine ⟨19960803543781177572326765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212915237800332560771485493 19960803543781177572326765)
    ·
      refine ⟨7485301328917941589622537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19960803543781177572326765 7485301328917941589622537)
      ·
        refine ⟨5613975996688456192216903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7485301328917941589622537 5613975996688456192216903)
        ·
          refine ⟨8420963995032684288325355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613975996688456192216903 8420963995032684288325355)
          ·
            refine ⟨12631445992549026432488033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8420963995032684288325355 12631445992549026432488033)
            ·
              refine ⟨9473584494411769824366025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12631445992549026432488033 9473584494411769824366025)
              ·
                refine ⟨7105188370808827368274519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9473584494411769824366025 7105188370808827368274519)
                ·
                  refine ⟨10657782556213241052411779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105188370808827368274519 10657782556213241052411779)
                  ·
                    refine ⟨15986673834319861578617669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10657782556213241052411779 15986673834319861578617669)
                    ·
                      refine ⟨2997501343934974045990813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15986673834319861578617669 2997501343934974045990813)
                      ·
                        rfl

theorem cell23_5837613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5837613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837613 prefixEnd_5837613 := by exact prefixLift 5837613
  have htrace : WordTrace (prefixWord ++ tailWord_5837613) baseStart_5837613 baseEnd_5837613 := by
    simpa [prefixWord, tailWord_5837613, baseEnd_5837613] using wordTrace_append hprefix tailTrace_5837613
  have hstable : (prefixWord ++ tailWord_5837613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837613).length < 2 ^ (prefixWord ++ tailWord_5837613).sum := by decide
  have hdescent : baseEnd_5837613 < baseStart_5837613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837636 : List Nat := [2, 3, 4, 2, 2, 1, 9]
def baseStart_5837636 : Nat := 118140960795 + 5837636 * 2 ^ 59
def prefixEnd_5837636 : Nat := 4983230072969 + 3 ^ 40 * 5837636 * 2
def baseEnd_5837636 : Nat := 37006335234444783407447

theorem tailTrace_5837636 : CollatzResearch.WordTrace tailWord_5837636 prefixEnd_5837636 37006335234444783407447 := by
  unfold tailWord_5837636
  simp only [CollatzResearch.WordTrace]
  refine ⟨106458038339624617849786381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141944051119499490466381841 106458038339624617849786381)
  ·
    refine ⟨39921764377359231693669893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106458038339624617849786381 39921764377359231693669893)
    ·
      refine ⟨7485330820754855942563105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39921764377359231693669893 7485330820754855942563105)
      ·
        refine ⟨5613998115566141956922329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7485330820754855942563105 5613998115566141956922329)
        ·
          refine ⟨4210498586674606467691747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613998115566141956922329 4210498586674606467691747)
          ·
            refine ⟨6315747880011909701537621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210498586674606467691747 6315747880011909701537621)
            ·
              refine ⟨37006335234444783407447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6315747880011909701537621 37006335234444783407447)
              ·
                rfl

theorem cell23_5837636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 9].length) (baseStart_5837636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837636 prefixEnd_5837636 := by exact prefixLift 5837636
  have htrace : WordTrace (prefixWord ++ tailWord_5837636) baseStart_5837636 baseEnd_5837636 := by
    simpa [prefixWord, tailWord_5837636, baseEnd_5837636] using wordTrace_append hprefix tailTrace_5837636
  have hstable : (prefixWord ++ tailWord_5837636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837636).length < 2 ^ (prefixWord ++ tailWord_5837636).sum := by decide
  have hdescent : baseEnd_5837636 < baseStart_5837636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837672 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5837672 : Nat := 118140960795 + 5837672 * 2 ^ 59
def prefixEnd_5837672 : Nat := 4983230072969 + 3 ^ 40 * 5837672 * 2
def baseEnd_5837672 : Nat := 2997531639293589315153041

theorem tailTrace_5837672 : CollatzResearch.WordTrace tailWord_5837672 prefixEnd_5837672 2997531639293589315153041 := by
  unfold tailWord_5837672
  simp only [CollatzResearch.WordTrace]
  refine ⟨106458694853559406923941635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141944926471412542565255513 106458694853559406923941635)
  ·
    refine ⟨159688042280339110385912453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106458694853559406923941635 159688042280339110385912453)
    ·
      refine ⟨29941507927563583197358585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159688042280339110385912453 29941507927563583197358585)
      ·
        refine ⟨22456130945672687398018939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29941507927563583197358585 22456130945672687398018939)
        ·
          refine ⟨33684196418509031097028409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22456130945672687398018939 33684196418509031097028409)
          ·
            refine ⟨25263147313881773322771307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33684196418509031097028409 25263147313881773322771307)
            ·
              refine ⟨37894720970822659984156961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25263147313881773322771307 37894720970822659984156961)
              ·
                refine ⟨28421040728116994988117721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37894720970822659984156961 28421040728116994988117721)
                ·
                  refine ⟨21315780546087746241088291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28421040728116994988117721 21315780546087746241088291)
                  ·
                    refine ⟨31973670819131619361632437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21315780546087746241088291 31973670819131619361632437)
                    ·
                      refine ⟨2997531639293589315153041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31973670819131619361632437 2997531639293589315153041)
                      ·
                        rfl

theorem cell23_5837672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5837672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837672 prefixEnd_5837672 := by exact prefixLift 5837672
  have htrace : WordTrace (prefixWord ++ tailWord_5837672) baseStart_5837672 baseEnd_5837672 := by
    simpa [prefixWord, tailWord_5837672, baseEnd_5837672] using wordTrace_append hprefix tailTrace_5837672
  have hstable : (prefixWord ++ tailWord_5837672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837672).length < 2 ^ (prefixWord ++ tailWord_5837672).sum := by decide
  have hdescent : baseEnd_5837672 < baseStart_5837672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837675 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 7]
def baseStart_5837675 : Nat := 118140960795 + 5837675 * 2 ^ 59
def prefixEnd_5837675 : Nat := 4983230072969 + 3 ^ 40 * 5837675 * 2
def baseEnd_5837675 : Nat := 333059242192839200379503

theorem tailTrace_5837675 : CollatzResearch.WordTrace tailWord_5837675 prefixEnd_5837675 333059242192839200379503 := by
  unfold tailWord_5837675
  simp only [CollatzResearch.WordTrace]
  refine ⟨212917499126107945360242479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141944999417405296906828319 212917499126107945360242479)
  ·
    refine ⟨319376248689161918040363719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212917499126107945360242479 319376248689161918040363719)
    ·
      refine ⟨479064373033742877060545579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319376248689161918040363719 479064373033742877060545579)
      ·
        refine ⟨718596559550614315590818369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479064373033742877060545579 718596559550614315590818369)
        ·
          refine ⟨538947419662960736693113777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718596559550614315590818369 538947419662960736693113777)
          ·
            refine ⟨404210564747220552519835333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538947419662960736693113777 404210564747220552519835333)
            ·
              refine ⟨75789480890103853597469125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404210564747220552519835333 75789480890103853597469125)
              ·
                refine ⟨14210527666894472549525461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75789480890103853597469125 14210527666894472549525461)
                ·
                  refine ⟨333059242192839200379503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14210527666894472549525461 333059242192839200379503)
                  ·
                    rfl

theorem cell23_5837675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 7].length) (baseStart_5837675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837675 prefixEnd_5837675 := by exact prefixLift 5837675
  have htrace : WordTrace (prefixWord ++ tailWord_5837675) baseStart_5837675 baseEnd_5837675 := by
    simpa [prefixWord, tailWord_5837675, baseEnd_5837675] using wordTrace_append hprefix tailTrace_5837675
  have hstable : (prefixWord ++ tailWord_5837675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837675).length < 2 ^ (prefixWord ++ tailWord_5837675).sum := by decide
  have hdescent : baseEnd_5837675 < baseStart_5837675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837686 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5837686 : Nat := 118140960795 + 5837686 * 2 ^ 59
def prefixEnd_5837686 : Nat := 4983230072969 + 3 ^ 40 * 5837686 * 2
def baseEnd_5837686 : Nat := 2997538828022752260377977

theorem tailTrace_5837686 : CollatzResearch.WordTrace tailWord_5837686 prefixEnd_5837686 2997538828022752260377977 := by
  unfold tailWord_5837686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307368770566755889930807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141945266886045396159261941 13307368770566755889930807)
  ·
    refine ⟨19961053155850133834896211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13307368770566755889930807 19961053155850133834896211)
    ·
      refine ⟨29941579733775200752344317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19961053155850133834896211 29941579733775200752344317)
      ·
        refine ⟨11228092400165700282129119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29941579733775200752344317 11228092400165700282129119)
        ·
          refine ⟨16842138600248550423193679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11228092400165700282129119 16842138600248550423193679)
          ·
            refine ⟨25263207900372825634790519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16842138600248550423193679 25263207900372825634790519)
            ·
              refine ⟨37894811850559238452185779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25263207900372825634790519 37894811850559238452185779)
              ·
                refine ⟨56842217775838857678278669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37894811850559238452185779 56842217775838857678278669)
                ·
                  refine ⟨21315831665939571629354501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56842217775838857678278669 21315831665939571629354501)
                  ·
                    refine ⟨3996718437363669680503969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21315831665939571629354501 3996718437363669680503969)
                    ·
                      refine ⟨2997538828022752260377977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996718437363669680503969 2997538828022752260377977)
                      ·
                        rfl

theorem cell23_5837686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5837686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837686 prefixEnd_5837686 := by exact prefixLift 5837686
  have htrace : WordTrace (prefixWord ++ tailWord_5837686) baseStart_5837686 baseEnd_5837686 := by
    simpa [prefixWord, tailWord_5837686, baseEnd_5837686] using wordTrace_append hprefix tailTrace_5837686
  have hstable : (prefixWord ++ tailWord_5837686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837686).length < 2 ^ (prefixWord ++ tailWord_5837686).sum := by decide
  have hdescent : baseEnd_5837686 < baseStart_5837686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837703 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_5837703 : Nat := 118140960795 + 5837703 * 2 ^ 59
def prefixEnd_5837703 : Nat := 4983230072969 + 3 ^ 40 * 5837703 * 2
def baseEnd_5837703 : Nat := 2997547557193878693865399

theorem tailTrace_5837703 : CollatzResearch.WordTrace tailWord_5837703 prefixEnd_5837703 2997547557193878693865399 := by
  unfold tailWord_5837703
  simp only [CollatzResearch.WordTrace]
  refine ⟨212918520370006506142261763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141945680246671004094841175 212918520370006506142261763)
  ·
    refine ⟨319377780555009759213392645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212918520370006506142261763 319377780555009759213392645)
    ·
      refine ⟨59883333854064329852511121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319377780555009759213392645 59883333854064329852511121)
      ·
        refine ⟨44912500390548247389383341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59883333854064329852511121 44912500390548247389383341)
        ·
          refine ⟨16842187646455592771018753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44912500390548247389383341 16842187646455592771018753)
          ·
            refine ⟨12631640734841694578264065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16842187646455592771018753 12631640734841694578264065)
            ·
              refine ⟨9473730551131270933698049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12631640734841694578264065 9473730551131270933698049)
              ·
                refine ⟨7105297913348453200273537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9473730551131270933698049 7105297913348453200273537)
                ·
                  refine ⟨5328973435011339900205153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105297913348453200273537 5328973435011339900205153)
                  ·
                    refine ⟨3996730076258504925153865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5328973435011339900205153 3996730076258504925153865)
                    ·
                      refine ⟨2997547557193878693865399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996730076258504925153865 2997547557193878693865399)
                      ·
                        rfl

theorem cell23_5837703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_5837703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837703 prefixEnd_5837703 := by exact prefixLift 5837703
  have htrace : WordTrace (prefixWord ++ tailWord_5837703) baseStart_5837703 baseEnd_5837703 := by
    simpa [prefixWord, tailWord_5837703, baseEnd_5837703] using wordTrace_append hprefix tailTrace_5837703
  have hstable : (prefixWord ++ tailWord_5837703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837703).length < 2 ^ (prefixWord ++ tailWord_5837703).sum := by decide
  have hdescent : baseEnd_5837703 < baseStart_5837703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837715 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_5837715 : Nat := 118140960795 + 5837715 * 2 ^ 59
def prefixEnd_5837715 : Nat := 4983230072969 + 3 ^ 40 * 5837715 * 2
def baseEnd_5837715 : Nat := 2997553718961732646915343

theorem tailTrace_5837715 : CollatzResearch.WordTrace tailWord_5837715 prefixEnd_5837715 2997553718961732646915343 := by
  unfold tailWord_5837715
  simp only [CollatzResearch.WordTrace]
  refine ⟨212918958045963032191698599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141945972030642021461132399 212918958045963032191698599)
  ·
    refine ⟨319378437068944548287547899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212918958045963032191698599 319378437068944548287547899)
    ·
      refine ⟨479067655603416822431321849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319378437068944548287547899 479067655603416822431321849)
      ·
        refine ⟨359300741702562616823491387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479067655603416822431321849 359300741702562616823491387)
        ·
          refine ⟨538951112553843925235237081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359300741702562616823491387 538951112553843925235237081)
          ·
            refine ⟨404213334415382943926427811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538951112553843925235237081 404213334415382943926427811)
            ·
              refine ⟨606320001623074415889641717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404213334415382943926427811 606320001623074415889641717)
              ·
                refine ⟨56842500152163226489653911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 606320001623074415889641717 56842500152163226489653911)
                ·
                  refine ⟨85263750228244839734480867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56842500152163226489653911 85263750228244839734480867)
                  ·
                    refine ⟨127895625342367259601721301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85263750228244839734480867 127895625342367259601721301)
                    ·
                      refine ⟨2997553718961732646915343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127895625342367259601721301 2997553718961732646915343)
                      ·
                        rfl

theorem cell23_5837715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_5837715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837715 prefixEnd_5837715 := by exact prefixLift 5837715
  have htrace : WordTrace (prefixWord ++ tailWord_5837715) baseStart_5837715 baseEnd_5837715 := by
    simpa [prefixWord, tailWord_5837715, baseEnd_5837715] using wordTrace_append hprefix tailTrace_5837715
  have hstable : (prefixWord ++ tailWord_5837715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837715).length < 2 ^ (prefixWord ++ tailWord_5837715).sum := by decide
  have hdescent : baseEnd_5837715 < baseStart_5837715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837772 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5837772 : Nat := 118140960795 + 5837772 * 2 ^ 59
def prefixEnd_5837772 : Nat := 4983230072969 + 3 ^ 40 * 5837772 * 2
def baseEnd_5837772 : Nat := 2997582987359038923902581

theorem tailTrace_5837772 : CollatzResearch.WordTrace tailWord_5837772 prefixEnd_5837772 2997582987359038923902581 := by
  unfold tailWord_5837772
  simp only [CollatzResearch.WordTrace]
  refine ⟨106460518503378265463261785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141947358004504353951015713 106460518503378265463261785)
  ·
    refine ⟨79845388877533699097446339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106460518503378265463261785 79845388877533699097446339)
    ·
      refine ⟨119768083316300548646169509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79845388877533699097446339 119768083316300548646169509)
      ·
        refine ⟨22456515621806352871156783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119768083316300548646169509 22456515621806352871156783)
        ·
          refine ⟨33684773432709529306735175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22456515621806352871156783 33684773432709529306735175)
          ·
            refine ⟨50527160149064293960102763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33684773432709529306735175 50527160149064293960102763)
            ·
              refine ⟨75790740223596440940154145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50527160149064293960102763 75790740223596440940154145)
              ·
                refine ⟨56843055167697330705115609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75790740223596440940154145 56843055167697330705115609)
                ·
                  refine ⟨42632291375772998028836707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56843055167697330705115609 42632291375772998028836707)
                  ·
                    refine ⟨63948437063659497043255061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42632291375772998028836707 63948437063659497043255061)
                    ·
                      refine ⟨2997582987359038923902581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63948437063659497043255061 2997582987359038923902581)
                      ·
                        rfl

theorem cell23_5837772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5837772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837772 prefixEnd_5837772 := by exact prefixLift 5837772
  have htrace : WordTrace (prefixWord ++ tailWord_5837772) baseStart_5837772 baseEnd_5837772 := by
    simpa [prefixWord, tailWord_5837772, baseEnd_5837772] using wordTrace_append hprefix tailTrace_5837772
  have hstable : (prefixWord ++ tailWord_5837772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837772).length < 2 ^ (prefixWord ++ tailWord_5837772).sum := by decide
  have hdescent : baseEnd_5837772 < baseStart_5837772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837849 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 6, 2]
def baseStart_5837849 : Nat := 118140960795 + 5837849 * 2 ^ 59
def prefixEnd_5837849 : Nat := 4983230072969 + 3 ^ 40 * 5837849 * 2
def baseEnd_5837849 : Nat := 2997622525369435122639727

theorem tailTrace_5837849 : CollatzResearch.WordTrace tailWord_5837849 prefixEnd_5837849 2997622525369435122639727 := by
  unfold tailWord_5837849
  simp only [CollatzResearch.WordTrace]
  refine ⟨212923845427477573077076601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141949230284985048718051067 212923845427477573077076601)
  ·
    refine ⟨159692884070608179807807451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212923845427477573077076601 159692884070608179807807451)
    ·
      refine ⟨239539326105912269711711177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159692884070608179807807451 239539326105912269711711177)
      ·
        refine ⟨179654494579434202283783383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239539326105912269711711177 179654494579434202283783383)
        ·
          refine ⟨269481741869151303425675075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179654494579434202283783383 269481741869151303425675075)
          ·
            refine ⟨404222612803726955138512613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269481741869151303425675075 404222612803726955138512613)
            ·
              refine ⟨75791739900698804088471115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404222612803726955138512613 75791739900698804088471115)
              ·
                refine ⟨113687609851048206132706673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75791739900698804088471115 113687609851048206132706673)
                ·
                  refine ⟨85265707388286154599530005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113687609851048206132706673 85265707388286154599530005)
                  ·
                    refine ⟨3996830033825913496852969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85265707388286154599530005 3996830033825913496852969)
                    ·
                      refine ⟨2997622525369435122639727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3996830033825913496852969 2997622525369435122639727)
                      ·
                        rfl

theorem cell23_5837849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_5837849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837849 prefixEnd_5837849 := by exact prefixLift 5837849
  have htrace : WordTrace (prefixWord ++ tailWord_5837849) baseStart_5837849 baseEnd_5837849 := by
    simpa [prefixWord, tailWord_5837849, baseEnd_5837849] using wordTrace_append hprefix tailTrace_5837849
  have hstable : (prefixWord ++ tailWord_5837849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837849).length < 2 ^ (prefixWord ++ tailWord_5837849).sum := by decide
  have hdescent : baseEnd_5837849 < baseStart_5837849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837859 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 1, 6]
def baseStart_5837859 : Nat := 118140960795 + 5837859 * 2 ^ 59
def prefixEnd_5837859 : Nat := 4983230072969 + 3 ^ 40 * 5837859 * 2
def baseEnd_5837859 : Nat := 999209220058660027838227

theorem tailTrace_5837859 : CollatzResearch.WordTrace tailWord_5837859 prefixEnd_5837859 999209220058660027838227 := by
  unfold tailWord_5837859
  simp only [CollatzResearch.WordTrace]
  refine ⟨212924210157441344784940631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141949473438294229856627087 212924210157441344784940631)
  ·
    refine ⟨319386315236162017177410947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212924210157441344784940631 319386315236162017177410947)
    ·
      refine ⟨479079472854243025766116421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319386315236162017177410947 479079472854243025766116421)
      ·
        refine ⟨89827401160170567331146829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479079472854243025766116421 89827401160170567331146829)
        ·
          refine ⟨33685275435063962749180061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89827401160170567331146829 33685275435063962749180061)
          ·
            refine ⟨12631978288148986030942523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33685275435063962749180061 12631978288148986030942523)
            ·
              refine ⟨18947967432223479046413785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12631978288148986030942523 18947967432223479046413785)
              ·
                refine ⟨14210975574167609284810339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18947967432223479046413785 14210975574167609284810339)
                ·
                  refine ⟨21316463361251413927215509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14210975574167609284810339 21316463361251413927215509)
                  ·
                    refine ⟨999209220058660027838227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21316463361251413927215509 999209220058660027838227)
                    ·
                      rfl

theorem cell23_5837859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 6].length) (baseStart_5837859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837859 prefixEnd_5837859 := by exact prefixLift 5837859
  have htrace : WordTrace (prefixWord ++ tailWord_5837859) baseStart_5837859 baseEnd_5837859 := by
    simpa [prefixWord, tailWord_5837859, baseEnd_5837859] using wordTrace_append hprefix tailTrace_5837859
  have hstable : (prefixWord ++ tailWord_5837859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837859).length < 2 ^ (prefixWord ++ tailWord_5837859).sum := by decide
  have hdescent : baseEnd_5837859 < baseStart_5837859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837906 : List Nat := [3, 2, 2, 1, 3, 2, 3, 7]
def baseStart_5837906 : Nat := 118140960795 + 5837906 * 2 ^ 59
def prefixEnd_5837906 : Nat := 4983230072969 + 3 ^ 40 * 5837906 * 2
def baseEnd_5837906 : Nat := 111024140509879311097295

theorem tailTrace_5837906 : CollatzResearch.WordTrace tailWord_5837906 prefixEnd_5837906 111024140509879311097295 := by
  unfold tailWord_5837906
  simp only [CollatzResearch.WordTrace]
  refine ⟨53231481097067767952975393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141950616258847381207934381 53231481097067767952975393)
  ·
    refine ⟨39923610822800825964731545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53231481097067767952975393 39923610822800825964731545)
    ·
      refine ⟨29942708117100619473548659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39923610822800825964731545 29942708117100619473548659)
      ·
        refine ⟨44914062175650929210322989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29942708117100619473548659 44914062175650929210322989)
        ·
          refine ⟨16842773315869098453871121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44914062175650929210322989 16842773315869098453871121)
          ·
            refine ⟨12632079986901823840403341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16842773315869098453871121 12632079986901823840403341)
            ·
              refine ⟨4737029995088183940151253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12632079986901823840403341 4737029995088183940151253)
              ·
                refine ⟨111024140509879311097295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4737029995088183940151253 111024140509879311097295)
                ·
                  rfl

theorem cell23_5837906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_5837906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837906 prefixEnd_5837906 := by exact prefixLift 5837906
  have htrace : WordTrace (prefixWord ++ tailWord_5837906) baseStart_5837906 baseEnd_5837906 := by
    simpa [prefixWord, tailWord_5837906, baseEnd_5837906] using wordTrace_append hprefix tailTrace_5837906
  have hstable : (prefixWord ++ tailWord_5837906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837906).length < 2 ^ (prefixWord ++ tailWord_5837906).sum := by decide
  have hdescent : baseEnd_5837906 < baseStart_5837906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837916 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_5837916 : Nat := 118140960795 + 5837916 * 2 ^ 59
def prefixEnd_5837916 : Nat := 4983230072969 + 3 ^ 40 * 5837916 * 2
def baseEnd_5837916 : Nat := 2997656928573286360501919

theorem tailTrace_5837916 : CollatzResearch.WordTrace tailWord_5837916 prefixEnd_5837916 2997656928573286360501919 := by
  unfold tailWord_5837916
  simp only [CollatzResearch.WordTrace]
  refine ⟨106463144559117421759882801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141950859412156562346510401 106463144559117421759882801)
  ·
    refine ⟨79847358419338066319912101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106463144559117421759882801 79847358419338066319912101)
    ·
      refine ⟨14971379703625887434983519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79847358419338066319912101 14971379703625887434983519)
      ·
        refine ⟨22457069555438831152475279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14971379703625887434983519 22457069555438831152475279)
        ·
          refine ⟨33685604333158246728712919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22457069555438831152475279 33685604333158246728712919)
          ·
            refine ⟨50528406499737370093069379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33685604333158246728712919 50528406499737370093069379)
            ·
              refine ⟨75792609749606055139604069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50528406499737370093069379 75792609749606055139604069)
              ·
                refine ⟨14211114328051135338675763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75792609749606055139604069 14211114328051135338675763)
                ·
                  refine ⟨21316671492076703008013645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14211114328051135338675763 21316671492076703008013645)
                  ·
                    refine ⟨7993751809528763628005117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21316671492076703008013645 7993751809528763628005117)
                    ·
                      refine ⟨2997656928573286360501919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7993751809528763628005117 2997656928573286360501919)
                      ·
                        rfl

theorem cell23_5837916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_5837916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837916 prefixEnd_5837916 := by exact prefixLift 5837916
  have htrace : WordTrace (prefixWord ++ tailWord_5837916) baseStart_5837916 baseEnd_5837916 := by
    simpa [prefixWord, tailWord_5837916, baseEnd_5837916] using wordTrace_append hprefix tailTrace_5837916
  have hstable : (prefixWord ++ tailWord_5837916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837916).length < 2 ^ (prefixWord ++ tailWord_5837916).sum := by decide
  have hdescent : baseEnd_5837916 < baseStart_5837916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837917 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5837917 : Nat := 118140960795 + 5837917 * 2 ^ 59
def prefixEnd_5837917 : Nat := 4983230072969 + 3 ^ 40 * 5837917 * 2
def baseEnd_5837917 : Nat := 2997657442053940856589415

theorem tailTrace_5837917 : CollatzResearch.WordTrace tailWord_5837917 prefixEnd_5837917 2997657442053940856589415 := by
  unfold tailWord_5837917
  simp only [CollatzResearch.WordTrace]
  refine ⟨212926325591231220690552005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141950883727487480460368003 212926325591231220690552005)
  ·
    refine ⟨39923686048355853879478501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212926325591231220690552005 39923686048355853879478501)
    ·
      refine ⟨7485691134066722602402219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39923686048355853879478501 7485691134066722602402219)
      ·
        refine ⟨11228536701100083903603329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7485691134066722602402219 11228536701100083903603329)
        ·
          refine ⟨8421402525825062927702497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11228536701100083903603329 8421402525825062927702497)
          ·
            refine ⟨6316051894368797195776873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8421402525825062927702497 6316051894368797195776873)
            ·
              refine ⟨4737038920776597896832655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6316051894368797195776873 4737038920776597896832655)
              ·
                refine ⟨7105558381164896845248983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737038920776597896832655 7105558381164896845248983)
                ·
                  refine ⟨10658337571747345267873475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105558381164896845248983 10658337571747345267873475)
                  ·
                    refine ⟨15987506357621017901810213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10658337571747345267873475 15987506357621017901810213)
                    ·
                      refine ⟨2997657442053940856589415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15987506357621017901810213 2997657442053940856589415)
                      ·
                        rfl

theorem cell23_5837917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5837917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837917 prefixEnd_5837917 := by exact prefixLift 5837917
  have htrace : WordTrace (prefixWord ++ tailWord_5837917) baseStart_5837917 baseEnd_5837917 := by
    simpa [prefixWord, tailWord_5837917, baseEnd_5837917] using wordTrace_append hprefix tailTrace_5837917
  have hstable : (prefixWord ++ tailWord_5837917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837917).length < 2 ^ (prefixWord ++ tailWord_5837917).sum := by decide
  have hdescent : baseEnd_5837917 < baseStart_5837917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837933 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_5837933 : Nat := 118140960795 + 5837933 * 2 ^ 59
def prefixEnd_5837933 : Nat := 4983230072969 + 3 ^ 40 * 5837933 * 2
def baseEnd_5837933 : Nat := 2997665657744412793989341

theorem tailTrace_5837933 : CollatzResearch.WordTrace tailWord_5837933 prefixEnd_5837933 2997665657744412793989341 := by
  unfold tailWord_5837933
  simp only [CollatzResearch.WordTrace]
  refine ⟨212926909159173255423134453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141951272772782170282089635 212926909159173255423134453)
  ·
    refine ⟨19961897733672492695918855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212926909159173255423134453 19961897733672492695918855)
    ·
      refine ⟨29942846600508739043878283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19961897733672492695918855 29942846600508739043878283)
      ·
        refine ⟨44914269900763108565817425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29942846600508739043878283 44914269900763108565817425)
        ·
          refine ⟨33685702425572331424363069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44914269900763108565817425 33685702425572331424363069)
          ·
            refine ⟨12632138409589624284136151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33685702425572331424363069 12632138409589624284136151)
            ·
              refine ⟨18948207614384436426204227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12632138409589624284136151 18948207614384436426204227)
              ·
                refine ⟨28422311421576654639306341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18948207614384436426204227 28422311421576654639306341)
                ·
                  refine ⟨5329183391545622744869939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28422311421576654639306341 5329183391545622744869939)
                  ·
                    refine ⟨7993775087318434117304909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329183391545622744869939 7993775087318434117304909)
                    ·
                      refine ⟨2997665657744412793989341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7993775087318434117304909 2997665657744412793989341)
                      ·
                        rfl

theorem cell23_5837933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_5837933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837933 prefixEnd_5837933 := by exact prefixLift 5837933
  have htrace : WordTrace (prefixWord ++ tailWord_5837933) baseStart_5837933 baseEnd_5837933 := by
    simpa [prefixWord, tailWord_5837933, baseEnd_5837933] using wordTrace_append hprefix tailTrace_5837933
  have hstable : (prefixWord ++ tailWord_5837933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837933).length < 2 ^ (prefixWord ++ tailWord_5837933).sum := by decide
  have hdescent : baseEnd_5837933 < baseStart_5837933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837949 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_5837949 : Nat := 118140960795 + 5837949 * 2 ^ 59
def prefixEnd_5837949 : Nat := 4983230072969 + 3 ^ 40 * 5837949 * 2
def baseEnd_5837949 : Nat := 999224624478294910463089

theorem tailTrace_5837949 : CollatzResearch.WordTrace tailWord_5837949 prefixEnd_5837949 999224624478294910463089 := by
  unfold tailWord_5837949
  simp only [CollatzResearch.WordTrace]
  refine ⟨212927492727115290155716901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141951661818076860103811267 212927492727115290155716901)
  ·
    refine ⟨39923904886334116904196919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212927492727115290155716901 39923904886334116904196919)
    ·
      refine ⟨59885857329501175356295379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39923904886334116904196919 59885857329501175356295379)
      ·
        refine ⟨89828785994251763034443069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59885857329501175356295379 89828785994251763034443069)
        ·
          refine ⟨33685794747844411137916151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89828785994251763034443069 33685794747844411137916151)
          ·
            refine ⟨50528692121766616706874227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33685794747844411137916151 50528692121766616706874227)
            ·
              refine ⟨75793038182649925060311341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50528692121766616706874227 75793038182649925060311341)
              ·
                refine ⟨28422389318493721897616753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75793038182649925060311341 28422389318493721897616753)
                ·
                  refine ⟨21316791988870291423212565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28422389318493721897616753 21316791988870291423212565)
                  ·
                    refine ⟨999224624478294910463089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21316791988870291423212565 999224624478294910463089)
                    ·
                      rfl

theorem cell23_5837949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_5837949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837949 prefixEnd_5837949 := by exact prefixLift 5837949
  have htrace : WordTrace (prefixWord ++ tailWord_5837949) baseStart_5837949 baseEnd_5837949 := by
    simpa [prefixWord, tailWord_5837949, baseEnd_5837949] using wordTrace_append hprefix tailTrace_5837949
  have hstable : (prefixWord ++ tailWord_5837949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837949).length < 2 ^ (prefixWord ++ tailWord_5837949).sum := by decide
  have hdescent : baseEnd_5837949 < baseStart_5837949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837959 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_5837959 : Nat := 118140960795 + 5837959 * 2 ^ 59
def prefixEnd_5837959 : Nat := 4983230072969 + 3 ^ 40 * 5837959 * 2
def baseEnd_5837959 : Nat := 2997679008241429692264221

theorem tailTrace_5837959 : CollatzResearch.WordTrace tailWord_5837959 prefixEnd_5837959 2997679008241429692264221 := by
  unfold tailWord_5837959
  simp only [CollatzResearch.WordTrace]
  refine ⟨212927857457079061863580931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141951904971386041242387287 212927857457079061863580931)
  ·
    refine ⟨319391786185618592795371397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212927857457079061863580931 319391786185618592795371397)
    ·
      refine ⟨59885959909803486149132137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319391786185618592795371397 59885959909803486149132137)
      ·
        refine ⟨44914469932352614611849103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59885959909803486149132137 44914469932352614611849103)
        ·
          refine ⟨67371704898528921917773655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44914469932352614611849103 67371704898528921917773655)
          ·
            refine ⟨101057557347793382876660483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67371704898528921917773655 101057557347793382876660483)
            ·
              refine ⟨151586336021690074314990725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101057557347793382876660483 151586336021690074314990725)
              ·
                refine ⟨28422438004066888934060761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151586336021690074314990725 28422438004066888934060761)
                ·
                  refine ⟨21316828503050166700545571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28422438004066888934060761 21316828503050166700545571)
                  ·
                    refine ⟨31975242754575250050818357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21316828503050166700545571 31975242754575250050818357)
                    ·
                      refine ⟨2997679008241429692264221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31975242754575250050818357 2997679008241429692264221)
                      ·
                        rfl

theorem cell23_5837959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_5837959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837959 prefixEnd_5837959 := by exact prefixLift 5837959
  have htrace : WordTrace (prefixWord ++ tailWord_5837959) baseStart_5837959 baseEnd_5837959 := by
    simpa [prefixWord, tailWord_5837959, baseEnd_5837959] using wordTrace_append hprefix tailTrace_5837959
  have hstable : (prefixWord ++ tailWord_5837959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837959).length < 2 ^ (prefixWord ++ tailWord_5837959).sum := by decide
  have hdescent : baseEnd_5837959 < baseStart_5837959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5837976 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5837976 : Nat := 118140960795 + 5837976 * 2 ^ 59
def prefixEnd_5837976 : Nat := 4983230072969 + 3 ^ 40 * 5837976 * 2
def baseEnd_5837976 : Nat := 2997687737412556125751643

theorem tailTrace_5837976 : CollatzResearch.WordTrace tailWord_5837976 prefixEnd_5837976 2997687737412556125751643 := by
  unfold tailWord_5837976
  simp only [CollatzResearch.WordTrace]
  refine ⟨106464238749008736883474891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141952318332011649177966521 106464238749008736883474891)
  ·
    refine ⟨159696358123513105325212337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106464238749008736883474891 159696358123513105325212337)
    ·
      refine ⟨119772268592634828993909253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159696358123513105325212337 119772268592634828993909253)
      ·
        refine ⟨22457300361119030436357985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119772268592634828993909253 22457300361119030436357985)
        ·
          refine ⟨16842975270839272827268489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22457300361119030436357985 16842975270839272827268489)
          ·
            refine ⟨12632231453129454620451367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16842975270839272827268489 12632231453129454620451367)
            ·
              refine ⟨18948347179694181930677051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12632231453129454620451367 18948347179694181930677051)
              ·
                refine ⟨28422520769541272896015577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18948347179694181930677051 28422520769541272896015577)
                ·
                  refine ⟨21316890577155954672011683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28422520769541272896015577 21316890577155954672011683)
                  ·
                    refine ⟨31975335865733932008017525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21316890577155954672011683 31975335865733932008017525)
                    ·
                      refine ⟨2997687737412556125751643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31975335865733932008017525 2997687737412556125751643)
                      ·
                        rfl

theorem cell23_5837976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5837976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5837976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5837976 prefixEnd_5837976 := by exact prefixLift 5837976
  have htrace : WordTrace (prefixWord ++ tailWord_5837976) baseStart_5837976 baseEnd_5837976 := by
    simpa [prefixWord, tailWord_5837976, baseEnd_5837976] using wordTrace_append hprefix tailTrace_5837976
  have hstable : (prefixWord ++ tailWord_5837976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5837976).length < 2 ^ (prefixWord ++ tailWord_5837976).sum := by decide
  have hdescent : baseEnd_5837976 < baseStart_5837976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5837976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838026 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_5838026 : Nat := 118140960795 + 5838026 * 2 ^ 59
def prefixEnd_5838026 : Nat := 4983230072969 + 3 ^ 40 * 5838026 * 2
def baseEnd_5838026 : Nat := 999237803815093643375471

theorem tailTrace_5838026 : CollatzResearch.WordTrace tailWord_5838026 prefixEnd_5838026 999237803815093643375471 := by
  unfold tailWord_5838026
  simp only [CollatzResearch.WordTrace]
  refine ⟨53232575286959083076567483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141953534098557554870846621 53232575286959083076567483)
  ·
    refine ⟨79848862930438624614851225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53232575286959083076567483 79848862930438624614851225)
    ·
      refine ⟨59886647197828968461138419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79848862930438624614851225 59886647197828968461138419)
      ·
        refine ⟨89829970796743452691707629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59886647197828968461138419 89829970796743452691707629)
        ·
          refine ⟨33686239048778794759390361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89829970796743452691707629 33686239048778794759390361)
          ·
            refine ⟨25264679286584096069542771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33686239048778794759390361 25264679286584096069542771)
            ·
              refine ⟨37897018929876144104314157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25264679286584096069542771 37897018929876144104314157)
              ·
                refine ⟨14211382098703554039117809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37897018929876144104314157 14211382098703554039117809)
                ·
                  refine ⟨10658536574027665529338357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14211382098703554039117809 10658536574027665529338357)
                  ·
                    refine ⟨999237803815093643375471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10658536574027665529338357 999237803815093643375471)
                    ·
                      rfl

theorem cell23_5838026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_5838026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838026 prefixEnd_5838026 := by exact prefixLift 5838026
  have htrace : WordTrace (prefixWord ++ tailWord_5838026) baseStart_5838026 baseEnd_5838026 := by
    simpa [prefixWord, tailWord_5838026, baseEnd_5838026] using wordTrace_append hprefix tailTrace_5838026
  have hstable : (prefixWord ++ tailWord_5838026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838026).length < 2 ^ (prefixWord ++ tailWord_5838026).sum := by decide
  have hdescent : baseEnd_5838026 < baseStart_5838026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838083 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3]
def baseStart_5838083 : Nat := 118140960795 + 5838083 * 2 ^ 59
def prefixEnd_5838083 : Nat := 4983230072969 + 3 ^ 40 * 5838083 * 2
def baseEnd_5838083 : Nat := 2997742679842587207113651

theorem tailTrace_5838083 : CollatzResearch.WordTrace tailWord_5838083 prefixEnd_5838083 2997742679842587207113651 := by
  unfold tailWord_5838083
  simp only [CollatzResearch.WordTrace]
  refine ⟨212932380108629831041094903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141954920072419887360729935 212932380108629831041094903)
  ·
    refine ⟨319398570162944746561642355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212932380108629831041094903 319398570162944746561642355)
    ·
      refine ⟨479097855244417119842463533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319398570162944746561642355 479097855244417119842463533)
      ·
        refine ⟨179661695716656419940923825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479097855244417119842463533 179661695716656419940923825)
        ·
          refine ⟨134746271787492314955692869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179661695716656419940923825 134746271787492314955692869)
          ·
            refine ⟨25264925960154809054192413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134746271787492314955692869 25264925960154809054192413)
            ·
              refine ⟨9474347235058053395322155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25264925960154809054192413 9474347235058053395322155)
              ·
                refine ⟨14211520852587080092983233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9474347235058053395322155 14211520852587080092983233)
                ·
                  refine ⟨10658640639440310069737425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14211520852587080092983233 10658640639440310069737425)
                  ·
                    refine ⟨7993980479580232552303069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10658640639440310069737425 7993980479580232552303069)
                    ·
                      refine ⟨2997742679842587207113651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7993980479580232552303069 2997742679842587207113651)
                      ·
                        rfl

theorem cell23_5838083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_5838083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838083 prefixEnd_5838083 := by exact prefixLift 5838083
  have htrace : WordTrace (prefixWord ++ tailWord_5838083) baseStart_5838083 baseEnd_5838083 := by
    simpa [prefixWord, tailWord_5838083, baseEnd_5838083] using wordTrace_append hprefix tailTrace_5838083
  have hstable : (prefixWord ++ tailWord_5838083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838083).length < 2 ^ (prefixWord ++ tailWord_5838083).sum := by decide
  have hdescent : baseEnd_5838083 < baseStart_5838083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838106 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_5838106 : Nat := 118140960795 + 5838106 * 2 ^ 59
def prefixEnd_5838106 : Nat := 4983230072969 + 3 ^ 40 * 5838106 * 2
def baseEnd_5838106 : Nat := 2997754489897640617126045

theorem tailTrace_5838106 : CollatzResearch.WordTrace tailWord_5838106 prefixEnd_5838106 2997754489897640617126045 := by
  unfold tailWord_5838106
  simp only [CollatzResearch.WordTrace]
  refine ⟨53233304746886626492295543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141955479325031003979454781 53233304746886626492295543)
  ·
    refine ⟨79849957120329939738443315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53233304746886626492295543 79849957120329939738443315)
    ·
      refine ⟨119774935680494909607664973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79849957120329939738443315 119774935680494909607664973)
      ·
        refine ⟨44915600880185591102874365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119774935680494909607664973 44915600880185591102874365)
        ·
          refine ⟨16843350330069596663577887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44915600880185591102874365 16843350330069596663577887)
          ·
            refine ⟨25265025495104394995366831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16843350330069596663577887 25265025495104394995366831)
            ·
              refine ⟨37897538242656592493050247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25265025495104394995366831 37897538242656592493050247)
              ·
                refine ⟨56846307363984888739575371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37897538242656592493050247 56846307363984888739575371)
                ·
                  refine ⟨85269461045977333109363057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56846307363984888739575371 85269461045977333109363057)
                  ·
                    refine ⟨63952095784482999832022293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85269461045977333109363057 63952095784482999832022293)
                    ·
                      refine ⟨2997754489897640617126045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63952095784482999832022293 2997754489897640617126045)
                      ·
                        rfl

theorem cell23_5838106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_5838106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838106 prefixEnd_5838106 := by exact prefixLift 5838106
  have htrace : WordTrace (prefixWord ++ tailWord_5838106) baseStart_5838106 baseEnd_5838106 := by
    simpa [prefixWord, tailWord_5838106, baseEnd_5838106] using wordTrace_append hprefix tailTrace_5838106
  have hstable : (prefixWord ++ tailWord_5838106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838106).length < 2 ^ (prefixWord ++ tailWord_5838106).sum := by decide
  have hdescent : baseEnd_5838106 < baseStart_5838106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838120 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 6]
def baseStart_5838120 : Nat := 118140960795 + 5838120 * 2 ^ 59
def prefixEnd_5838120 : Nat := 4983230072969 + 3 ^ 40 * 5838120 * 2
def baseEnd_5838120 : Nat := 333084630958533729150109

theorem tailTrace_5838120 : CollatzResearch.WordTrace tailWord_5838120 prefixEnd_5838120 333084630958533729150109 := by
  unfold tailWord_5838120
  simp only [CollatzResearch.WordTrace]
  refine ⟨106466864804747893180095907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141955819739663857573461209 106466864804747893180095907)
  ·
    refine ⟨159700297207121839770143861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106466864804747893180095907 159700297207121839770143861)
    ·
      refine ⟨14971902863167672478450987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159700297207121839770143861 14971902863167672478450987)
      ·
        refine ⟨22457854294751508717676481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14971902863167672478450987 22457854294751508717676481)
        ·
          refine ⟨16843390721063631538257361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22457854294751508717676481 16843390721063631538257361)
          ·
            refine ⟨12632543040797723653693021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16843390721063631538257361 12632543040797723653693021)
            ·
              refine ⟨4737203640299146370134883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12632543040797723653693021 4737203640299146370134883)
              ·
                refine ⟨7105805460448719555202325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737203640299146370134883 7105805460448719555202325)
                ·
                  refine ⟨333084630958533729150109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7105805460448719555202325 333084630958533729150109)
                  ·
                    rfl

theorem cell23_5838120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 6].length) (baseStart_5838120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838120 prefixEnd_5838120 := by exact prefixLift 5838120
  have htrace : WordTrace (prefixWord ++ tailWord_5838120) baseStart_5838120 baseEnd_5838120 := by
    simpa [prefixWord, tailWord_5838120, baseEnd_5838120] using wordTrace_append hprefix tailTrace_5838120
  have hstable : (prefixWord ++ tailWord_5838120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838120).length < 2 ^ (prefixWord ++ tailWord_5838120).sum := by decide
  have hdescent : baseEnd_5838120 < baseStart_5838120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838130 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_5838130 : Nat := 118140960795 + 5838130 * 2 ^ 59
def prefixEnd_5838130 : Nat := 4983230072969 + 3 ^ 40 * 5838130 * 2
def baseEnd_5838130 : Nat := 2997766813433348523225935

theorem tailTrace_5838130 : CollatzResearch.WordTrace tailWord_5838130 prefixEnd_5838130 2997766813433348523225935 := by
  unfold tailWord_5838130
  simp only [CollatzResearch.WordTrace]
  refine ⟨53233523584864889517013961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141956062892973038712037229 53233523584864889517013961)
  ·
    refine ⟨39925142688648667137760471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53233523584864889517013961 39925142688648667137760471)
    ·
      refine ⟨59887714032973000706640707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39925142688648667137760471 59887714032973000706640707)
      ·
        refine ⟨89831571049459501059961061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59887714032973000706640707 89831571049459501059961061)
        ·
          refine ⟨16843419571773656448742699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89831571049459501059961061 16843419571773656448742699)
          ·
            refine ⟨25265129357660484673114049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16843419571773656448742699 25265129357660484673114049)
            ·
              refine ⟨18948847018245363504835537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25265129357660484673114049 18948847018245363504835537)
              ·
                refine ⟨14211635263684022628626653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18948847018245363504835537 14211635263684022628626653)
                ·
                  refine ⟨5329363223881508485734995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14211635263684022628626653 5329363223881508485734995)
                  ·
                    refine ⟨7994044835822262728602493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329363223881508485734995 7994044835822262728602493)
                    ·
                      refine ⟨2997766813433348523225935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994044835822262728602493 2997766813433348523225935)
                      ·
                        rfl

theorem cell23_5838130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_5838130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838130 prefixEnd_5838130 := by exact prefixLift 5838130
  have htrace : WordTrace (prefixWord ++ tailWord_5838130) baseStart_5838130 baseEnd_5838130 := by
    simpa [prefixWord, tailWord_5838130, baseEnd_5838130] using wordTrace_append hprefix tailTrace_5838130
  have hstable : (prefixWord ++ tailWord_5838130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838130).length < 2 ^ (prefixWord ++ tailWord_5838130).sum := by decide
  have hdescent : baseEnd_5838130 < baseStart_5838130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838133 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_5838133 : Nat := 118140960795 + 5838133 * 2 ^ 59
def prefixEnd_5838133 : Nat := 4983230072969 + 3 ^ 40 * 5838133 * 2
def baseEnd_5838133 : Nat := 999256117958437337162807

theorem tailTrace_5838133 : CollatzResearch.WordTrace tailWord_5838133 prefixEnd_5838133 999256117958437337162807 := by
  unfold tailWord_5838133
  simp only [CollatzResearch.WordTrace]
  refine ⟨212934203758448689580415053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141956135838965793053610035 212934203758448689580415053)
  ·
    refine ⟨79850326409418258592655645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212934203758448689580415053 79850326409418258592655645)
    ·
      refine ⟨29943872403531846972245867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79850326409418258592655645 29943872403531846972245867)
      ·
        refine ⟨44915808605297770458368801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29943872403531846972245867 44915808605297770458368801)
        ·
          refine ⟨33686856453973327843776601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44915808605297770458368801 33686856453973327843776601)
          ·
            refine ⟨25265142340479995882832451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33686856453973327843776601 25265142340479995882832451)
            ·
              refine ⟨37897713510719993824248677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25265142340479995882832451 37897713510719993824248677)
              ·
                refine ⟨7105821283259998842046627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37897713510719993824248677 7105821283259998842046627)
                ·
                  refine ⟨10658731924889998263069941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105821283259998842046627 10658731924889998263069941)
                  ·
                    refine ⟨999256117958437337162807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10658731924889998263069941 999256117958437337162807)
                    ·
                      rfl

theorem cell23_5838133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_5838133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838133 prefixEnd_5838133 := by exact prefixLift 5838133
  have htrace : WordTrace (prefixWord ++ tailWord_5838133) baseStart_5838133 baseEnd_5838133 := by
    simpa [prefixWord, tailWord_5838133, baseEnd_5838133] using wordTrace_append hprefix tailTrace_5838133
  have hstable : (prefixWord ++ tailWord_5838133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838133).length < 2 ^ (prefixWord ++ tailWord_5838133).sum := by decide
  have hdescent : baseEnd_5838133 < baseStart_5838133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838141 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_5838141 : Nat := 118140960795 + 5838141 * 2 ^ 59
def prefixEnd_5838141 : Nat := 4983230072969 + 3 ^ 40 * 5838141 * 2
def baseEnd_5838141 : Nat := 999257487240182660062795

theorem tailTrace_5838141 : CollatzResearch.WordTrace tailWord_5838141 prefixEnd_5838141 999257487240182660062795 := by
  unfold tailWord_5838141
  simp only [CollatzResearch.WordTrace]
  refine ⟨212934495542419706946706277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141956330361613137964470851 212934495542419706946706277)
  ·
    refine ⟨39925217914203695052507427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212934495542419706946706277 39925217914203695052507427)
    ·
      refine ⟨59887826871305542578761141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39925217914203695052507427 59887826871305542578761141)
      ·
        refine ⟨5614483769184894616758857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59887826871305542578761141 5614483769184894616758857)
        ·
          refine ⟨4210862826888670962569143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5614483769184894616758857 4210862826888670962569143)
          ·
            refine ⟨6316294240333006443853715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210862826888670962569143 6316294240333006443853715)
            ·
              refine ⟨9474441360499509665780573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316294240333006443853715 9474441360499509665780573)
              ·
                refine ⟨3552915510187316124667715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9474441360499509665780573 3552915510187316124667715)
                ·
                  refine ⟨5329373265280974187001573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552915510187316124667715 5329373265280974187001573)
                  ·
                    refine ⟨999257487240182660062795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329373265280974187001573 999257487240182660062795)
                    ·
                      rfl

theorem cell23_5838141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_5838141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838141 prefixEnd_5838141 := by exact prefixLift 5838141
  have htrace : WordTrace (prefixWord ++ tailWord_5838141) baseStart_5838141 baseEnd_5838141 := by
    simpa [prefixWord, tailWord_5838141, baseEnd_5838141] using wordTrace_append hprefix tailTrace_5838141
  have hstable : (prefixWord ++ tailWord_5838141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838141).length < 2 ^ (prefixWord ++ tailWord_5838141).sum := by decide
  have hdescent : baseEnd_5838141 < baseStart_5838141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838153 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_5838153 : Nat := 118140960795 + 5838153 * 2 ^ 59
def prefixEnd_5838153 : Nat := 4983230072969 + 3 ^ 40 * 5838153 * 2
def baseEnd_5838153 : Nat := 2997778623488401933238329

theorem tailTrace_5838153 : CollatzResearch.WordTrace tailWord_5838153 prefixEnd_5838153 2997778623488401933238329 := by
  unfold tailWord_5838153
  simp only [CollatzResearch.WordTrace]
  refine ⟨212934933218376232996143113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141956622145584155330762075 212934933218376232996143113)
  ·
    refine ⟨159701199913782174747107335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212934933218376232996143113 159701199913782174747107335)
    ·
      refine ⟨239551799870673262120661003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159701199913782174747107335 239551799870673262120661003)
      ·
        refine ⟨359327699806009893180991505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239551799870673262120661003 359327699806009893180991505)
        ·
          refine ⟨269495774854507419885743629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359327699806009893180991505 269495774854507419885743629)
          ·
            refine ⟨101060915570440282457153861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269495774854507419885743629 101060915570440282457153861)
            ·
              refine ⟨18948921669457552960716349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101060915570440282457153861 18948921669457552960716349)
              ·
                refine ⟨7105845626046582360268631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18948921669457552960716349 7105845626046582360268631)
                ·
                  refine ⟨10658768439069873540402947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105845626046582360268631 10658768439069873540402947)
                  ·
                    refine ⟨15988152658604810310604421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10658768439069873540402947 15988152658604810310604421)
                    ·
                      refine ⟨2997778623488401933238329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15988152658604810310604421 2997778623488401933238329)
                      ·
                        rfl

theorem cell23_5838153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_5838153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838153 prefixEnd_5838153 := by exact prefixLift 5838153
  have htrace : WordTrace (prefixWord ++ tailWord_5838153) baseStart_5838153 baseEnd_5838153 := by
    simpa [prefixWord, tailWord_5838153, baseEnd_5838153] using wordTrace_append hprefix tailTrace_5838153
  have hstable : (prefixWord ++ tailWord_5838153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838153).length < 2 ^ (prefixWord ++ tailWord_5838153).sum := by decide
  have hdescent : baseEnd_5838153 < baseStart_5838153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838163 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 2, 4]
def baseStart_5838163 : Nat := 118140960795 + 5838163 * 2 ^ 59
def prefixEnd_5838163 : Nat := 4983230072969 + 3 ^ 40 * 5838163 * 2
def baseEnd_5838163 : Nat := 999261252764982298037761

theorem tailTrace_5838163 : CollatzResearch.WordTrace tailWord_5838163 prefixEnd_5838163 999261252764982298037761 := by
  unfold tailWord_5838163
  simp only [CollatzResearch.WordTrace]
  refine ⟨212935297948340004704007143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141956865298893336469338095 212935297948340004704007143)
  ·
    refine ⟨319402946922510007056010715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212935297948340004704007143 319402946922510007056010715)
    ·
      refine ⟨479104420383765010584016073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319402946922510007056010715 479104420383765010584016073)
      ·
        refine ⟨359328315287823757938012055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479104420383765010584016073 359328315287823757938012055)
        ·
          refine ⟨538992472931735636907018083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359328315287823757938012055 538992472931735636907018083)
          ·
            refine ⟨808488709397603455360527125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538992472931735636907018083 808488709397603455360527125)
            ·
              refine ⟨37897908253012661970024709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 808488709397603455360527125 37897908253012661970024709)
              ·
                refine ⟨7105857797439874119379633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37897908253012661970024709 7105857797439874119379633)
                ·
                  refine ⟨5329393348079905589534725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105857797439874119379633 5329393348079905589534725)
                  ·
                    refine ⟨999261252764982298037761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329393348079905589534725 999261252764982298037761)
                    ·
                      rfl

theorem cell23_5838163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 4].length) (baseStart_5838163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838163 prefixEnd_5838163 := by exact prefixLift 5838163
  have htrace : WordTrace (prefixWord ++ tailWord_5838163) baseStart_5838163 baseEnd_5838163 := by
    simpa [prefixWord, tailWord_5838163, baseEnd_5838163] using wordTrace_append hprefix tailTrace_5838163
  have hstable : (prefixWord ++ tailWord_5838163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838163).length < 2 ^ (prefixWord ++ tailWord_5838163).sum := by decide
  have hdescent : baseEnd_5838163 < baseStart_5838163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838164 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_5838164 : Nat := 118140960795 + 5838164 * 2 ^ 59
def prefixEnd_5838164 : Nat := 4983230072969 + 3 ^ 40 * 5838164 * 2
def baseEnd_5838164 : Nat := 2997784271775601390200779

theorem tailTrace_5838164 : CollatzResearch.WordTrace tailWord_5838164 prefixEnd_5838164 2997784271775601390200779 := by
  unfold tailWord_5838164
  simp only [CollatzResearch.WordTrace]
  refine ⟨106467667210668190937396773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141956889614224254583195697 106467667210668190937396773)
  ·
    refine ⟨19962687602000285800761895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106467667210668190937396773 19962687602000285800761895)
    ·
      refine ⟨29944031403000428701142843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19962687602000285800761895 29944031403000428701142843)
      ·
        refine ⟨44916047104500643051714265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29944031403000428701142843 44916047104500643051714265)
        ·
          refine ⟨33687035328375482288785699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44916047104500643051714265 33687035328375482288785699)
          ·
            refine ⟨50530552992563223433178549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33687035328375482288785699 50530552992563223433178549)
            ·
              refine ⟨4737239343052802196860489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50530552992563223433178549 4737239343052802196860489)
              ·
                refine ⟨3552929507289601647645367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4737239343052802196860489 3552929507289601647645367)
                ·
                  refine ⟨5329394260934402471468051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552929507289601647645367 5329394260934402471468051)
                  ·
                    refine ⟨7994091391401603707202077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329394260934402471468051 7994091391401603707202077)
                    ·
                      refine ⟨2997784271775601390200779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994091391401603707202077 2997784271775601390200779)
                      ·
                        rfl

theorem cell23_5838164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_5838164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838164 prefixEnd_5838164 := by exact prefixLift 5838164
  have htrace : WordTrace (prefixWord ++ tailWord_5838164) baseStart_5838164 baseEnd_5838164 := by
    simpa [prefixWord, tailWord_5838164, baseEnd_5838164] using wordTrace_append hprefix tailTrace_5838164
  have hstable : (prefixWord ++ tailWord_5838164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838164).length < 2 ^ (prefixWord ++ tailWord_5838164).sum := by decide
  have hdescent : baseEnd_5838164 < baseStart_5838164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838176 : List Nat := [2, 1, 1, 3, 4, 1, 1, 10]
def baseStart_5838176 : Nat := 118140960795 + 5838176 * 2 ^ 59
def prefixEnd_5838176 : Nat := 4983230072969 + 3 ^ 40 * 5838176 * 2
def baseEnd_5838176 : Nat := 111029275316424271972249

theorem tailTrace_5838176 : CollatzResearch.WordTrace tailWord_5838176 prefixEnd_5838176 111029275316424271972249 := by
  unfold tailWord_5838176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106467886048646453962115191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141957181398195271949486921 106467886048646453962115191)
  ·
    refine ⟨159701829072969680943172787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106467886048646453962115191 159701829072969680943172787)
    ·
      refine ⟨239552743609454521414759181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159701829072969680943172787 239552743609454521414759181)
      ·
        refine ⟨89832278853545445530534693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239552743609454521414759181 89832278853545445530534693)
        ·
          refine ⟨16843552285039771036975255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89832278853545445530534693 16843552285039771036975255)
          ·
            refine ⟨25265328427559656555462883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16843552285039771036975255 25265328427559656555462883)
            ·
              refine ⟨37897992641339484833194325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25265328427559656555462883 37897992641339484833194325)
              ·
                refine ⟨111029275316424271972249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37897992641339484833194325 111029275316424271972249)
                ·
                  rfl

theorem cell23_5838176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 10].length) (baseStart_5838176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838176 prefixEnd_5838176 := by exact prefixLift 5838176
  have htrace : WordTrace (prefixWord ++ tailWord_5838176) baseStart_5838176 baseEnd_5838176 := by
    simpa [prefixWord, tailWord_5838176, baseEnd_5838176] using wordTrace_append hprefix tailTrace_5838176
  have hstable : (prefixWord ++ tailWord_5838176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838176).length < 2 ^ (prefixWord ++ tailWord_5838176).sum := by decide
  have hdescent : baseEnd_5838176 < baseStart_5838176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838180 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_5838180 : Nat := 118140960795 + 5838180 * 2 ^ 59
def prefixEnd_5838180 : Nat := 4983230072969 + 3 ^ 40 * 5838180 * 2
def baseEnd_5838180 : Nat := 999264162488691109200235

theorem tailTrace_5838180 : CollatzResearch.WordTrace tailWord_5838180 prefixEnd_5838180 999264162488691109200235 := by
  unfold tailWord_5838180
  simp only [CollatzResearch.WordTrace]
  refine ⟨106467958994639208303687997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141957278659518944404917329 106467958994639208303687997)
  ·
    refine ⟨39925484622989703113882999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106467958994639208303687997 39925484622989703113882999)
    ·
      refine ⟨59888226934484554670824499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39925484622989703113882999 59888226934484554670824499)
      ·
        refine ⟨89832340401726832006236749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59888226934484554670824499 89832340401726832006236749)
        ·
          refine ⟨33687127650647562002338781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89832340401726832006236749 33687127650647562002338781)
          ·
            refine ⟨12632672868992835750877043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33687127650647562002338781 12632672868992835750877043)
            ·
              refine ⟨18949009303489253626315565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12632672868992835750877043 18949009303489253626315565)
              ·
                refine ⟨7105878488808470109868337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18949009303489253626315565 7105878488808470109868337)
                ·
                  refine ⟨5329408866606352582401253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105878488808470109868337 5329408866606352582401253)
                  ·
                    refine ⟨999264162488691109200235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329408866606352582401253 999264162488691109200235)
                    ·
                      rfl

theorem cell23_5838180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_5838180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838180 prefixEnd_5838180 := by exact prefixLift 5838180
  have htrace : WordTrace (prefixWord ++ tailWord_5838180) baseStart_5838180 baseEnd_5838180 := by
    simpa [prefixWord, tailWord_5838180, baseEnd_5838180] using wordTrace_append hprefix tailTrace_5838180
  have hstable : (prefixWord ++ tailWord_5838180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838180).length < 2 ^ (prefixWord ++ tailWord_5838180).sum := by decide
  have hdescent : baseEnd_5838180 < baseStart_5838180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838203 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3]
def baseStart_5838203 : Nat := 118140960795 + 5838203 * 2 ^ 59
def prefixEnd_5838203 : Nat := 4983230072969 + 3 ^ 40 * 5838203 * 2
def baseEnd_5838203 : Nat := 2997804297521126737613099

theorem tailTrace_5838203 : CollatzResearch.WordTrace tailWord_5838203 prefixEnd_5838203 2997804297521126737613099 := by
  unfold tailWord_5838203
  simp only [CollatzResearch.WordTrace]
  refine ⟨212936756868195091535463263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141957837912130061023642175 212936756868195091535463263)
  ·
    refine ⟨319405135302292637303194895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212936756868195091535463263 319405135302292637303194895)
    ·
      refine ⟨479107702953438955954792343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319405135302292637303194895 479107702953438955954792343)
      ·
        refine ⟨718661554430158433932188515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479107702953438955954792343 718661554430158433932188515)
        ·
          refine ⟨1077992331645237650898282773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718661554430158433932188515 1077992331645237650898282773)
          ·
            refine ⟨50530890545870514885857005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1077992331645237650898282773 50530890545870514885857005)
            ·
              refine ⟨18949083954701443082196377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50530890545870514885857005 18949083954701443082196377)
              ·
                refine ⟨14211812966026082311647283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18949083954701443082196377 14211812966026082311647283)
                ·
                  refine ⟨21317719449039123467470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14211812966026082311647283 21317719449039123467470925)
                  ·
                    refine ⟨7994144793389671300301597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21317719449039123467470925 7994144793389671300301597)
                    ·
                      refine ⟨2997804297521126737613099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994144793389671300301597 2997804297521126737613099)
                      ·
                        rfl

theorem cell23_5838203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3].length) (baseStart_5838203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838203 prefixEnd_5838203 := by exact prefixLift 5838203
  have htrace : WordTrace (prefixWord ++ tailWord_5838203) baseStart_5838203 baseEnd_5838203 := by
    simpa [prefixWord, tailWord_5838203, baseEnd_5838203] using wordTrace_append hprefix tailTrace_5838203
  have hstable : (prefixWord ++ tailWord_5838203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838203).length < 2 ^ (prefixWord ++ tailWord_5838203).sum := by decide
  have hdescent : baseEnd_5838203 < baseStart_5838203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838237 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_5838237 : Nat := 118140960795 + 5838237 * 2 ^ 59
def prefixEnd_5838237 : Nat := 4983230072969 + 3 ^ 40 * 5838237 * 2
def baseEnd_5838237 : Nat := 2997821755863379604587943

theorem tailTrace_5838237 : CollatzResearch.WordTrace tailWord_5838237 prefixEnd_5838237 2997821755863379604587943 := by
  unfold tailWord_5838237
  simp only [CollatzResearch.WordTrace]
  refine ⟨212937996950071915342200965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141958664633381276894800643 212937996950071915342200965)
  ·
    refine ⟨39925874428138484126662681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212937996950071915342200965 39925874428138484126662681)
    ·
      refine ⟨29944405821103863094997011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39925874428138484126662681 29944405821103863094997011)
      ·
        refine ⟨44916608731655794642495517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29944405821103863094997011 44916608731655794642495517)
        ·
          refine ⟨16843728274370922990935819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44916608731655794642495517 16843728274370922990935819)
          ·
            refine ⟨25265592411556384486403729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16843728274370922990935819 25265592411556384486403729)
            ·
              refine ⟨18949194308667288364802797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25265592411556384486403729 18949194308667288364802797)
              ·
                refine ⟨7105947865750233136801049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18949194308667288364802797 7105947865750233136801049)
                ·
                  refine ⟨5329460899312674852600787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105947865750233136801049 5329460899312674852600787)
                  ·
                    refine ⟨7994191348969012278901181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329460899312674852600787 7994191348969012278901181)
                    ·
                      refine ⟨2997821755863379604587943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994191348969012278901181 2997821755863379604587943)
                      ·
                        rfl

theorem cell23_5838237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_5838237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838237 prefixEnd_5838237 := by exact prefixLift 5838237
  have htrace : WordTrace (prefixWord ++ tailWord_5838237) baseStart_5838237 baseEnd_5838237 := by
    simpa [prefixWord, tailWord_5838237, baseEnd_5838237] using wordTrace_append hprefix tailTrace_5838237
  have hstable : (prefixWord ++ tailWord_5838237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838237).length < 2 ^ (prefixWord ++ tailWord_5838237).sum := by decide
  have hdescent : baseEnd_5838237 < baseStart_5838237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838247 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5838247 : Nat := 118140960795 + 5838247 * 2 ^ 59
def prefixEnd_5838247 : Nat := 4983230072969 + 3 ^ 40 * 5838247 * 2
def baseEnd_5838247 : Nat := 2997826890669924565462897

theorem tailTrace_5838247 : CollatzResearch.WordTrace tailWord_5838247 prefixEnd_5838247 2997826890669924565462897 := by
  unfold tailWord_5838247
  simp only [CollatzResearch.WordTrace]
  refine ⟨212938361680035687050064995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141958907786690458033376663 212938361680035687050064995)
  ·
    refine ⟨319407542520053530575097493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212938361680035687050064995 319407542520053530575097493)
    ·
      refine ⟨14972228555627509245707695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 319407542520053530575097493 14972228555627509245707695)
      ·
        refine ⟨22458342833441263868561543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14972228555627509245707695 22458342833441263868561543)
        ·
          refine ⟨33687514250161895802842315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22458342833441263868561543 33687514250161895802842315)
          ·
            refine ⟨50531271375242843704263473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33687514250161895802842315 50531271375242843704263473)
            ·
              refine ⟨37898453531432132778197605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50531271375242843704263473 37898453531432132778197605)
              ·
                refine ⟨7105960037143524895912051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37898453531432132778197605 7105960037143524895912051)
                ·
                  refine ⟨10658940055715287343868077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105960037143524895912051 10658940055715287343868077)
                  ·
                    refine ⟨3997102520893232753950529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10658940055715287343868077 3997102520893232753950529)
                    ·
                      refine ⟨2997826890669924565462897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997102520893232753950529 2997826890669924565462897)
                      ·
                        rfl

theorem cell23_5838247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5838247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838247 prefixEnd_5838247 := by exact prefixLift 5838247
  have htrace : WordTrace (prefixWord ++ tailWord_5838247) baseStart_5838247 baseEnd_5838247 := by
    simpa [prefixWord, tailWord_5838247, baseEnd_5838247] using wordTrace_append hprefix tailTrace_5838247
  have hstable : (prefixWord ++ tailWord_5838247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838247).length < 2 ^ (prefixWord ++ tailWord_5838247).sum := by decide
  have hdescent : baseEnd_5838247 < baseStart_5838247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838294 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_5838294 : Nat := 118140960795 + 5838294 * 2 ^ 59
def prefixEnd_5838294 : Nat := 4983230072969 + 3 ^ 40 * 5838294 * 2
def baseEnd_5838294 : Nat := 2997851024260685881575181

theorem tailTrace_5838294 : CollatzResearch.WordTrace tailWord_5838294 prefixEnd_5838294 2997851024260685881575181 := by
  unfold tailWord_5838294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308754744429088379814121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141960050607243609384683957 13308754744429088379814121)
  ·
    refine ⟨9981566058321816284860591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13308754744429088379814121 9981566058321816284860591)
    ·
      refine ⟨14972349087482724427290887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9981566058321816284860591 14972349087482724427290887)
      ·
        refine ⟨22458523631224086640936331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14972349087482724427290887 22458523631224086640936331)
        ·
          refine ⟨33687785446836129961404497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22458523631224086640936331 33687785446836129961404497)
          ·
            refine ⟨25265839085127097471053373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33687785446836129961404497 25265839085127097471053373)
            ·
              refine ⟨9474689656922661551645015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25265839085127097471053373 9474689656922661551645015)
              ·
                refine ⟨14212034485383992327467523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9474689656922661551645015 14212034485383992327467523)
                ·
                  refine ⟨21318051728075988491201285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14212034485383992327467523 21318051728075988491201285)
                  ·
                    refine ⟨3997134699014247842100241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21318051728075988491201285 3997134699014247842100241)
                    ·
                      refine ⟨2997851024260685881575181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997134699014247842100241 2997851024260685881575181)
                      ·
                        rfl

theorem cell23_5838294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_5838294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838294 prefixEnd_5838294 := by exact prefixLift 5838294
  have htrace : WordTrace (prefixWord ++ tailWord_5838294) baseStart_5838294 baseEnd_5838294 := by
    simpa [prefixWord, tailWord_5838294, baseEnd_5838294] using wordTrace_append hprefix tailTrace_5838294
  have hstable : (prefixWord ++ tailWord_5838294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838294).length < 2 ^ (prefixWord ++ tailWord_5838294).sum := by decide
  have hdescent : baseEnd_5838294 < baseStart_5838294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838334 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_5838334 : Nat := 118140960795 + 5838334 * 2 ^ 59
def prefixEnd_5838334 : Nat := 4983230072969 + 3 ^ 40 * 5838334 * 2
def baseEnd_5838334 : Nat := 333096840387429525008333

theorem tailTrace_5838334 : CollatzResearch.WordTrace tailWord_5838334 prefixEnd_5838334 333096840387429525008333 := by
  unfold tailWord_5838334
  simp only [CollatzResearch.WordTrace]
  refine ⟨26617691853840062613560257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141961023220480333938988037 26617691853840062613560257)
  ·
    refine ⟨19963268890380046960170193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26617691853840062613560257 19963268890380046960170193)
    ·
      refine ⟨14972451667785035220127645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19963268890380046960170193 14972451667785035220127645)
      ·
        refine ⟨5614669375419388207547867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14972451667785035220127645 5614669375419388207547867)
        ·
          refine ⟨8422004063129082311321801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614669375419388207547867 8422004063129082311321801)
          ·
            refine ⟨6316503047346811733491351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8422004063129082311321801 6316503047346811733491351)
            ·
              refine ⟨9474754571020217600237027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316503047346811733491351 9474754571020217600237027)
              ·
                refine ⟨14212131856530326400355541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9474754571020217600237027 14212131856530326400355541)
                ·
                  refine ⟨333096840387429525008333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14212131856530326400355541 333096840387429525008333)
                  ·
                    rfl

theorem cell23_5838334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_5838334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838334 prefixEnd_5838334 := by exact prefixLift 5838334
  have htrace : WordTrace (prefixWord ++ tailWord_5838334) baseStart_5838334 baseEnd_5838334 := by
    simpa [prefixWord, tailWord_5838334, baseEnd_5838334] using wordTrace_append hprefix tailTrace_5838334
  have hstable : (prefixWord ++ tailWord_5838334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838334).length < 2 ^ (prefixWord ++ tailWord_5838334).sum := by decide
  have hdescent : baseEnd_5838334 < baseStart_5838334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838370 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_5838370 : Nat := 118140960795 + 5838370 * 2 ^ 59
def prefixEnd_5838370 : Nat := 4983230072969 + 3 ^ 40 * 5838370 * 2
def baseEnd_5838370 : Nat := 2997890048790427584224831

theorem tailTrace_5838370 : CollatzResearch.WordTrace tailWord_5838370 prefixEnd_5838370 2997890048790427584224831 := by
  unfold tailWord_5838370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53235711964647519764198141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141961898572393386037861709 53235711964647519764198141)
  ·
    refine ⟨19963391986742819911574303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53235711964647519764198141 19963391986742819911574303)
    ·
      refine ⟨29945087980114229867361455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19963391986742819911574303 29945087980114229867361455)
      ·
        refine ⟨44917631970171344801042183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29945087980114229867361455 44917631970171344801042183)
        ·
          refine ⟨67376447955257017201563275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44917631970171344801042183 67376447955257017201563275)
          ·
            refine ⟨101064671932885525802344913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67376447955257017201563275 101064671932885525802344913)
            ·
              refine ⟨75798503949664144351758685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101064671932885525802344913 75798503949664144351758685)
              ·
                refine ⟨28424438981124054131909507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75798503949664144351758685 28424438981124054131909507)
                ·
                  refine ⟨42636658471686081197864261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28424438981124054131909507 42636658471686081197864261)
                  ·
                    refine ⟨7994373463441140224599549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42636658471686081197864261 7994373463441140224599549)
                    ·
                      refine ⟨2997890048790427584224831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994373463441140224599549 2997890048790427584224831)
                      ·
                        rfl

theorem cell23_5838370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_5838370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838370 prefixEnd_5838370 := by exact prefixLift 5838370
  have htrace : WordTrace (prefixWord ++ tailWord_5838370) baseStart_5838370 baseEnd_5838370 := by
    simpa [prefixWord, tailWord_5838370, baseEnd_5838370] using wordTrace_append hprefix tailTrace_5838370
  have hstable : (prefixWord ++ tailWord_5838370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838370).length < 2 ^ (prefixWord ++ tailWord_5838370).sum := by decide
  have hdescent : baseEnd_5838370 < baseStart_5838370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838417 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_5838417 : Nat := 118140960795 + 5838417 * 2 ^ 59
def prefixEnd_5838417 : Nat := 4983230072969 + 3 ^ 40 * 5838417 * 2
def baseEnd_5838417 : Nat := 2997914182381188900337115

theorem tailTrace_5838417 : CollatzResearch.WordTrace tailWord_5838417 prefixEnd_5838417 2997914182381188900337115 := by
  unfold tailWord_5838417
  simp only [CollatzResearch.WordTrace]
  refine ⟨212944562089419806083753505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141963041392946537389169003 212944562089419806083753505)
  ·
    refine ⟨159708421567064854562815129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212944562089419806083753505 159708421567064854562815129)
    ·
      refine ⟨119781316175298640922111347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159708421567064854562815129 119781316175298640922111347)
      ·
        refine ⟨179671974262947961383167021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119781316175298640922111347 179671974262947961383167021)
        ·
          refine ⟨67376990348605485518687633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179671974262947961383167021 67376990348605485518687633)
          ·
            refine ⟨50532742761454114139015725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67376990348605485518687633 50532742761454114139015725)
            ·
              refine ⟨18949778535545292802130897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50532742761454114139015725 18949778535545292802130897)
              ·
                refine ⟨14212333901658969601598173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18949778535545292802130897 14212333901658969601598173)
                ·
                  refine ⟨5329625213122113600599315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14212333901658969601598173 5329625213122113600599315)
                  ·
                    refine ⟨7994437819683170400898973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329625213122113600599315 7994437819683170400898973)
                    ·
                      refine ⟨2997914182381188900337115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994437819683170400898973 2997914182381188900337115)
                      ·
                        rfl

theorem cell23_5838417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_5838417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838417 prefixEnd_5838417 := by exact prefixLift 5838417
  have htrace : WordTrace (prefixWord ++ tailWord_5838417) baseStart_5838417 baseEnd_5838417 := by
    simpa [prefixWord, tailWord_5838417, baseEnd_5838417] using wordTrace_append hprefix tailTrace_5838417
  have hstable : (prefixWord ++ tailWord_5838417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838417).length < 2 ^ (prefixWord ++ tailWord_5838417).sum := by decide
  have hdescent : baseEnd_5838417 < baseStart_5838417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838420 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5838420 : Nat := 118140960795 + 5838420 * 2 ^ 59
def prefixEnd_5838420 : Nat := 4983230072969 + 3 ^ 40 * 5838420 * 2
def baseEnd_5838420 : Nat := 999305240941050796199867

theorem tailTrace_5838420 : CollatzResearch.WordTrace tailWord_5838420 prefixEnd_5838420 999305240941050796199867 := by
  unfold tailWord_5838420
  simp only [CollatzResearch.WordTrace]
  refine ⟨106472335754204468798056357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141963114338939291730741809 106472335754204468798056357)
  ·
    refine ⟨19963562953913337899635567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106472335754204468798056357 19963562953913337899635567)
    ·
      refine ⟨29945344430870006849453351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19963562953913337899635567 29945344430870006849453351)
      ·
        refine ⟨44918016646305010274180027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29945344430870006849453351 44918016646305010274180027)
        ·
          refine ⟨67377024969457515411270041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44918016646305010274180027 67377024969457515411270041)
          ·
            refine ⟨50532768727093136558452531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67377024969457515411270041 50532768727093136558452531)
            ·
              refine ⟨75799153090639704837678797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50532768727093136558452531 75799153090639704837678797)
              ·
                refine ⟨28424682408989889314129549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75799153090639704837678797 28424682408989889314129549)
                ·
                  refine ⟨10659255903371208492798581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28424682408989889314129549 10659255903371208492798581)
                  ·
                    refine ⟨999305240941050796199867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10659255903371208492798581 999305240941050796199867)
                    ·
                      rfl

theorem cell23_5838420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5838420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838420 prefixEnd_5838420 := by exact prefixLift 5838420
  have htrace : WordTrace (prefixWord ++ tailWord_5838420) baseStart_5838420 baseEnd_5838420 := by
    simpa [prefixWord, tailWord_5838420, baseEnd_5838420] using wordTrace_append hprefix tailTrace_5838420
  have hstable : (prefixWord ++ tailWord_5838420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838420).length < 2 ^ (prefixWord ++ tailWord_5838420).sum := by decide
  have hdescent : baseEnd_5838420 < baseStart_5838420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838437 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_5838437 : Nat := 118140960795 + 5838437 * 2 ^ 59
def prefixEnd_5838437 : Nat := 4983230072969 + 3 ^ 40 * 5838437 * 2
def baseEnd_5838437 : Nat := 999308150664759607362341

theorem tailTrace_5838437 : CollatzResearch.WordTrace tailWord_5838437 prefixEnd_5838437 999308150664759607362341 := by
  unfold tailWord_5838437
  simp only [CollatzResearch.WordTrace]
  refine ⟨212945291549347349499481565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141963527699564899666321043 212945291549347349499481565)
  ·
    refine ⟨79854484331005256062305587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212945291549347349499481565 79854484331005256062305587)
    ·
      refine ⟨119781726496507884093458381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79854484331005256062305587 119781726496507884093458381)
      ·
        refine ⟨44918147436190456535046893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119781726496507884093458381 44918147436190456535046893)
        ·
          refine ⟨16844305288571421200642585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44918147436190456535046893 16844305288571421200642585)
          ·
            refine ⟨12633228966428565900481939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16844305288571421200642585 12633228966428565900481939)
            ·
              refine ⟨18949843449642848850722909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633228966428565900481939 18949843449642848850722909)
              ·
                refine ⟨7106191293616068319021091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18949843449642848850722909 7106191293616068319021091)
                ·
                  refine ⟨10659286940424102478531637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7106191293616068319021091 10659286940424102478531637)
                  ·
                    refine ⟨999308150664759607362341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10659286940424102478531637 999308150664759607362341)
                    ·
                      rfl

theorem cell23_5838437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_5838437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838437 prefixEnd_5838437 := by exact prefixLift 5838437
  have htrace : WordTrace (prefixWord ++ tailWord_5838437) baseStart_5838437 baseEnd_5838437 := by
    simpa [prefixWord, tailWord_5838437, baseEnd_5838437] using wordTrace_append hprefix tailTrace_5838437
  have hstable : (prefixWord ++ tailWord_5838437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838437).length < 2 ^ (prefixWord ++ tailWord_5838437).sum := by decide
  have hdescent : baseEnd_5838437 < baseStart_5838437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838474 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_5838474 : Nat := 118140960795 + 5838474 * 2 ^ 59
def prefixEnd_5838474 : Nat := 4983230072969 + 3 ^ 40 * 5838474 * 2
def baseEnd_5838474 : Nat := 2997943450778495177324353

theorem tailTrace_5838474 : CollatzResearch.WordTrace tailWord_5838474 prefixEnd_5838474 2997943450778495177324353 := by
  unfold tailWord_5838474
  simp only [CollatzResearch.WordTrace]
  refine ⟨53236660262553326204644619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141964427366808869879052317 53236660262553326204644619)
  ·
    refine ⟨79854990393829989306966929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53236660262553326204644619 79854990393829989306966929)
    ·
      refine ⟨59891242795372491980225197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79854990393829989306966929 59891242795372491980225197)
      ·
        refine ⟨22459216048264684492584449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59891242795372491980225197 22459216048264684492584449)
        ·
          refine ⟨16844412036198513369438337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22459216048264684492584449 16844412036198513369438337)
          ·
            refine ⟨12633309027148885027078753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16844412036198513369438337 12633309027148885027078753)
            ·
              refine ⟨9474981770361663770309065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12633309027148885027078753 9474981770361663770309065)
              ·
                refine ⟨7106236327771247827731799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9474981770361663770309065 7106236327771247827731799)
                ·
                  refine ⟨10659354491656871741597699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7106236327771247827731799 10659354491656871741597699)
                  ·
                    refine ⟨15989031737485307612396549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10659354491656871741597699 15989031737485307612396549)
                    ·
                      refine ⟨2997943450778495177324353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15989031737485307612396549 2997943450778495177324353)
                      ·
                        rfl

theorem cell23_5838474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_5838474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838474 prefixEnd_5838474 := by exact prefixLift 5838474
  have htrace : WordTrace (prefixWord ++ tailWord_5838474) baseStart_5838474 baseEnd_5838474 := by
    simpa [prefixWord, tailWord_5838474, baseEnd_5838474] using wordTrace_append hprefix tailTrace_5838474
  have hstable : (prefixWord ++ tailWord_5838474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838474).length < 2 ^ (prefixWord ++ tailWord_5838474).sum := by decide
  have hdescent : baseEnd_5838474 < baseStart_5838474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838494 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5838494 : Nat := 118140960795 + 5838494 * 2 ^ 59
def prefixEnd_5838494 : Nat := 4983230072969 + 3 ^ 40 * 5838494 * 2
def baseEnd_5838494 : Nat := 2997953720391585099074261

theorem tailTrace_5838494 : CollatzResearch.WordTrace tailWord_5838494 prefixEnd_5838494 2997953720391585099074261 := by
  unfold tailWord_5838494
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618421313767606029288317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141964913673427232156204357 26618421313767606029288317)
  ·
    refine ⟨9981907992662852260983119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26618421313767606029288317 9981907992662852260983119)
    ·
      refine ⟨14972861988994278391474679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9981907992662852260983119 14972861988994278391474679)
      ·
        refine ⟨22459292983491417587212019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14972861988994278391474679 22459292983491417587212019)
        ·
          refine ⟨33688939475237126380818029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22459292983491417587212019 33688939475237126380818029)
          ·
            refine ⟨12633352303213922392806761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33688939475237126380818029 12633352303213922392806761)
            ·
              refine ⟨9475014227410441794605071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12633352303213922392806761 9475014227410441794605071)
              ·
                refine ⟨14212521341115662691907607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9475014227410441794605071 14212521341115662691907607)
                ·
                  refine ⟨21318782011673494037861411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14212521341115662691907607 21318782011673494037861411)
                  ·
                    refine ⟨31978173017510241056792117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21318782011673494037861411 31978173017510241056792117)
                    ·
                      refine ⟨2997953720391585099074261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31978173017510241056792117 2997953720391585099074261)
                      ·
                        rfl

theorem cell23_5838494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5838494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838494 prefixEnd_5838494 := by exact prefixLift 5838494
  have htrace : WordTrace (prefixWord ++ tailWord_5838494) baseStart_5838494 baseEnd_5838494 := by
    simpa [prefixWord, tailWord_5838494, baseEnd_5838494] using wordTrace_append hprefix tailTrace_5838494
  have hstable : (prefixWord ++ tailWord_5838494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838494).length < 2 ^ (prefixWord ++ tailWord_5838494).sum := by decide
  have hdescent : baseEnd_5838494 < baseStart_5838494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838518 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5838518 : Nat := 118140960795 + 5838518 * 2 ^ 59
def prefixEnd_5838518 : Nat := 4983230072969 + 3 ^ 40 * 5838518 * 2
def baseEnd_5838518 : Nat := 999322014642431001724717

theorem tailTrace_5838518 : CollatzResearch.WordTrace tailWord_5838518 prefixEnd_5838518 999322014642431001724717 := by
  unfold tailWord_5838518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309265366378368770823763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141965497241369266888786805 13309265366378368770823763)
  ·
    refine ⟨19963898049567553156235645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13309265366378368770823763 19963898049567553156235645)
    ·
      refine ⟨7486461768587832433588367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19963898049567553156235645 7486461768587832433588367)
      ·
        refine ⟨11229692652881748650382551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486461768587832433588367 11229692652881748650382551)
        ·
          refine ⟨16844538979322622975573827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11229692652881748650382551 16844538979322622975573827)
          ·
            refine ⟨25266808468983934463360741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16844538979322622975573827 25266808468983934463360741)
            ·
              refine ⟨4737526587934487711880139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25266808468983934463360741 4737526587934487711880139)
              ·
                refine ⟨7106289881901731567820209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737526587934487711880139 7106289881901731567820209)
                ·
                  refine ⟨5329717411426298675865157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7106289881901731567820209 5329717411426298675865157)
                  ·
                    refine ⟨999322014642431001724717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329717411426298675865157 999322014642431001724717)
                    ·
                      rfl

theorem cell23_5838518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5838518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838518 prefixEnd_5838518 := by exact prefixLift 5838518
  have htrace : WordTrace (prefixWord ++ tailWord_5838518) baseStart_5838518 baseEnd_5838518 := by
    simpa [prefixWord, tailWord_5838518, baseEnd_5838518] using wordTrace_append hprefix tailTrace_5838518
  have hstable : (prefixWord ++ tailWord_5838518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838518).length < 2 ^ (prefixWord ++ tailWord_5838518).sum := by decide
  have hdescent : baseEnd_5838518 < baseStart_5838518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838541 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5838541 : Nat := 118140960795 + 5838541 * 2 ^ 59
def prefixEnd_5838541 : Nat := 4983230072969 + 3 ^ 40 * 5838541 * 2
def baseEnd_5838541 : Nat := 2997977853982346415186545

theorem tailTrace_5838541 : CollatzResearch.WordTrace tailWord_5838541 prefixEnd_5838541 2997977853982346415186545 := by
  unfold tailWord_5838541
  simp only [CollatzResearch.WordTrace]
  refine ⟨212949084740970575261267477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141966056493980383507511651 212949084740970575261267477)
  ·
    refine ⟨9981988347232995715371913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212949084740970575261267477 9981988347232995715371913)
    ·
      refine ⟨7486491260424746786528935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9981988347232995715371913 7486491260424746786528935)
      ·
        refine ⟨11229736890637120179793403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486491260424746786528935 11229736890637120179793403)
        ·
          refine ⟨16844605335955680269690105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11229736890637120179793403 16844605335955680269690105)
          ·
            refine ⟨12633454001966760202267579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16844605335955680269690105 12633454001966760202267579)
            ·
              refine ⟨18950181002950140303401369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633454001966760202267579 18950181002950140303401369)
              ·
                refine ⟨14212635752212605227551027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18950181002950140303401369 14212635752212605227551027)
                ·
                  refine ⟨21318953628318907841326541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14212635752212605227551027 21318953628318907841326541)
                  ·
                    refine ⟨7994607610619590440497453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21318953628318907841326541 7994607610619590440497453)
                    ·
                      refine ⟨2997977853982346415186545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994607610619590440497453 2997977853982346415186545)
                      ·
                        rfl

theorem cell23_5838541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5838541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838541 prefixEnd_5838541 := by exact prefixLift 5838541
  have htrace : WordTrace (prefixWord ++ tailWord_5838541) baseStart_5838541 baseEnd_5838541 := by
    simpa [prefixWord, tailWord_5838541, baseEnd_5838541] using wordTrace_append hprefix tailTrace_5838541
  have hstable : (prefixWord ++ tailWord_5838541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838541).length < 2 ^ (prefixWord ++ tailWord_5838541).sum := by decide
  have hdescent : baseEnd_5838541 < baseStart_5838541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838551 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_5838551 : Nat := 118140960795 + 5838551 * 2 ^ 59
def prefixEnd_5838551 : Nat := 4983230072969 + 3 ^ 40 * 5838551 * 2
def baseEnd_5838551 : Nat := 2997982988788891376061499

theorem tailTrace_5838551 : CollatzResearch.WordTrace tailWord_5838551 prefixEnd_5838551 2997982988788891376061499 := by
  unfold tailWord_5838551
  simp only [CollatzResearch.WordTrace]
  refine ⟨212949449470934346969131507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141966299647289564646087671 212949449470934346969131507)
  ·
    refine ⟨319424174206401520453697261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212949449470934346969131507 319424174206401520453697261)
    ·
      refine ⟨119784065327400570170136473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319424174206401520453697261 119784065327400570170136473)
      ·
        refine ⟨89838048995550427627602355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119784065327400570170136473 89838048995550427627602355)
        ·
          refine ⟨134757073493325641441403533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89838048995550427627602355 134757073493325641441403533)
          ·
            refine ⟨50533902559997115540526325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134757073493325641441403533 50533902559997115540526325)
            ·
              refine ⟨4737553364999729581924343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50533902559997115540526325 4737553364999729581924343)
              ·
                refine ⟨7106330047499594372886515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737553364999729581924343 7106330047499594372886515)
                ·
                  refine ⟨10659495071249391559329773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7106330047499594372886515 10659495071249391559329773)
                  ·
                    refine ⟨3997310651718521834748665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10659495071249391559329773 3997310651718521834748665)
                    ·
                      refine ⟨2997982988788891376061499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997310651718521834748665 2997982988788891376061499)
                      ·
                        rfl

theorem cell23_5838551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_5838551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838551 prefixEnd_5838551 := by exact prefixLift 5838551
  have htrace : WordTrace (prefixWord ++ tailWord_5838551) baseStart_5838551 baseEnd_5838551 := by
    simpa [prefixWord, tailWord_5838551, baseEnd_5838551] using wordTrace_append hprefix tailTrace_5838551
  have hstable : (prefixWord ++ tailWord_5838551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838551).length < 2 ^ (prefixWord ++ tailWord_5838551).sum := by decide
  have hdescent : baseEnd_5838551 < baseStart_5838551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838577 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_5838577 : Nat := 118140960795 + 5838577 * 2 ^ 59
def prefixEnd_5838577 : Nat := 4983230072969 + 3 ^ 40 * 5838577 * 2
def baseEnd_5838577 : Nat := 2997996339285908274336379

theorem tailTrace_5838577 : CollatzResearch.WordTrace tailWord_5838577 prefixEnd_5838577 2997996339285908274336379 := by
  unfold tailWord_5838577
  simp only [CollatzResearch.WordTrace]
  refine ⟨212950397768840153409577985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141966931845893435606385323 212950397768840153409577985)
  ·
    refine ⟨159712798326630115057183489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212950397768840153409577985 159712798326630115057183489)
    ·
      refine ⟨119784598744972586292887617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159712798326630115057183489 119784598744972586292887617)
      ·
        refine ⟨89838449058729439719665713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119784598744972586292887617 89838449058729439719665713)
        ·
          refine ⟨67378836794047079789749285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89838449058729439719665713 67378836794047079789749285)
          ·
            refine ⟨12633531898883827460577991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67378836794047079789749285 12633531898883827460577991)
            ·
              refine ⟨18950297848325741190866987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633531898883827460577991 18950297848325741190866987)
              ·
                refine ⟨28425446772488611786300481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18950297848325741190866987 28425446772488611786300481)
                ·
                  refine ⟨21319085079366458839725361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28425446772488611786300481 21319085079366458839725361)
                  ·
                    refine ⟨15989313809524844129794021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21319085079366458839725361 15989313809524844129794021)
                    ·
                      refine ⟨2997996339285908274336379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15989313809524844129794021 2997996339285908274336379)
                      ·
                        rfl

theorem cell23_5838577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_5838577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838577 prefixEnd_5838577 := by exact prefixLift 5838577
  have htrace : WordTrace (prefixWord ++ tailWord_5838577) baseStart_5838577 baseEnd_5838577 := by
    simpa [prefixWord, tailWord_5838577, baseEnd_5838577] using wordTrace_append hprefix tailTrace_5838577
  have hstable : (prefixWord ++ tailWord_5838577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838577).length < 2 ^ (prefixWord ++ tailWord_5838577).sum := by decide
  have hdescent : baseEnd_5838577 < baseStart_5838577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838607 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 7, 2]
def baseStart_5838607 : Nat := 118140960795 + 5838607 * 2 ^ 59
def prefixEnd_5838607 : Nat := 4983230072969 + 3 ^ 40 * 5838607 * 2
def baseEnd_5838607 : Nat := 2998011743705543156961241

theorem tailTrace_5838607 : CollatzResearch.WordTrace tailWord_5838607 prefixEnd_5838607 2998011743705543156961241 := by
  unfold tailWord_5838607
  simp only [CollatzResearch.WordTrace]
  refine ⟨212951491958731468533170075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141967661305820979022113383 212951491958731468533170075)
  ·
    refine ⟨319427237938097202799755113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212951491958731468533170075 319427237938097202799755113)
    ·
      refine ⟨239570428453572902099816335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319427237938097202799755113 239570428453572902099816335)
      ·
        refine ⟨359355642680359353149724503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239570428453572902099816335 359355642680359353149724503)
        ·
          refine ⟨539033464020539029724586755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359355642680359353149724503 539033464020539029724586755)
          ·
            refine ⟨808550196030808544586880133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539033464020539029724586755 808550196030808544586880133)
            ·
              refine ⟨151603161755776602110040025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 808550196030808544586880133 151603161755776602110040025)
              ·
                refine ⟨113702371316832451582530019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151603161755776602110040025 113702371316832451582530019)
                ·
                  refine ⟨170553556975248677373795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113702371316832451582530019 170553556975248677373795029)
                  ·
                    refine ⟨3997348991607390875948321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170553556975248677373795029 3997348991607390875948321)
                    ·
                      refine ⟨2998011743705543156961241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997348991607390875948321 2998011743705543156961241)
                      ·
                        rfl

theorem cell23_5838607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 7, 2].length) (baseStart_5838607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838607 prefixEnd_5838607 := by exact prefixLift 5838607
  have htrace : WordTrace (prefixWord ++ tailWord_5838607) baseStart_5838607 baseEnd_5838607 := by
    simpa [prefixWord, tailWord_5838607, baseEnd_5838607] using wordTrace_append hprefix tailTrace_5838607
  have hstable : (prefixWord ++ tailWord_5838607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838607).length < 2 ^ (prefixWord ++ tailWord_5838607).sum := by decide
  have hdescent : baseEnd_5838607 < baseStart_5838607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838647 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 5, 4]
def baseStart_5838647 : Nat := 118140960795 + 5838647 * 2 ^ 59
def prefixEnd_5838647 : Nat := 4983230072969 + 3 ^ 40 * 5838647 * 2
def baseEnd_5838647 : Nat := 999344094310574333487019

theorem tailTrace_5838647 : CollatzResearch.WordTrace tailWord_5838647 prefixEnd_5838647 999344094310574333487019 := by
  unfold tailWord_5838647
  simp only [CollatzResearch.WordTrace]
  refine ⟨212952950878586555364626195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141968633919057703576417463 212952950878586555364626195)
  ·
    refine ⟨319429426317879833046939293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212952950878586555364626195 319429426317879833046939293)
    ·
      refine ⟨119786034869204937392602235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319429426317879833046939293 119786034869204937392602235)
      ·
        refine ⟨179679052303807406088903353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119786034869204937392602235 179679052303807406088903353)
        ·
          refine ⟨134759289227855554566677515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179679052303807406088903353 134759289227855554566677515)
          ·
            refine ⟨202138933841783331850016273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134759289227855554566677515 202138933841783331850016273)
            ·
              refine ⟨151604200381337498887512205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202138933841783331850016273 151604200381337498887512205)
              ·
                refine ⟨56851575143001562082817077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151604200381337498887512205 56851575143001562082817077)
                ·
                  refine ⟨5329835169656396445264101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56851575143001562082817077 5329835169656396445264101)
                  ·
                    refine ⟨999344094310574333487019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5329835169656396445264101 999344094310574333487019)
                    ·
                      rfl

theorem cell23_5838647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_5838647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838647 prefixEnd_5838647 := by exact prefixLift 5838647
  have htrace : WordTrace (prefixWord ++ tailWord_5838647) baseStart_5838647 baseEnd_5838647 := by
    simpa [prefixWord, tailWord_5838647, baseEnd_5838647] using wordTrace_append hprefix tailTrace_5838647
  have hstable : (prefixWord ++ tailWord_5838647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838647).length < 2 ^ (prefixWord ++ tailWord_5838647).sum := by decide
  have hdescent : baseEnd_5838647 < baseStart_5838647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838654 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5838654 : Nat := 118140960795 + 5838654 * 2 ^ 59
def prefixEnd_5838654 : Nat := 4983230072969 + 3 ^ 40 * 5838654 * 2
def baseEnd_5838654 : Nat := 2998035877296304473073525

theorem tailTrace_5838654 : CollatzResearch.WordTrace tailWord_5838654 prefixEnd_5838654 2998035877296304473073525 := by
  unfold tailWord_5838654
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619150773695149445016377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141968804126374130373420677 26619150773695149445016377)
  ·
    refine ⟨19964363080271362083762283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26619150773695149445016377 19964363080271362083762283)
    ·
      refine ⟨29946544620407043125643425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19964363080271362083762283 29946544620407043125643425)
      ·
        refine ⟨22459908465305282344232569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29946544620407043125643425 22459908465305282344232569)
        ·
          refine ⟨16844931348978961758174427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22459908465305282344232569 16844931348978961758174427)
          ·
            refine ⟨25267397023468442637261641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16844931348978961758174427 25267397023468442637261641)
            ·
              refine ⟨18950547767601331977946231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25267397023468442637261641 18950547767601331977946231)
              ·
                refine ⟨28425821651401997966919347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18950547767601331977946231 28425821651401997966919347)
                ·
                  refine ⟨42638732477102996950379021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28425821651401997966919347 42638732477102996950379021)
                  ·
                    refine ⟨15989524678913623856392133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42638732477102996950379021 15989524678913623856392133)
                    ·
                      refine ⟨2998035877296304473073525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15989524678913623856392133 2998035877296304473073525)
                      ·
                        rfl

theorem cell23_5838654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5838654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838654 prefixEnd_5838654 := by exact prefixLift 5838654
  have htrace : WordTrace (prefixWord ++ tailWord_5838654) baseStart_5838654 baseEnd_5838654 := by
    simpa [prefixWord, tailWord_5838654, baseEnd_5838654] using wordTrace_append hprefix tailTrace_5838654
  have hstable : (prefixWord ++ tailWord_5838654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838654).length < 2 ^ (prefixWord ++ tailWord_5838654).sum := by decide
  have hdescent : baseEnd_5838654 < baseStart_5838654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838674 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_5838674 : Nat := 118140960795 + 5838674 * 2 ^ 59
def prefixEnd_5838674 : Nat := 4983230072969 + 3 ^ 40 * 5838674 * 2
def baseEnd_5838674 : Nat := 2998046146909394394823433

theorem tailTrace_5838674 : CollatzResearch.WordTrace tailWord_5838674 prefixEnd_5838674 2998046146909394394823433 := by
  unfold tailWord_5838674
  simp only [CollatzResearch.WordTrace]
  refine ⟨53238483912372184743964769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141969290432992492650572717 53238483912372184743964769)
  ·
    refine ⟨39928862934279138557973577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53238483912372184743964769 39928862934279138557973577)
    ·
      refine ⟨29946647200709353918480183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39928862934279138557973577 29946647200709353918480183)
      ·
        refine ⟨44919970801064030877720275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29946647200709353918480183 44919970801064030877720275)
        ·
          refine ⟨67379956201596046316580413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44919970801064030877720275 67379956201596046316580413)
          ·
            refine ⟨25267483575598517368717655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67379956201596046316580413 25267483575598517368717655)
            ·
              refine ⟨37901225363397776053076483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25267483575598517368717655 37901225363397776053076483)
              ·
                refine ⟨56851838045096664079614725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37901225363397776053076483 56851838045096664079614725)
                ·
                  refine ⟨10659719633455624514927761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56851838045096664079614725 10659719633455624514927761)
                  ·
                    refine ⟨7994789725091718386195821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10659719633455624514927761 7994789725091718386195821)
                    ·
                      refine ⟨2998046146909394394823433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994789725091718386195821 2998046146909394394823433)
                      ·
                        rfl

theorem cell23_5838674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_5838674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838674 prefixEnd_5838674 := by exact prefixLift 5838674
  have htrace : WordTrace (prefixWord ++ tailWord_5838674) baseStart_5838674 baseEnd_5838674 := by
    simpa [prefixWord, tailWord_5838674, baseEnd_5838674] using wordTrace_append hprefix tailTrace_5838674
  have hstable : (prefixWord ++ tailWord_5838674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838674).length < 2 ^ (prefixWord ++ tailWord_5838674).sum := by decide
  have hdescent : baseEnd_5838674 < baseStart_5838674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838677 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 8]
def baseStart_5838677 : Nat := 118140960795 + 5838677 * 2 ^ 59
def prefixEnd_5838677 : Nat := 4983230072969 + 3 ^ 40 * 5838677 * 2
def baseEnd_5838677 : Nat := 333116409705706431453991

theorem tailTrace_5838677 : CollatzResearch.WordTrace tailWord_5838677 prefixEnd_5838677 333116409705706431453991 := by
  unfold tailWord_5838677
  simp only [CollatzResearch.WordTrace]
  refine ⟨212954045068477870488218285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141969363378985246992145523 212954045068477870488218285)
  ·
    refine ⟨79857766900679201433081857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212954045068477870488218285 79857766900679201433081857)
    ·
      refine ⟨59893325175509401074811393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79857766900679201433081857 59893325175509401074811393)
      ·
        refine ⟨44919993881632050806108545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59893325175509401074811393 44919993881632050806108545)
        ·
          refine ⟨33689995411224038104581409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44919993881632050806108545 33689995411224038104581409)
          ·
            refine ⟨25267496558418028578436057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33689995411224038104581409 25267496558418028578436057)
            ·
              refine ⟨18950622418813521433827043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25267496558418028578436057 18950622418813521433827043)
              ·
                refine ⟨28425933628220282150740565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18950622418813521433827043 28425933628220282150740565)
                ·
                  refine ⟨333116409705706431453991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28425933628220282150740565 333116409705706431453991)
                  ·
                    rfl

theorem cell23_5838677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_5838677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838677 prefixEnd_5838677 := by exact prefixLift 5838677
  have htrace : WordTrace (prefixWord ++ tailWord_5838677) baseStart_5838677 baseEnd_5838677 := by
    simpa [prefixWord, tailWord_5838677, baseEnd_5838677] using wordTrace_append hprefix tailTrace_5838677
  have hstable : (prefixWord ++ tailWord_5838677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838677).length < 2 ^ (prefixWord ++ tailWord_5838677).sum := by decide
  have hdescent : baseEnd_5838677 < baseStart_5838677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838704 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3]
def baseStart_5838704 : Nat := 118140960795 + 5838704 * 2 ^ 59
def prefixEnd_5838704 : Nat := 4983230072969 + 3 ^ 40 * 5838704 * 2
def baseEnd_5838704 : Nat := 2998061551329029277448295

theorem tailTrace_5838704 : CollatzResearch.WordTrace tailWord_5838704 prefixEnd_5838704 2998061551329029277448295 := by
  unfold tailWord_5838704
  simp only [CollatzResearch.WordTrace]
  refine ⟨106477514919690027049725583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141970019892920036066300777 106477514919690027049725583)
  ·
    refine ⟨159716272379535040574588375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106477514919690027049725583 159716272379535040574588375)
    ·
      refine ⟨239574408569302560861882563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159716272379535040574588375 239574408569302560861882563)
      ·
        refine ⟨359361612853953841292823845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239574408569302560861882563 359361612853953841292823845)
        ·
          refine ⟨67380302410116345242404471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359361612853953841292823845 67380302410116345242404471)
          ·
            refine ⟨101070453615174517863606707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67380302410116345242404471 101070453615174517863606707)
            ·
              refine ⟨151605680422761776795410061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101070453615174517863606707 151605680422761776795410061)
              ·
                refine ⟨56852130158535666298278773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151605680422761776795410061 56852130158535666298278773)
                ·
                  refine ⟨5329887202362718715463635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56852130158535666298278773 5329887202362718715463635)
                  ·
                    refine ⟨7994830803544078073195453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329887202362718715463635 7994830803544078073195453)
                    ·
                      refine ⟨2998061551329029277448295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994830803544078073195453 2998061551329029277448295)
                      ·
                        rfl

theorem cell23_5838704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_5838704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838704 prefixEnd_5838704 := by exact prefixLift 5838704
  have htrace : WordTrace (prefixWord ++ tailWord_5838704) baseStart_5838704 baseEnd_5838704 := by
    simpa [prefixWord, tailWord_5838704, baseEnd_5838704] using wordTrace_append hprefix tailTrace_5838704
  have hstable : (prefixWord ++ tailWord_5838704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838704).length < 2 ^ (prefixWord ++ tailWord_5838704).sum := by decide
  have hdescent : baseEnd_5838704 < baseStart_5838704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838714 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_5838714 : Nat := 118140960795 + 5838714 * 2 ^ 59
def prefixEnd_5838714 : Nat := 4983230072969 + 3 ^ 40 * 5838714 * 2
def baseEnd_5838714 : Nat := 2998066686135574238323249

theorem tailTrace_5838714 : CollatzResearch.WordTrace tailWord_5838714 prefixEnd_5838714 2998066686135574238323249 := by
  unfold tailWord_5838714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53238848642335956451828799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141970263046229217204876797 53238848642335956451828799)
  ·
    refine ⟨79858272963503934677743199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53238848642335956451828799 79858272963503934677743199)
    ·
      refine ⟨119787409445255902016614799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79858272963503934677743199 119787409445255902016614799)
      ·
        refine ⟨179681114167883853024922199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119787409445255902016614799 179681114167883853024922199)
        ·
          refine ⟨269521671251825779537383299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179681114167883853024922199 269521671251825779537383299)
          ·
            refine ⟨404282506877738669306074949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269521671251825779537383299 404282506877738669306074949)
            ·
              refine ⟨75802970039576000494889053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404282506877738669306074949 75802970039576000494889053)
              ·
                refine ⟨28426113764841000185583395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75802970039576000494889053 28426113764841000185583395)
                ·
                  refine ⟨42639170647261500278375093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28426113764841000185583395 42639170647261500278375093)
                  ·
                    refine ⟨3997422248180765651097665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42639170647261500278375093 3997422248180765651097665)
                    ·
                      refine ⟨2998066686135574238323249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997422248180765651097665 2998066686135574238323249)
                      ·
                        rfl

theorem cell23_5838714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_5838714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838714 prefixEnd_5838714 := by exact prefixLift 5838714
  have htrace : WordTrace (prefixWord ++ tailWord_5838714) baseStart_5838714 baseEnd_5838714 := by
    simpa [prefixWord, tailWord_5838714, baseEnd_5838714] using wordTrace_append hprefix tailTrace_5838714
  have hstable : (prefixWord ++ tailWord_5838714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838714).length < 2 ^ (prefixWord ++ tailWord_5838714).sum := by decide
  have hdescent : baseEnd_5838714 < baseStart_5838714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838724 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_5838724 : Nat := 118140960795 + 5838724 * 2 ^ 59
def prefixEnd_5838724 : Nat := 4983230072969 + 3 ^ 40 * 5838724 * 2
def baseEnd_5838724 : Nat := 999357273647373066399401

theorem tailTrace_5838724 : CollatzResearch.WordTrace tailWord_5838724 prefixEnd_5838724 999357273647373066399401 := by
  unfold tailWord_5838724
  simp only [CollatzResearch.WordTrace]
  refine ⟨106477879649653798757589613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141970506199538398343452817 106477879649653798757589613)
  ·
    refine ⟨39929204868620174534096105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106477879649653798757589613 39929204868620174534096105)
    ·
      refine ⟨29946903651465130900572079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39929204868620174534096105 29946903651465130900572079)
      ·
        refine ⟨44920355477197696350858119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29946903651465130900572079 44920355477197696350858119)
        ·
          refine ⟨67380533215796544526287179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44920355477197696350858119 67380533215796544526287179)
          ·
            refine ⟨101070799823694816789430769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67380533215796544526287179 101070799823694816789430769)
            ·
              refine ⟨75803099867771112592073077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101070799823694816789430769 75803099867771112592073077)
              ·
                refine ⟨7106540612603541805506851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75803099867771112592073077 7106540612603541805506851)
                ·
                  refine ⟨10659810918905312708260277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7106540612603541805506851 10659810918905312708260277)
                  ·
                    refine ⟨999357273647373066399401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10659810918905312708260277 999357273647373066399401)
                    ·
                      rfl

theorem cell23_5838724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_5838724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838724 prefixEnd_5838724 := by exact prefixLift 5838724
  have htrace : WordTrace (prefixWord ++ tailWord_5838724) baseStart_5838724 baseEnd_5838724 := by
    simpa [prefixWord, tailWord_5838724, baseEnd_5838724] using wordTrace_append hprefix tailTrace_5838724
  have hstable : (prefixWord ++ tailWord_5838724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838724).length < 2 ^ (prefixWord ++ tailWord_5838724).sum := by decide
  have hdescent : baseEnd_5838724 < baseStart_5838724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838757 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_5838757 : Nat := 118140960795 + 5838757 * 2 ^ 59
def prefixEnd_5838757 : Nat := 4983230072969 + 3 ^ 40 * 5838757 * 2
def baseEnd_5838757 : Nat := 2998088765803717570085551

theorem tailTrace_5838757 : CollatzResearch.WordTrace tailWord_5838757 prefixEnd_5838757 2998088765803717570085551 := by
  unfold tailWord_5838757
  simp only [CollatzResearch.WordTrace]
  refine ⟨212956962908188044151130525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141971308605458696100753683 212956962908188044151130525)
  ·
    refine ⟨79858861090570516556673947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212956962908188044151130525 79858861090570516556673947)
    ·
      refine ⟨119788291635855774835010921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79858861090570516556673947 119788291635855774835010921)
      ·
        refine ⟨89841218726891831126258191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119788291635855774835010921 89841218726891831126258191)
        ·
          refine ⟨134761828090337746689387287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89841218726891831126258191 134761828090337746689387287)
          ·
            refine ⟨202142742135506620034080931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134761828090337746689387287 202142742135506620034080931)
            ·
              refine ⟨303214113203259930051121397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202142742135506620034080931 303214113203259930051121397)
              ·
                refine ⟨28426323112805618442292631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303214113203259930051121397 28426323112805618442292631)
                ·
                  refine ⟨42639484669208427663438947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28426323112805618442292631 42639484669208427663438947)
                  ·
                    refine ⟨63959227003812641495158421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42639484669208427663438947 63959227003812641495158421)
                    ·
                      refine ⟨2998088765803717570085551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63959227003812641495158421 2998088765803717570085551)
                      ·
                        rfl

theorem cell23_5838757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_5838757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838757 prefixEnd_5838757 := by exact prefixLift 5838757
  have htrace : WordTrace (prefixWord ++ tailWord_5838757) baseStart_5838757 baseEnd_5838757 := by
    simpa [prefixWord, tailWord_5838757, baseEnd_5838757] using wordTrace_append hprefix tailTrace_5838757
  have hstable : (prefixWord ++ tailWord_5838757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838757).length < 2 ^ (prefixWord ++ tailWord_5838757).sum := by decide
  have hdescent : baseEnd_5838757 < baseStart_5838757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838794 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_5838794 : Nat := 118140960795 + 5838794 * 2 ^ 59
def prefixEnd_5838794 : Nat := 4983230072969 + 3 ^ 40 * 5838794 * 2
def baseEnd_5838794 : Nat := 2998107764587933925322881

theorem tailTrace_5838794 : CollatzResearch.WordTrace tailWord_5838794 prefixEnd_5838794 2998107764587933925322881 := by
  unfold tailWord_5838794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53239578102263499867556859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141972208272702666313484957 53239578102263499867556859)
  ·
    refine ⟨79859367153395249801335289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53239578102263499867556859 79859367153395249801335289)
    ·
      refine ⟨59894525365046437351001467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79859367153395249801335289 59894525365046437351001467)
      ·
        refine ⟨89841788047569656026502201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59894525365046437351001467 89841788047569656026502201)
        ·
          refine ⟨67381341035677242019876651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89841788047569656026502201 67381341035677242019876651)
          ·
            refine ⟨101072011553515863029814977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67381341035677242019876651 101072011553515863029814977)
            ·
              refine ⟨75804008665136897272361233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101072011553515863029814977 75804008665136897272361233)
              ·
                refine ⟨56853006498852672954270925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75804008665136897272361233 56853006498852672954270925)
                ·
                  refine ⟨21319877437069752357851597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56853006498852672954270925 21319877437069752357851597)
                  ·
                    refine ⟨7994954038901157134194349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21319877437069752357851597 7994954038901157134194349)
                    ·
                      refine ⟨2998107764587933925322881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7994954038901157134194349 2998107764587933925322881)
                      ·
                        rfl

theorem cell23_5838794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_5838794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838794 prefixEnd_5838794 := by exact prefixLift 5838794
  have htrace : WordTrace (prefixWord ++ tailWord_5838794) baseStart_5838794 baseEnd_5838794 := by
    simpa [prefixWord, tailWord_5838794, baseEnd_5838794] using wordTrace_append hprefix tailTrace_5838794
  have hstable : (prefixWord ++ tailWord_5838794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838794).length < 2 ^ (prefixWord ++ tailWord_5838794).sum := by decide
  have hdescent : baseEnd_5838794 < baseStart_5838794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838812 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5838812 : Nat := 118140960795 + 5838812 * 2 ^ 59
def prefixEnd_5838812 : Nat := 4983230072969 + 3 ^ 40 * 5838812 * 2
def baseEnd_5838812 : Nat := 2998117007239714854897799

theorem tailTrace_5838812 : CollatzResearch.WordTrace tailWord_5838812 prefixEnd_5838812 2998117007239714854897799 := by
  unfold tailWord_5838812
  simp only [CollatzResearch.WordTrace]
  refine ⟨106479484461494394272191345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141972645948659192362921793 106479484461494394272191345)
  ·
    refine ⟨79859613346120795704143509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106479484461494394272191345 79859613346120795704143509)
    ·
      refine ⟨3743419375599412298631727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79859613346120795704143509 3743419375599412298631727)
      ·
        refine ⟨5615129063399118447947591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743419375599412298631727 5615129063399118447947591)
        ·
          refine ⟨8422693595098677671921387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615129063399118447947591 8422693595098677671921387)
          ·
            refine ⟨12634040392648016507882081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8422693595098677671921387 12634040392648016507882081)
            ·
              refine ⟨9475530294486012380911561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12634040392648016507882081 9475530294486012380911561)
              ·
                refine ⟨7106647720864509285683671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9475530294486012380911561 7106647720864509285683671)
                ·
                  refine ⟨10659971581296763928525507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7106647720864509285683671 10659971581296763928525507)
                  ·
                    refine ⟨15989957371945145892788261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10659971581296763928525507 15989957371945145892788261)
                    ·
                      refine ⟨2998117007239714854897799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15989957371945145892788261 2998117007239714854897799)
                      ·
                        rfl

theorem cell23_5838812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5838812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838812 prefixEnd_5838812 := by exact prefixLift 5838812
  have htrace : WordTrace (prefixWord ++ tailWord_5838812) baseStart_5838812 baseEnd_5838812 := by
    simpa [prefixWord, tailWord_5838812, baseEnd_5838812] using wordTrace_append hprefix tailTrace_5838812
  have hstable : (prefixWord ++ tailWord_5838812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838812).length < 2 ^ (prefixWord ++ tailWord_5838812).sum := by decide
  have hdescent : baseEnd_5838812 < baseStart_5838812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838827 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 8]
def baseStart_5838827 : Nat := 118140960795 + 5838827 * 2 ^ 59
def prefixEnd_5838827 : Nat := 4983230072969 + 3 ^ 40 * 5838827 * 2
def baseEnd_5838827 : Nat := 999374903149844098736743

theorem tailTrace_5838827 : CollatzResearch.WordTrace tailWord_5838827 prefixEnd_5838827 999374903149844098736743 := by
  unfold tailWord_5838827
  simp only [CollatzResearch.WordTrace]
  refine ⟨212959516017934446106178735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141973010678622964070785823 212959516017934446106178735)
  ·
    refine ⟨319439274026901669159268103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212959516017934446106178735 319439274026901669159268103)
    ·
      refine ⟨479158911040352503738902155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319439274026901669159268103 479158911040352503738902155)
      ·
        refine ⟨718738366560528755608353233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479158911040352503738902155 718738366560528755608353233)
        ·
          refine ⟨539053774920396566706264925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718738366560528755608353233 539053774920396566706264925)
          ·
            refine ⟨202145165595148712514849347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539053774920396566706264925 202145165595148712514849347)
            ·
              refine ⟨303217748392723068772274021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202145165595148712514849347 303217748392723068772274021)
              ·
                refine ⟨56853327823635575394801379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303217748392723068772274021 56853327823635575394801379)
                ·
                  refine ⟨85279991735453363092202069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56853327823635575394801379 85279991735453363092202069)
                  ·
                    refine ⟨999374903149844098736743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85279991735453363092202069 999374903149844098736743)
                    ·
                      rfl

theorem cell23_5838827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_5838827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838827 prefixEnd_5838827 := by exact prefixLift 5838827
  have htrace : WordTrace (prefixWord ++ tailWord_5838827) baseStart_5838827 baseEnd_5838827 := by
    simpa [prefixWord, tailWord_5838827, baseEnd_5838827] using wordTrace_append hprefix tailTrace_5838827
  have hstable : (prefixWord ++ tailWord_5838827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838827).length < 2 ^ (prefixWord ++ tailWord_5838827).sum := by decide
  have hdescent : baseEnd_5838827 < baseStart_5838827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838902 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_5838902 : Nat := 118140960795 + 5838902 * 2 ^ 59
def prefixEnd_5838902 : Nat := 4983230072969 + 3 ^ 40 * 5838902 * 2
def baseEnd_5838902 : Nat := 2998163220498619502772385

theorem tailTrace_5838902 : CollatzResearch.WordTrace tailWord_5838902 prefixEnd_5838902 2998163220498619502772385 := by
  unfold tailWord_5838902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310140718291420869697435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141974834328441822610105973 13310140718291420869697435)
  ·
    refine ⟨19965211077437131304546153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13310140718291420869697435 19965211077437131304546153)
    ·
      refine ⟨14973908308077848478409615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19965211077437131304546153 14973908308077848478409615)
      ·
        refine ⟨22460862462116772717614423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14973908308077848478409615 22460862462116772717614423)
        ·
          refine ⟨33691293693175159076421635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22460862462116772717614423 33691293693175159076421635)
          ·
            refine ⟨50536940539762738614632453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33691293693175159076421635 50536940539762738614632453)
            ·
              refine ⟨9475676351205513490243585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50536940539762738614632453 9475676351205513490243585)
              ·
                refine ⟨7106757263404135117682689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9475676351205513490243585 7106757263404135117682689)
                ·
                  refine ⟨5330067947553101338262017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7106757263404135117682689 5330067947553101338262017)
                  ·
                    refine ⟨3997550960664826003696513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330067947553101338262017 3997550960664826003696513)
                    ·
                      refine ⟨2998163220498619502772385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997550960664826003696513 2998163220498619502772385)
                      ·
                        rfl

theorem cell23_5838902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_5838902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838902 prefixEnd_5838902 := by exact prefixLift 5838902
  have htrace : WordTrace (prefixWord ++ tailWord_5838902) baseStart_5838902 baseEnd_5838902 := by
    simpa [prefixWord, tailWord_5838902, baseEnd_5838902] using wordTrace_append hprefix tailTrace_5838902
  have hstable : (prefixWord ++ tailWord_5838902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838902).length < 2 ^ (prefixWord ++ tailWord_5838902).sum := by decide
  have hdescent : baseEnd_5838902 < baseStart_5838902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838911 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 5, 2]
def baseStart_5838911 : Nat := 118140960795 + 5838911 * 2 ^ 59
def prefixEnd_5838911 : Nat := 4983230072969 + 3 ^ 40 * 5838911 * 2
def baseEnd_5838911 : Nat := 2998167841824509967559843

theorem tailTrace_5838911 : CollatzResearch.WordTrace tailWord_5838911 prefixEnd_5838911 2998167841824509967559843 := by
  unfold tailWord_5838911
  simp only [CollatzResearch.WordTrace]
  refine ⟨212962579749630128452236587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141975053166420085634824391 212962579749630128452236587)
  ·
    refine ⟨319443869624445192678354881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212962579749630128452236587 319443869624445192678354881)
    ·
      refine ⟨239582902218333894508766161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319443869624445192678354881 239582902218333894508766161)
      ·
        refine ⟨179687176663750420881574621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239582902218333894508766161 179687176663750420881574621)
        ·
          refine ⟨67382691248906407830590483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179687176663750420881574621 67382691248906407830590483)
          ·
            refine ⟨101074036873359611745885725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67382691248906407830590483 101074036873359611745885725)
            ·
              refine ⟨37902763827509854404707147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101074036873359611745885725 37902763827509854404707147)
              ·
                refine ⟨56854145741264781607060721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37902763827509854404707147 56854145741264781607060721)
                ·
                  refine ⟨42640609305948586205295541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56854145741264781607060721 42640609305948586205295541)
                  ·
                    refine ⟨3997557122432679956746457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42640609305948586205295541 3997557122432679956746457)
                    ·
                      refine ⟨2998167841824509967559843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997557122432679956746457 2998167841824509967559843)
                      ·
                        rfl

theorem cell23_5838911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_5838911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838911 prefixEnd_5838911 := by exact prefixLift 5838911
  have htrace : WordTrace (prefixWord ++ tailWord_5838911) baseStart_5838911 baseEnd_5838911 := by
    simpa [prefixWord, tailWord_5838911, baseEnd_5838911] using wordTrace_append hprefix tailTrace_5838911
  have hstable : (prefixWord ++ tailWord_5838911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838911).length < 2 ^ (prefixWord ++ tailWord_5838911).sum := by decide
  have hdescent : baseEnd_5838911 < baseStart_5838911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838951 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 5, 4]
def baseStart_5838951 : Nat := 118140960795 + 5838951 * 2 ^ 59
def prefixEnd_5838951 : Nat := 4983230072969 + 3 ^ 40 * 5838951 * 2
def baseEnd_5838951 : Nat := 999396127016896603686553

theorem tailTrace_5838951 : CollatzResearch.WordTrace tailWord_5838951 prefixEnd_5838951 999396127016896603686553 := by
  unfold tailWord_5838951
  simp only [CollatzResearch.WordTrace]
  refine ⟨212964038669485215283692707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141976025779656810189128471 212964038669485215283692707)
  ·
    refine ⟨319446058004227822925539061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212964038669485215283692707 319446058004227822925539061)
    ·
      refine ⟨29948067937896358399269287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319446058004227822925539061 29948067937896358399269287)
      ·
        refine ⟨44922101906844537598903931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29948067937896358399269287 44922101906844537598903931)
        ·
          refine ⟨67383152860266806398355897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44922101906844537598903931 67383152860266806398355897)
          ·
            refine ⟨50537364645200104798766923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67383152860266806398355897 50537364645200104798766923)
            ·
              refine ⟨75806046967800157198150385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50537364645200104798766923 75806046967800157198150385)
              ·
                refine ⟨56854535225850117898612789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75806046967800157198150385 56854535225850117898612789)
                ·
                  refine ⟨5330112677423448552994949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56854535225850117898612789 5330112677423448552994949)
                  ·
                    refine ⟨999396127016896603686553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330112677423448552994949 999396127016896603686553)
                    ·
                      rfl

theorem cell23_5838951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_5838951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838951 prefixEnd_5838951 := by exact prefixLift 5838951
  have htrace : WordTrace (prefixWord ++ tailWord_5838951) baseStart_5838951 baseEnd_5838951 := by
    simpa [prefixWord, tailWord_5838951, baseEnd_5838951] using wordTrace_append hprefix tailTrace_5838951
  have hstable : (prefixWord ++ tailWord_5838951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838951).length < 2 ^ (prefixWord ++ tailWord_5838951).sum := by decide
  have hdescent : baseEnd_5838951 < baseStart_5838951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838958 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5838958 : Nat := 118140960795 + 5838958 * 2 ^ 59
def prefixEnd_5838958 : Nat := 4983230072969 + 3 ^ 40 * 5838958 * 2
def baseEnd_5838958 : Nat := 2998191975415271283672127

theorem tailTrace_5838958 : CollatzResearch.WordTrace tailWord_5838958 prefixEnd_5838958 2998191975415271283672127 := by
  unfold tailWord_5838958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26620536747557481934899691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141976195986973236986131685 26620536747557481934899691)
  ·
    refine ⟨39930805121336222902349537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26620536747557481934899691 39930805121336222902349537)
    ·
      refine ⟨29948103841002167176762153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39930805121336222902349537 29948103841002167176762153)
      ·
        refine ⟨22461077880751625382571615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29948103841002167176762153 22461077880751625382571615)
        ·
          refine ⟨33691616821127438073857423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22461077880751625382571615 33691616821127438073857423)
          ·
            refine ⟨50537425231691157110786135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33691616821127438073857423 50537425231691157110786135)
            ·
              refine ⟨75806137847536735666179203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50537425231691157110786135 75806137847536735666179203)
              ·
                refine ⟨113709206771305103499268805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75806137847536735666179203 113709206771305103499268805)
                ·
                  refine ⟨21320476269619706906112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113709206771305103499268805 21320476269619706906112901)
                  ·
                    refine ⟨3997589300553695044896169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21320476269619706906112901 3997589300553695044896169)
                    ·
                      refine ⟨2998191975415271283672127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997589300553695044896169 2998191975415271283672127)
                      ·
                        rfl

theorem cell23_5838958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5838958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838958 prefixEnd_5838958 := by exact prefixLift 5838958
  have htrace : WordTrace (prefixWord ++ tailWord_5838958) baseStart_5838958 baseEnd_5838958 := by
    simpa [prefixWord, tailWord_5838958, baseEnd_5838958] using wordTrace_append hprefix tailTrace_5838958
  have hstable : (prefixWord ++ tailWord_5838958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838958).length < 2 ^ (prefixWord ++ tailWord_5838958).sum := by decide
  have hdescent : baseEnd_5838958 < baseStart_5838958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5838961 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_5838961 : Nat := 118140960795 + 5838961 * 2 ^ 59
def prefixEnd_5838961 : Nat := 4983230072969 + 3 ^ 40 * 5838961 * 2
def baseEnd_5838961 : Nat := 2998193515857234771934613

theorem tailTrace_5838961 : CollatzResearch.WordTrace tailWord_5838961 prefixEnd_5838961 2998193515857234771934613 := by
  unfold tailWord_5838961
  simp only [CollatzResearch.WordTrace]
  refine ⟨212964403399448986991556737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141976268932965991327704491 212964403399448986991556737)
  ·
    refine ⟨159723302549586740243667553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212964403399448986991556737 159723302549586740243667553)
    ·
      refine ⟨119792476912190055182750665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159723302549586740243667553 119792476912190055182750665)
      ·
        refine ⟨89844357684142541387062999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119792476912190055182750665 89844357684142541387062999)
        ·
          refine ⟨134766536526213812080594499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89844357684142541387062999 134766536526213812080594499)
          ·
            refine ⟨202149804789320718120891749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134766536526213812080594499 202149804789320718120891749)
            ·
              refine ⟨37903088397997634647667203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202149804789320718120891749 37903088397997634647667203)
              ·
                refine ⟨56854632596996451971500805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37903088397997634647667203 56854632596996451971500805)
                ·
                  refine ⟨10660243611936834744656401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56854632596996451971500805 10660243611936834744656401)
                  ·
                    refine ⟨7995182708952626058492301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10660243611936834744656401 7995182708952626058492301)
                    ·
                      refine ⟨2998193515857234771934613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7995182708952626058492301 2998193515857234771934613)
                      ·
                        rfl

theorem cell23_5838961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_5838961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5838961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5838961 prefixEnd_5838961 := by exact prefixLift 5838961
  have htrace : WordTrace (prefixWord ++ tailWord_5838961) baseStart_5838961 baseEnd_5838961 := by
    simpa [prefixWord, tailWord_5838961, baseEnd_5838961] using wordTrace_append hprefix tailTrace_5838961
  have hstable : (prefixWord ++ tailWord_5838961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5838961).length < 2 ^ (prefixWord ++ tailWord_5838961).sum := by decide
  have hdescent : baseEnd_5838961 < baseStart_5838961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5838961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839024 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_5839024 : Nat := 118140960795 + 5839024 * 2 ^ 59
def prefixEnd_5839024 : Nat := 4983230072969 + 3 ^ 40 * 5839024 * 2
def baseEnd_5839024 : Nat := 999408621712822675148941

theorem tailTrace_5839024 : CollatzResearch.WordTrace tailWord_5839024 prefixEnd_5839024 999408621712822675148941 := by
  unfold tailWord_5839024
  simp only [CollatzResearch.WordTrace]
  refine ⟨106483350599110374375550063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141977800798813832500733417 106483350599110374375550063)
  ·
    refine ⟨159725025898665561563325095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106483350599110374375550063 159725025898665561563325095)
    ·
      refine ⟨239587538847998342344987643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159725025898665561563325095 239587538847998342344987643)
      ·
        refine ⟨359381308271997513517481465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239587538847998342344987643 359381308271997513517481465)
        ·
          refine ⟨269535981203998135138111099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359381308271997513517481465 269535981203998135138111099)
          ·
            refine ⟨404303971805997202707166649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269535981203998135138111099 404303971805997202707166649)
            ·
              refine ⟨303227978854497902030374987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404303971805997202707166649 303227978854497902030374987)
              ·
                refine ⟨454841968281746853045562481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303227978854497902030374987 454841968281746853045562481)
                ·
                  refine ⟨341131476211310139784171861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454841968281746853045562481 341131476211310139784171861)
                  ·
                    refine ⟨999408621712822675148941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 341131476211310139784171861 999408621712822675148941)
                    ·
                      rfl

theorem cell23_5839024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_5839024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839024 prefixEnd_5839024 := by exact prefixLift 5839024
  have htrace : WordTrace (prefixWord ++ tailWord_5839024) baseStart_5839024 baseEnd_5839024 := by
    simpa [prefixWord, tailWord_5839024, baseEnd_5839024] using wordTrace_append hprefix tailTrace_5839024
  have hstable : (prefixWord ++ tailWord_5839024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839024).length < 2 ^ (prefixWord ++ tailWord_5839024).sum := by decide
  have hdescent : baseEnd_5839024 < baseStart_5839024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839058 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_5839058 : Nat := 118140960795 + 5839058 * 2 ^ 59
def prefixEnd_5839058 : Nat := 4983230072969 + 3 ^ 40 * 5839058 * 2
def baseEnd_5839058 : Nat := 999414441160240297473889

theorem tailTrace_5839058 : CollatzResearch.WordTrace tailWord_5839058 prefixEnd_5839058 999414441160240297473889 := by
  unfold tailWord_5839058
  simp only [CollatzResearch.WordTrace]
  refine ⟨53241985320024393139459457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141978627520065048371891885 53241985320024393139459457)
  ·
    refine ⟨39931488990018294854594593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53241985320024393139459457 39931488990018294854594593)
    ·
      refine ⟨29948616742513721140945945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39931488990018294854594593 29948616742513721140945945)
      ·
        refine ⟨22461462556885290855709459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29948616742513721140945945 22461462556885290855709459)
        ·
          refine ⟨33692193835327936283564189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22461462556885290855709459 33692193835327936283564189)
          ·
            refine ⟨12634572688247976106336571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33692193835327936283564189 12634572688247976106336571)
            ·
              refine ⟨18951859032371964159504857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12634572688247976106336571 18951859032371964159504857)
              ·
                refine ⟨14213894274278973119628643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18951859032371964159504857 14213894274278973119628643)
                ·
                  refine ⟨21320841411418459679442965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14213894274278973119628643 21320841411418459679442965)
                  ·
                    refine ⟨999414441160240297473889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21320841411418459679442965 999414441160240297473889)
                    ·
                      rfl

theorem cell23_5839058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_5839058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839058 prefixEnd_5839058 := by exact prefixLift 5839058
  have htrace : WordTrace (prefixWord ++ tailWord_5839058) baseStart_5839058 baseEnd_5839058 := by
    simpa [prefixWord, tailWord_5839058, baseEnd_5839058] using wordTrace_append hprefix tailTrace_5839058
  have hstable : (prefixWord ++ tailWord_5839058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839058).length < 2 ^ (prefixWord ++ tailWord_5839058).sum := by decide
  have hdescent : baseEnd_5839058 < baseStart_5839058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839098 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_5839098 : Nat := 118140960795 + 5839098 * 2 ^ 59
def prefixEnd_5839098 : Nat := 4983230072969 + 3 ^ 40 * 5839098 * 2
def baseEnd_5839098 : Nat := 2998263862706900735921483

theorem tailTrace_5839098 : CollatzResearch.WordTrace tailWord_5839098 prefixEnd_5839098 2998263862706900735921483 := by
  unfold tailWord_5839098
  simp only [CollatzResearch.WordTrace]
  refine ⟨53242350049988164847323487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141979600133301772926195965 53242350049988164847323487)
  ·
    refine ⟨79863525074982247270985231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53242350049988164847323487 79863525074982247270985231)
    ·
      refine ⟨119795287612473370906477847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79863525074982247270985231 119795287612473370906477847)
      ·
        refine ⟨179692931418710056359716771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119795287612473370906477847 179692931418710056359716771)
        ·
          refine ⟨269539397128065084539575157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179692931418710056359716771 269539397128065084539575157)
          ·
            refine ⟨25269318480756101675585171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 269539397128065084539575157 25269318480756101675585171)
            ·
              refine ⟨37903977721134152513377757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25269318480756101675585171 37903977721134152513377757)
              ·
                refine ⟨14213991645425307192516659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37903977721134152513377757 14213991645425307192516659)
                ·
                  refine ⟨21320987468137960788774989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14213991645425307192516659 21320987468137960788774989)
                  ·
                    refine ⟨7995370300551735295790621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21320987468137960788774989 7995370300551735295790621)
                    ·
                      refine ⟨2998263862706900735921483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7995370300551735295790621 2998263862706900735921483)
                      ·
                        rfl

theorem cell23_5839098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_5839098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839098 prefixEnd_5839098 := by exact prefixLift 5839098
  have htrace : WordTrace (prefixWord ++ tailWord_5839098) baseStart_5839098 baseEnd_5839098 := by
    simpa [prefixWord, tailWord_5839098, baseEnd_5839098] using wordTrace_append hprefix tailTrace_5839098
  have hstable : (prefixWord ++ tailWord_5839098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839098).length < 2 ^ (prefixWord ++ tailWord_5839098).sum := by decide
  have hdescent : baseEnd_5839098 < baseStart_5839098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839131 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 2, 6]
def baseStart_5839131 : Nat := 118140960795 + 5839131 * 2 ^ 59
def prefixEnd_5839131 : Nat := 4983230072969 + 3 ^ 40 * 5839131 * 2
def baseEnd_5839131 : Nat := 999426935856166368936277

theorem tailTrace_5839131 : CollatzResearch.WordTrace tailWord_5839131 prefixEnd_5839131 999426935856166368936277 := by
  unfold tailWord_5839131
  simp only [CollatzResearch.WordTrace]
  refine ⟨212970603808833106025245247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141980402539222070683496831 212970603808833106025245247)
  ·
    refine ⟨319455905713249659037867871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212970603808833106025245247 319455905713249659037867871)
    ·
      refine ⟨479183858569874488556801807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319455905713249659037867871 479183858569874488556801807)
      ·
        refine ⟨718775787854811732835202711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479183858569874488556801807 718775787854811732835202711)
        ·
          refine ⟨1078163681782217599252804067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718775787854811732835202711 1078163681782217599252804067)
          ·
            refine ⟨1617245522673326398879206101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078163681782217599252804067 1617245522673326398879206101)
            ·
              refine ⟨37904191937656087473731393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1617245522673326398879206101 37904191937656087473731393)
              ·
                refine ⟨28428143953242065605298545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37904191937656087473731393 28428143953242065605298545)
                ·
                  refine ⟨21321107964931549203973909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28428143953242065605298545 21321107964931549203973909)
                  ·
                    refine ⟨999426935856166368936277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21321107964931549203973909 999426935856166368936277)
                    ·
                      rfl

theorem cell23_5839131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_5839131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839131 prefixEnd_5839131 := by exact prefixLift 5839131
  have htrace : WordTrace (prefixWord ++ tailWord_5839131) baseStart_5839131 baseEnd_5839131 := by
    simpa [prefixWord, tailWord_5839131, baseEnd_5839131] using wordTrace_append hprefix tailTrace_5839131
  have hstable : (prefixWord ++ tailWord_5839131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839131).length < 2 ^ (prefixWord ++ tailWord_5839131).sum := by decide
  have hdescent : baseEnd_5839131 < baseStart_5839131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839149 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5839149 : Nat := 118140960795 + 5839149 * 2 ^ 59
def prefixEnd_5839149 : Nat := 4983230072969 + 3 ^ 40 * 5839149 * 2
def baseEnd_5839149 : Nat := 2998290050220280036383749

theorem tailTrace_5839149 : CollatzResearch.WordTrace tailWord_5839149 prefixEnd_5839149 2998290050220280036383749 := by
  unfold tailWord_5839149
  simp only [CollatzResearch.WordTrace]
  refine ⟨212971260322767895099400501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141980840215178596732933667 212971260322767895099400501)
  ·
    refine ⟨19966055655259490165568797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212971260322767895099400501 19966055655259490165568797)
    ·
      refine ⟨7487270870722308812088299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19966055655259490165568797 7487270870722308812088299)
      ·
        refine ⟨11230906306083463218132449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487270870722308812088299 11230906306083463218132449)
        ·
          refine ⟨8423179729562597413599337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11230906306083463218132449 8423179729562597413599337)
          ·
            refine ⟨6317384797171948060199503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423179729562597413599337 6317384797171948060199503)
            ·
              refine ⟨9476077195757922090299255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317384797171948060199503 9476077195757922090299255)
              ·
                refine ⟨14214115793636883135448883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9476077195757922090299255 14214115793636883135448883)
                ·
                  refine ⟨21321173690455324703173325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14214115793636883135448883 21321173690455324703173325)
                  ·
                    refine ⟨7995440133920746763689997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21321173690455324703173325 7995440133920746763689997)
                    ·
                      refine ⟨2998290050220280036383749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7995440133920746763689997 2998290050220280036383749)
                      ·
                        rfl

theorem cell23_5839149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5839149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839149 prefixEnd_5839149 := by exact prefixLift 5839149
  have htrace : WordTrace (prefixWord ++ tailWord_5839149) baseStart_5839149 baseEnd_5839149 := by
    simpa [prefixWord, tailWord_5839149, baseEnd_5839149] using wordTrace_append hprefix tailTrace_5839149
  have hstable : (prefixWord ++ tailWord_5839149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839149).length < 2 ^ (prefixWord ++ tailWord_5839149).sum := by decide
  have hdescent : baseEnd_5839149 < baseStart_5839149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839272 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5839272 : Nat := 118140960795 + 5839272 * 2 ^ 59
def prefixEnd_5839272 : Nat := 4983230072969 + 3 ^ 40 * 5839272 * 2
def baseEnd_5839272 : Nat := 999451069446927685048561

theorem tailTrace_5839272 : CollatzResearch.WordTrace tailWord_5839272 prefixEnd_5839272 999451069446927685048561 := by
  unfold tailWord_5839272
  simp only [CollatzResearch.WordTrace]
  refine ⟨106487873250661143553064035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141983831000881524737418713 106487873250661143553064035)
  ·
    refine ⟨159731809875991715329596053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106487873250661143553064035 159731809875991715329596053)
    ·
      refine ⟨7487428587937111656074815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159731809875991715329596053 7487428587937111656074815)
      ·
        refine ⟨11231142881905667484112223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487428587937111656074815 11231142881905667484112223)
        ·
          refine ⟨16846714322858501226168335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11231142881905667484112223 16846714322858501226168335)
          ·
            refine ⟨25270071484287751839252503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16846714322858501226168335 25270071484287751839252503)
            ·
              refine ⟨37905107226431627758878755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25270071484287751839252503 37905107226431627758878755)
              ·
                refine ⟨56857660839647441638318133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37905107226431627758878755 56857660839647441638318133)
                ·
                  refine ⟨5330405703716947653592325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56857660839647441638318133 5330405703716947653592325)
                  ·
                    refine ⟨999451069446927685048561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330405703716947653592325 999451069446927685048561)
                    ·
                      rfl

theorem cell23_5839272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5839272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839272 prefixEnd_5839272 := by exact prefixLift 5839272
  have htrace : WordTrace (prefixWord ++ tailWord_5839272) baseStart_5839272 baseEnd_5839272 := by
    simpa [prefixWord, tailWord_5839272, baseEnd_5839272] using wordTrace_append hprefix tailTrace_5839272
  have hstable : (prefixWord ++ tailWord_5839272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839272).length < 2 ^ (prefixWord ++ tailWord_5839272).sum := by decide
  have hdescent : baseEnd_5839272 < baseStart_5839272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839289 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 1, 4]
def baseStart_5839289 : Nat := 118140960795 + 5839289 * 2 ^ 59
def prefixEnd_5839289 : Nat := 4983230072969 + 3 ^ 40 * 5839289 * 2
def baseEnd_5839289 : Nat := 999453979170636496211035

theorem tailTrace_5839289 : CollatzResearch.WordTrace tailWord_5839289 prefixEnd_5839289 999453979170636496211035 := by
  unfold tailWord_5839289
  simp only [CollatzResearch.WordTrace]
  refine ⟨212976366542260699009496921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141984244361507132672997947 212976366542260699009496921)
  ·
    refine ⟨159732274906695524257122691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212976366542260699009496921 159732274906695524257122691)
    ·
      refine ⟨239598412360043286385684037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159732274906695524257122691 239598412360043286385684037)
      ·
        refine ⟨44924702317508116197315757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239598412360043286385684037 44924702317508116197315757)
        ·
          refine ⟨16846763369065543573993409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44924702317508116197315757 16846763369065543573993409)
          ·
            refine ⟨12635072526799157680495057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16846763369065543573993409 12635072526799157680495057)
            ·
              refine ⟨9476304395099368260371293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12635072526799157680495057 9476304395099368260371293)
              ·
                refine ⟨3553614148162263097639235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9476304395099368260371293 3553614148162263097639235)
                ·
                  refine ⟨5330421222243394646458853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553614148162263097639235 5330421222243394646458853)
                  ·
                    refine ⟨999453979170636496211035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330421222243394646458853 999453979170636496211035)
                    ·
                      rfl

theorem cell23_5839289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 4].length) (baseStart_5839289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839289 prefixEnd_5839289 := by exact prefixLift 5839289
  have htrace : WordTrace (prefixWord ++ tailWord_5839289) baseStart_5839289 baseEnd_5839289 := by
    simpa [prefixWord, tailWord_5839289, baseEnd_5839289] using wordTrace_append hprefix tailTrace_5839289
  have hstable : (prefixWord ++ tailWord_5839289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839289).length < 2 ^ (prefixWord ++ tailWord_5839289).sum := by decide
  have hdescent : baseEnd_5839289 < baseStart_5839289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839345 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_5839345 : Nat := 118140960795 + 5839345 * 2 ^ 59
def prefixEnd_5839345 : Nat := 4983230072969 + 3 ^ 40 * 5839345 * 2
def baseEnd_5839345 : Nat := 999463564142853756510949

theorem tailTrace_5839345 : CollatzResearch.WordTrace tailWord_5839345 prefixEnd_5839345 999463564142853756510949 := by
  unfold tailWord_5839345
  simp only [CollatzResearch.WordTrace]
  refine ⟨212978409030057820573535489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141985606020038547049023659 212978409030057820573535489)
  ·
    refine ⟨159733806772543365430151617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212978409030057820573535489 159733806772543365430151617)
    ·
      refine ⟨119800355079407524072613713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159733806772543365430151617 119800355079407524072613713)
      ·
        refine ⟨89850266309555643054460285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119800355079407524072613713 89850266309555643054460285)
        ·
          refine ⟨33693849866083366145422607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89850266309555643054460285 33693849866083366145422607)
          ·
            refine ⟨50540774799125049218133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33693849866083366145422607 50540774799125049218133911)
            ·
              refine ⟨75811162198687573827200867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50540774799125049218133911 75811162198687573827200867)
              ·
                refine ⟨113716743298031360740801301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75811162198687573827200867 113716743298031360740801301)
                ·
                  refine ⟨5330472342095220034725061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113716743298031360740801301 5330472342095220034725061)
                  ·
                    refine ⟨999463564142853756510949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330472342095220034725061 999463564142853756510949)
                    ·
                      rfl

theorem cell23_5839345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_5839345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839345 prefixEnd_5839345 := by exact prefixLift 5839345
  have htrace : WordTrace (prefixWord ++ tailWord_5839345) baseStart_5839345 baseEnd_5839345 := by
    simpa [prefixWord, tailWord_5839345, baseEnd_5839345] using wordTrace_append hprefix tailTrace_5839345
  have hstable : (prefixWord ++ tailWord_5839345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839345).length < 2 ^ (prefixWord ++ tailWord_5839345).sum := by decide
  have hdescent : baseEnd_5839345 < baseStart_5839345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839389 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_5839389 : Nat := 118140960795 + 5839389 * 2 ^ 59
def prefixEnd_5839389 : Nat := 4983230072969 + 3 ^ 40 * 5839389 * 2
def baseEnd_5839389 : Nat := 2998413285577359097382645

theorem tailTrace_5839389 : CollatzResearch.WordTrace tailWord_5839389 prefixEnd_5839389 2998413285577359097382645 := by
  unfold tailWord_5839389
  simp only [CollatzResearch.WordTrace]
  refine ⟨212980013841898416088137221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141986675894598944058758147 212980013841898416088137221)
  ·
    refine ⟨39933752595355953016525729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212980013841898416088137221 39933752595355953016525729)
    ·
      refine ⟨29950314446516964762394297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39933752595355953016525729 29950314446516964762394297)
      ·
        refine ⟨22462735834887723571795723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29950314446516964762394297 22462735834887723571795723)
        ·
          refine ⟨33694103752331585357693585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22462735834887723571795723 33694103752331585357693585)
          ·
            refine ⟨25270577814248689018270189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33694103752331585357693585 25270577814248689018270189)
            ·
              refine ⟨9476466680343258381851321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25270577814248689018270189 9476466680343258381851321)
              ·
                refine ⟨7107350010257443786388491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9476466680343258381851321 7107350010257443786388491)
                ·
                  refine ⟨10661025015386165679582737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107350010257443786388491 10661025015386165679582737)
                  ·
                    refine ⟨7995768761539624259687053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10661025015386165679582737 7995768761539624259687053)
                    ·
                      refine ⟨2998413285577359097382645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7995768761539624259687053 2998413285577359097382645)
                      ·
                        rfl

theorem cell23_5839389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_5839389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839389 prefixEnd_5839389 := by exact prefixLift 5839389
  have htrace : WordTrace (prefixWord ++ tailWord_5839389) baseStart_5839389 baseEnd_5839389 := by
    simpa [prefixWord, tailWord_5839389, baseEnd_5839389] using wordTrace_append hprefix tailTrace_5839389
  have hstable : (prefixWord ++ tailWord_5839389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839389).length < 2 ^ (prefixWord ++ tailWord_5839389).sum := by decide
  have hdescent : baseEnd_5839389 < baseStart_5839389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839402 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5839402 : Nat := 118140960795 + 5839402 * 2 ^ 59
def prefixEnd_5839402 : Nat := 4983230072969 + 3 ^ 40 * 5839402 * 2
def baseEnd_5839402 : Nat := 2998419960825867546520085

theorem tailTrace_5839402 : CollatzResearch.WordTrace tailWord_5839402 prefixEnd_5839402 2998419960825867546520085 := by
  unfold tailWord_5839402
  simp only [CollatzResearch.WordTrace]
  refine ⟨53245121997712829827090115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141986991993900879538906973 53245121997712829827090115)
  ·
    refine ⟨79867682996569244740635173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53245121997712829827090115 79867682996569244740635173)
    ·
      refine ⟨14975190561856733388869095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79867682996569244740635173 14975190561856733388869095)
      ·
        refine ⟨22462785842785100083303643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14975190561856733388869095 22462785842785100083303643)
        ·
          refine ⟨33694178764177650124955465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22462785842785100083303643 33694178764177650124955465)
          ·
            refine ⟨25270634073133237593716599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33694178764177650124955465 25270634073133237593716599)
            ·
              refine ⟨37905951109699856390574899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25270634073133237593716599 37905951109699856390574899)
              ·
                refine ⟨56858926664549784585862349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37905951109699856390574899 56858926664549784585862349)
                ·
                  refine ⟨21322097499206169219698381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56858926664549784585862349 21322097499206169219698381)
                  ·
                    refine ⟨7995786562202313457386893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21322097499206169219698381 7995786562202313457386893)
                    ·
                      refine ⟨2998419960825867546520085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7995786562202313457386893 2998419960825867546520085)
                      ·
                        rfl

theorem cell23_5839402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5839402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839402 prefixEnd_5839402 := by exact prefixLift 5839402
  have htrace : WordTrace (prefixWord ++ tailWord_5839402) baseStart_5839402 baseEnd_5839402 := by
    simpa [prefixWord, tailWord_5839402, baseEnd_5839402] using wordTrace_append hprefix tailTrace_5839402
  have hstable : (prefixWord ++ tailWord_5839402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839402).length < 2 ^ (prefixWord ++ tailWord_5839402).sum := by decide
  have hdescent : baseEnd_5839402 < baseStart_5839402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839406 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5839406 : Nat := 118140960795 + 5839406 * 2 ^ 59
def prefixEnd_5839406 : Nat := 4983230072969 + 3 ^ 40 * 5839406 * 2
def baseEnd_5839406 : Nat := 2998422014748485530870067

theorem tailTrace_5839406 : CollatzResearch.WordTrace tailWord_5839406 prefixEnd_5839406 2998422014748485530870067 := by
  unfold tailWord_5839406
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622579235354603498938259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141987089255224551994337381 26622579235354603498938259)
  ·
    refine ⟨39933868853031905248407389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26622579235354603498938259 39933868853031905248407389)
    ·
      refine ⟨14975200819886964468152771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39933868853031905248407389 14975200819886964468152771)
      ·
        refine ⟨22462801229830446702229157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14975200819886964468152771 22462801229830446702229157)
        ·
          refine ⟨4211775230593208756667967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22462801229830446702229157 4211775230593208756667967)
          ·
            refine ⟨6317662845889813135001951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211775230593208756667967 6317662845889813135001951)
            ·
              refine ⟨9476494268834719702502927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317662845889813135001951 9476494268834719702502927)
              ·
                refine ⟨14214741403252079553754391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9476494268834719702502927 14214741403252079553754391)
                ·
                  refine ⟨21322112104878119330631587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14214741403252079553754391 21322112104878119330631587)
                  ·
                    refine ⟨31983168157317178995947381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21322112104878119330631587 31983168157317178995947381)
                    ·
                      refine ⟨2998422014748485530870067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31983168157317178995947381 2998422014748485530870067)
                      ·
                        rfl

theorem cell23_5839406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5839406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839406 prefixEnd_5839406 := by exact prefixLift 5839406
  have htrace : WordTrace (prefixWord ++ tailWord_5839406) baseStart_5839406 baseEnd_5839406 := by
    simpa [prefixWord, tailWord_5839406, baseEnd_5839406] using wordTrace_append hprefix tailTrace_5839406
  have hstable : (prefixWord ++ tailWord_5839406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839406).length < 2 ^ (prefixWord ++ tailWord_5839406).sum := by decide
  have hdescent : baseEnd_5839406 < baseStart_5839406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839420 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_5839420 : Nat := 118140960795 + 5839420 * 2 ^ 59
def prefixEnd_5839420 : Nat := 4983230072969 + 3 ^ 40 * 5839420 * 2
def baseEnd_5839420 : Nat := 2998429203477648476095003

theorem tailTrace_5839420 : CollatzResearch.WordTrace tailWord_5839420 prefixEnd_5839420 2998429203477648476095003 := by
  unfold tailWord_5839420
  simp only [CollatzResearch.WordTrace]
  refine ⟨106490572252393054191257857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141987429669857405588343809 106490572252393054191257857)
  ·
    refine ⟨79867929189294790643443393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106490572252393054191257857 79867929189294790643443393)
    ·
      refine ⟨59900946891971092982582545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79867929189294790643443393 59900946891971092982582545)
      ·
        refine ⟨44925710168978319736936909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59900946891971092982582545 44925710168978319736936909)
        ·
          refine ⟨16847141313366869901351341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44925710168978319736936909 16847141313366869901351341)
          ·
            refine ⟨6317677992512576213006753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16847141313366869901351341 6317677992512576213006753)
            ·
              refine ⟨4738258494384432159755065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6317677992512576213006753 4738258494384432159755065)
              ·
                refine ⟨3553693870788324119816299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738258494384432159755065 3553693870788324119816299)
                ·
                  refine ⟨5330540806182486179724449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553693870788324119816299 5330540806182486179724449)
                  ·
                    refine ⟨3997905604636864634793337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330540806182486179724449 3997905604636864634793337)
                    ·
                      refine ⟨2998429203477648476095003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997905604636864634793337 2998429203477648476095003)
                      ·
                        rfl

theorem cell23_5839420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_5839420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839420 prefixEnd_5839420 := by exact prefixLift 5839420
  have htrace : WordTrace (prefixWord ++ tailWord_5839420) baseStart_5839420 baseEnd_5839420 := by
    simpa [prefixWord, tailWord_5839420, baseEnd_5839420] using wordTrace_append hprefix tailTrace_5839420
  have hstable : (prefixWord ++ tailWord_5839420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839420).length < 2 ^ (prefixWord ++ tailWord_5839420).sum := by decide
  have hdescent : baseEnd_5839420 < baseStart_5839420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839445 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5839445 : Nat := 118140960795 + 5839445 * 2 ^ 59
def prefixEnd_5839445 : Nat := 4983230072969 + 3 ^ 40 * 5839445 * 2
def baseEnd_5839445 : Nat := 2998442040494010878282387

theorem tailTrace_5839445 : CollatzResearch.WordTrace tailWord_5839445 prefixEnd_5839445 2998442040494010878282387 := by
  unfold tailWord_5839445
  simp only [CollatzResearch.WordTrace]
  refine ⟨212982056329695537652175789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141988037553130358434783859 212982056329695537652175789)
  ·
    refine ⟨79868271123635826619565921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212982056329695537652175789 79868271123635826619565921)
    ·
      refine ⟨59901203342726869964674441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79868271123635826619565921 59901203342726869964674441)
      ·
        refine ⟨44925902507045152473505831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59901203342726869964674441 44925902507045152473505831)
        ·
          refine ⟨67388853760567728710258747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44925902507045152473505831 67388853760567728710258747)
          ·
            refine ⟨101083280640851593065388121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67388853760567728710258747 101083280640851593065388121)
            ·
              refine ⟨75812460480638694799041091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101083280640851593065388121 75812460480638694799041091)
              ·
                refine ⟨113718690720958042198561637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75812460480638694799041091 113718690720958042198561637)
                ·
                  refine ⟨21322254510179632912230307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113718690720958042198561637 21322254510179632912230307)
                  ·
                    refine ⟨31983381765269449368345461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21322254510179632912230307 31983381765269449368345461)
                    ·
                      refine ⟨2998442040494010878282387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31983381765269449368345461 2998442040494010878282387)
                      ·
                        rfl

theorem cell23_5839445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5839445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839445 prefixEnd_5839445 := by exact prefixLift 5839445
  have htrace : WordTrace (prefixWord ++ tailWord_5839445) baseStart_5839445 baseEnd_5839445 := by
    simpa [prefixWord, tailWord_5839445, baseEnd_5839445] using wordTrace_append hprefix tailTrace_5839445
  have hstable : (prefixWord ++ tailWord_5839445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839445).length < 2 ^ (prefixWord ++ tailWord_5839445).sum := by decide
  have hdescent : baseEnd_5839445 < baseStart_5839445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839454 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5839454 : Nat := 118140960795 + 5839454 * 2 ^ 59
def prefixEnd_5839454 : Nat := 4983230072969 + 3 ^ 40 * 5839454 * 2
def baseEnd_5839454 : Nat := 2998446661819901343069847

theorem tailTrace_5839454 : CollatzResearch.WordTrace tailWord_5839454 prefixEnd_5839454 2998446661819901343069847 := by
  unfold tailWord_5839454
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622798073332866523656677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141988256391108621459502277 26622798073332866523656677)
  ·
    refine ⟨4991774638749912473185627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26622798073332866523656677 4991774638749912473185627)
    ·
      refine ⟨7487661958124868709778441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991774638749912473185627 7487661958124868709778441)
      ·
        refine ⟨5615746468593651532333831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487661958124868709778441 5615746468593651532333831)
        ·
          refine ⟨8423619702890477298500747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615746468593651532333831 8423619702890477298500747)
          ·
            refine ⟨12635429554335715947751121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8423619702890477298500747 12635429554335715947751121)
            ·
              refine ⟨9476572165751786960813341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12635429554335715947751121 9476572165751786960813341)
              ·
                refine ⟨3553714562156920110305003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9476572165751786960813341 3553714562156920110305003)
                ·
                  refine ⟨5330571843235380165457505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553714562156920110305003 5330571843235380165457505)
                  ·
                    refine ⟨3997928882426535124093129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330571843235380165457505 3997928882426535124093129)
                    ·
                      refine ⟨2998446661819901343069847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997928882426535124093129 2998446661819901343069847)
                      ·
                        rfl

theorem cell23_5839454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5839454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839454 prefixEnd_5839454 := by exact prefixLift 5839454
  have htrace : WordTrace (prefixWord ++ tailWord_5839454) baseStart_5839454 baseEnd_5839454 := by
    simpa [prefixWord, tailWord_5839454, baseEnd_5839454] using wordTrace_append hprefix tailTrace_5839454
  have hstable : (prefixWord ++ tailWord_5839454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839454).length < 2 ^ (prefixWord ++ tailWord_5839454).sum := by decide
  have hdescent : baseEnd_5839454 < baseStart_5839454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839459 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5839459 : Nat := 118140960795 + 5839459 * 2 ^ 59
def prefixEnd_5839459 : Nat := 4983230072969 + 3 ^ 40 * 5839459 * 2
def baseEnd_5839459 : Nat := 2998449229223173823507323

theorem tailTrace_5839459 : CollatzResearch.WordTrace tailWord_5839459 prefixEnd_5839459 2998449229223173823507323 := by
  unfold tailWord_5839459
  simp only [CollatzResearch.WordTrace]
  refine ⟨212982566951644818043185431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141988377967763212028790287 212982566951644818043185431)
  ·
    refine ⟨319473850427467227064778147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212982566951644818043185431 319473850427467227064778147)
    ·
      refine ⟨479210775641200840597167221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319473850427467227064778147 479210775641200840597167221)
      ·
        refine ⟨44926010216362578805984427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 479210775641200840597167221 44926010216362578805984427)
        ·
          refine ⟨67389015324543868208976641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44926010216362578805984427 67389015324543868208976641)
          ·
            refine ⟨50541761493407901156732481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67389015324543868208976641 50541761493407901156732481)
            ·
              refine ⟨37906321120055925867549361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50541761493407901156732481 37906321120055925867549361)
              ·
                refine ⟨28429740840041944400662021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37906321120055925867549361 28429740840041944400662021)
                ·
                  refine ⟨5330576407507864575124129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28429740840041944400662021 5330576407507864575124129)
                  ·
                    refine ⟨3997932305630898431343097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330576407507864575124129 3997932305630898431343097)
                    ·
                      refine ⟨2998449229223173823507323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997932305630898431343097 2998449229223173823507323)
                      ·
                        rfl

theorem cell23_5839459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5839459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839459 prefixEnd_5839459 := by exact prefixLift 5839459
  have htrace : WordTrace (prefixWord ++ tailWord_5839459) baseStart_5839459 baseEnd_5839459 := by
    simpa [prefixWord, tailWord_5839459, baseEnd_5839459] using wordTrace_append hprefix tailTrace_5839459
  have hstable : (prefixWord ++ tailWord_5839459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839459).length < 2 ^ (prefixWord ++ tailWord_5839459).sum := by decide
  have hdescent : baseEnd_5839459 < baseStart_5839459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839493 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_5839493 : Nat := 118140960795 + 5839493 * 2 ^ 59
def prefixEnd_5839493 : Nat := 4983230072969 + 3 ^ 40 * 5839493 * 2
def baseEnd_5839493 : Nat := 2998466687565426690482167

theorem tailTrace_5839493 : CollatzResearch.WordTrace tailWord_5839493 prefixEnd_5839493 2998466687565426690482167 := by
  unfold tailWord_5839493
  simp only [CollatzResearch.WordTrace]
  refine ⟨212983807033521641849923133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141989204689014427899948755 212983807033521641849923133)
  ·
    refine ⟨79868927637570615693721175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212983807033521641849923133 79868927637570615693721175)
    ·
      refine ⟨119803391456355923540581763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79868927637570615693721175 119803391456355923540581763)
      ·
        refine ⟨179705087184533885310872645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119803391456355923540581763 179705087184533885310872645)
        ·
          refine ⟨33694703847100103495788621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179705087184533885310872645 33694703847100103495788621)
          ·
            refine ⟨12635513942662538810920733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33694703847100103495788621 12635513942662538810920733)
            ·
              refine ⟨4738317728498452054095275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12635513942662538810920733 4738317728498452054095275)
              ·
                refine ⟨7107476592747678081142913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738317728498452054095275 7107476592747678081142913)
                ·
                  refine ⟨5330607444560758560857185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7107476592747678081142913 5330607444560758560857185)
                  ·
                    refine ⟨3997955583420568920642889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330607444560758560857185 3997955583420568920642889)
                    ·
                      refine ⟨2998466687565426690482167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3997955583420568920642889 2998466687565426690482167)
                      ·
                        rfl

theorem cell23_5839493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_5839493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839493 prefixEnd_5839493 := by exact prefixLift 5839493
  have htrace : WordTrace (prefixWord ++ tailWord_5839493) baseStart_5839493 baseEnd_5839493 := by
    simpa [prefixWord, tailWord_5839493, baseEnd_5839493] using wordTrace_append hprefix tailTrace_5839493
  have hstable : (prefixWord ++ tailWord_5839493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839493).length < 2 ^ (prefixWord ++ tailWord_5839493).sum := by decide
  have hdescent : baseEnd_5839493 < baseStart_5839493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839495 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 7]
def baseStart_5839495 : Nat := 118140960795 + 5839495 * 2 ^ 59
def prefixEnd_5839495 : Nat := 4983230072969 + 3 ^ 40 * 5839495 * 2
def baseEnd_5839495 : Nat := 999489238175578560885719

theorem tailTrace_5839495 : CollatzResearch.WordTrace tailWord_5839495 prefixEnd_5839495 999489238175578560885719 := by
  unfold tailWord_5839495
  simp only [CollatzResearch.WordTrace]
  refine ⟨212983879979514396191495939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141989253319676264127663959 212983879979514396191495939)
  ·
    refine ⟨319475819969271594287243909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212983879979514396191495939 319475819969271594287243909)
    ·
      refine ⟨59901716244238423928858233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319475819969271594287243909 59901716244238423928858233)
      ·
        refine ⟨44926287183178817946643675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59901716244238423928858233 44926287183178817946643675)
        ·
          refine ⟨67389430774768226919965513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44926287183178817946643675 67389430774768226919965513)
          ·
            refine ⟨50542073081076170189974135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67389430774768226919965513 50542073081076170189974135)
            ·
              refine ⟨75813109621614255284961203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50542073081076170189974135 75813109621614255284961203)
              ·
                refine ⟨113719664432421382927441805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75813109621614255284961203 113719664432421382927441805)
                ·
                  refine ⟨42644874162158018597790677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113719664432421382927441805 42644874162158018597790677)
                  ·
                    refine ⟨999489238175578560885719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42644874162158018597790677 999489238175578560885719)
                    ·
                      rfl

theorem cell23_5839495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_5839495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839495 prefixEnd_5839495 := by exact prefixLift 5839495
  have htrace : WordTrace (prefixWord ++ tailWord_5839495) baseStart_5839495 baseEnd_5839495 := by
    simpa [prefixWord, tailWord_5839495, baseEnd_5839495] using wordTrace_append hprefix tailTrace_5839495
  have hstable : (prefixWord ++ tailWord_5839495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839495).length < 2 ^ (prefixWord ++ tailWord_5839495).sum := by decide
  have hdescent : baseEnd_5839495 < baseStart_5839495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839512 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_5839512 : Nat := 118140960795 + 5839512 * 2 ^ 59
def prefixEnd_5839512 : Nat := 4983230072969 + 3 ^ 40 * 5839512 * 2
def baseEnd_5839512 : Nat := 999492147899287372048193

theorem tailTrace_5839512 : CollatzResearch.WordTrace tailWord_5839512 prefixEnd_5839512 999492147899287372048193 := by
  unfold tailWord_5839512
  simp only [CollatzResearch.WordTrace]
  refine ⟨106492250010226404047432395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141989666680301872063243193 106492250010226404047432395)
  ·
    refine ⟨159738375015339606071148593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106492250010226404047432395 159738375015339606071148593)
    ·
      refine ⟨119803781261504704553361445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159738375015339606071148593 119803781261504704553361445)
      ·
        refine ⟨22463208986532132103755271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119803781261504704553361445 22463208986532132103755271)
        ·
          refine ⟨33694813479798198155632907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22463208986532132103755271 33694813479798198155632907)
          ·
            refine ⟨50542220219697297233449361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33694813479798198155632907 50542220219697297233449361)
            ·
              refine ⟨37906665164772972925087021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50542220219697297233449361 37906665164772972925087021)
              ·
                refine ⟨14214999436789864846907633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37906665164772972925087021 14214999436789864846907633)
                ·
                  refine ⟨10661249577592398635180725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14214999436789864846907633 10661249577592398635180725)
                  ·
                    refine ⟨999492147899287372048193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10661249577592398635180725 999492147899287372048193)
                    ·
                      rfl

theorem cell23_5839512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_5839512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839512 prefixEnd_5839512 := by exact prefixLift 5839512
  have htrace : WordTrace (prefixWord ++ tailWord_5839512) baseStart_5839512 baseEnd_5839512 := by
    simpa [prefixWord, tailWord_5839512, baseEnd_5839512] using wordTrace_append hprefix tailTrace_5839512
  have hstable : (prefixWord ++ tailWord_5839512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839512).length < 2 ^ (prefixWord ++ tailWord_5839512).sum := by decide
  have hdescent : baseEnd_5839512 < baseStart_5839512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839516 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 5]
def baseStart_5839516 : Nat := 118140960795 + 5839516 * 2 ^ 59
def prefixEnd_5839516 : Nat := 4983230072969 + 3 ^ 40 * 5839516 * 2
def baseEnd_5839516 : Nat := 333164277513386677832729

theorem tailTrace_5839516 : CollatzResearch.WordTrace tailWord_5839516 prefixEnd_5839516 333164277513386677832729 := by
  unfold tailWord_5839516
  simp only [CollatzResearch.WordTrace]
  refine ⟨106492322956219158389005201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141989763941625544518673601 106492322956219158389005201)
  ·
    refine ⟨79869242217164368791753901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106492322956219158389005201 79869242217164368791753901)
    ·
      refine ⟨29950965831436638296907713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79869242217164368791753901 29950965831436638296907713)
      ·
        refine ⟨22463224373577478722680785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29950965831436638296907713 22463224373577478722680785)
        ·
          refine ⟨16847418280183109042010589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22463224373577478722680785 16847418280183109042010589)
          ·
            refine ⟨6317781855068665890753971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16847418280183109042010589 6317781855068665890753971)
            ·
              refine ⟨9476672782602998836130957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317781855068665890753971 9476672782602998836130957)
              ·
                refine ⟨3553752293476124563549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9476672782602998836130957 3553752293476124563549109)
                ·
                  refine ⟨333164277513386677832729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3553752293476124563549109 333164277513386677832729)
                  ·
                    rfl

theorem cell23_5839516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_5839516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839516 prefixEnd_5839516 := by exact prefixLift 5839516
  have htrace : WordTrace (prefixWord ++ tailWord_5839516) baseStart_5839516 baseEnd_5839516 := by
    simpa [prefixWord, tailWord_5839516, baseEnd_5839516] using wordTrace_append hprefix tailTrace_5839516
  have hstable : (prefixWord ++ tailWord_5839516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839516).length < 2 ^ (prefixWord ++ tailWord_5839516).sum := by decide
  have hdescent : baseEnd_5839516 < baseStart_5839516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839569 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_5839569 : Nat := 118140960795 + 5839569 * 2 ^ 59
def prefixEnd_5839569 : Nat := 4983230072969 + 3 ^ 40 * 5839569 * 2
def baseEnd_5839569 : Nat := 2998505712095168393131817

theorem tailTrace_5839569 : CollatzResearch.WordTrace tailWord_5839569 prefixEnd_5839569 2998505712095168393131817 := by
  unfold tailWord_5839569
  simp only [CollatzResearch.WordTrace]
  refine ⟨212986578981246306829689761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141991052654164204553126507 212986578981246306829689761)
  ·
    refine ⟨159739934235934730122267321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212986578981246306829689761 159739934235934730122267321)
    ·
      refine ⟨119804950676951047591700491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159739934235934730122267321 119804950676951047591700491)
      ·
        refine ⟨179707426015426571387550737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119804950676951047591700491 179707426015426571387550737)
        ·
          refine ⟨134780569511569928540663053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179707426015426571387550737 134780569511569928540663053)
          ·
            refine ⟨50542713566838723202748645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134780569511569928540663053 50542713566838723202748645)
            ·
              refine ⟨9476758793782260600515371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50542713566838723202748645 9476758793782260600515371)
              ·
                refine ⟨14215138190673390900773057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9476758793782260600515371 14215138190673390900773057)
                ·
                  refine ⟨10661353643005043175579793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14215138190673390900773057 10661353643005043175579793)
                  ·
                    refine ⟨7996015232253782381684845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10661353643005043175579793 7996015232253782381684845)
                    ·
                      refine ⟨2998505712095168393131817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996015232253782381684845 2998505712095168393131817)
                      ·
                        rfl

theorem cell23_5839569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_5839569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839569 prefixEnd_5839569 := by exact prefixLift 5839569
  have htrace : WordTrace (prefixWord ++ tailWord_5839569) baseStart_5839569 baseEnd_5839569 := by
    simpa [prefixWord, tailWord_5839569, baseEnd_5839569] using wordTrace_append hprefix tailTrace_5839569
  have hstable : (prefixWord ++ tailWord_5839569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839569).length < 2 ^ (prefixWord ++ tailWord_5839569).sum := by decide
  have hdescent : baseEnd_5839569 < baseStart_5839569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839589 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 6]
def baseStart_5839589 : Nat := 118140960795 + 5839589 * 2 ^ 59
def prefixEnd_5839589 : Nat := 4983230072969 + 3 ^ 40 * 5839589 * 2
def baseEnd_5839589 : Nat := 333168442412028701653525

theorem tailTrace_5839589 : CollatzResearch.WordTrace tailWord_5839589 prefixEnd_5839589 333168442412028701653525 := by
  unfold tailWord_5839589
  simp only [CollatzResearch.WordTrace]
  refine ⟨212987308441173850245417821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141991538960782566830278547 212987308441173850245417821)
  ·
    refine ⟨79870240665440193842031683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212987308441173850245417821 79870240665440193842031683)
    ·
      refine ⟨119805360998160290763047525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79870240665440193842031683 119805360998160290763047525)
      ·
        refine ⟨22463505187155054518071411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119805360998160290763047525 22463505187155054518071411)
        ·
          refine ⟨33695257780732581777107117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22463505187155054518071411 33695257780732581777107117)
          ·
            refine ⟨12635721667774718166415169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33695257780732581777107117 12635721667774718166415169)
            ·
              refine ⟨9476791250831038624811377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12635721667774718166415169 9476791250831038624811377)
              ·
                refine ⟨7107593438123278968608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9476791250831038624811377 7107593438123278968608533)
                ·
                  refine ⟨333168442412028701653525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7107593438123278968608533 333168442412028701653525)
                  ·
                    rfl

theorem cell23_5839589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_5839589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839589 prefixEnd_5839589 := by exact prefixLift 5839589
  have htrace : WordTrace (prefixWord ++ tailWord_5839589) baseStart_5839589 baseEnd_5839589 := by
    simpa [prefixWord, tailWord_5839589, baseEnd_5839589] using wordTrace_append hprefix tailTrace_5839589
  have hstable : (prefixWord ++ tailWord_5839589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839589).length < 2 ^ (prefixWord ++ tailWord_5839589).sum := by decide
  have hdescent : baseEnd_5839589 < baseStart_5839589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839609 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 4, 3, 2]
def baseStart_5839609 : Nat := 118140960795 + 5839609 * 2 ^ 59
def prefixEnd_5839609 : Nat := 4983230072969 + 3 ^ 40 * 5839609 * 2
def baseEnd_5839609 : Nat := 2998526251321348236631633

theorem tailTrace_5839609 : CollatzResearch.WordTrace tailWord_5839609 prefixEnd_5839609 2998526251321348236631633 := by
  unfold tailWord_5839609
  simp only [CollatzResearch.WordTrace]
  refine ⟨212988037901101393661145881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141992025267400929107430587 212988037901101393661145881)
  ·
    refine ⟨159741028425826045245859411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212988037901101393661145881 159741028425826045245859411)
    ·
      refine ⟨239611542638739067868789117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159741028425826045245859411 239611542638739067868789117)
      ·
        refine ⟨89854328489527150450795919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239611542638739067868789117 89854328489527150450795919)
        ·
          refine ⟨134781492734290725676193879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89854328489527150450795919 134781492734290725676193879)
          ·
            refine ⟨202172239101436088514290819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134781492734290725676193879 202172239101436088514290819)
            ·
              refine ⟨303258358652154132771436229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202172239101436088514290819 303258358652154132771436229)
              ·
                refine ⟨56860942247278899894644293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303258358652154132771436229 56860942247278899894644293)
                ·
                  refine ⟨10661426671364793730245805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56860942247278899894644293 10661426671364793730245805)
                  ·
                    refine ⟨3998035001761797648842177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10661426671364793730245805 3998035001761797648842177)
                    ·
                      refine ⟨2998526251321348236631633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998035001761797648842177 2998526251321348236631633)
                      ·
                        rfl

theorem cell23_5839609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_5839609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839609 prefixEnd_5839609 := by exact prefixLift 5839609
  have htrace : WordTrace (prefixWord ++ tailWord_5839609) baseStart_5839609 baseEnd_5839609 := by
    simpa [prefixWord, tailWord_5839609, baseEnd_5839609] using wordTrace_append hprefix tailTrace_5839609
  have hstable : (prefixWord ++ tailWord_5839609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839609).length < 2 ^ (prefixWord ++ tailWord_5839609).sum := by decide
  have hdescent : baseEnd_5839609 < baseStart_5839609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839649 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_5839649 : Nat := 118140960795 + 5839649 * 2 ^ 59
def prefixEnd_5839649 : Nat := 4983230072969 + 3 ^ 40 * 5839649 * 2
def baseEnd_5839649 : Nat := 999515596849176026710483

theorem tailTrace_5839649 : CollatzResearch.WordTrace tailWord_5839649 prefixEnd_5839649 999515596849176026710483 := by
  unfold tailWord_5839649
  simp only [CollatzResearch.WordTrace]
  refine ⟨212989496820956480492602001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141992997880637653661734667 212989496820956480492602001)
  ·
    refine ⟨159742122615717360369451501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212989496820956480492602001 159742122615717360369451501)
    ·
      refine ⟨59903295980894010138544313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159742122615717360369451501 59903295980894010138544313)
      ·
        refine ⟨44927471985670507603908235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59903295980894010138544313 44927471985670507603908235)
        ·
          refine ⟨67391207978505761405862353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44927471985670507603908235 67391207978505761405862353)
          ·
            refine ⟨50543405983879321054396765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67391207978505761405862353 50543405983879321054396765)
            ·
              refine ⟨18953777243954745395398787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50543405983879321054396765 18953777243954745395398787)
              ·
                refine ⟨28430665865932118093098181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18953777243954745395398787 28430665865932118093098181)
                ·
                  refine ⟨5330749849862272142455909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28430665865932118093098181 5330749849862272142455909)
                  ·
                    refine ⟨999515596849176026710483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5330749849862272142455909 999515596849176026710483)
                    ·
                      rfl

theorem cell23_5839649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_5839649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839649 prefixEnd_5839649 := by exact prefixLift 5839649
  have htrace : WordTrace (prefixWord ++ tailWord_5839649) baseStart_5839649 baseEnd_5839649 := by
    simpa [prefixWord, tailWord_5839649, baseEnd_5839649] using wordTrace_append hprefix tailTrace_5839649
  have hstable : (prefixWord ++ tailWord_5839649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839649).length < 2 ^ (prefixWord ++ tailWord_5839649).sum := by decide
  have hdescent : baseEnd_5839649 < baseStart_5839649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839669 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_5839669 : Nat := 118140960795 + 5839669 * 2 ^ 59
def prefixEnd_5839669 : Nat := 4983230072969 + 3 ^ 40 * 5839669 * 2
def baseEnd_5839669 : Nat := 2998557060160618001881357

theorem tailTrace_5839669 : CollatzResearch.WordTrace tailWord_5839669 prefixEnd_5839669 2998557060160618001881357 := by
  unfold tailWord_5839669
  simp only [CollatzResearch.WordTrace]
  refine ⟨212990226280884023908330061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141993484187256015938886707 212990226280884023908330061)
  ·
    refine ⟨79871334855331508965623773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212990226280884023908330061 79871334855331508965623773)
    ·
      refine ⟨29951750570749315862108915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79871334855331508965623773 29951750570749315862108915)
      ·
        refine ⟨44927625856123973793163373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29951750570749315862108915 44927625856123973793163373)
        ·
          refine ⟨16847859696046490172436265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44927625856123973793163373 16847859696046490172436265)
          ·
            refine ⟨12635894772034867629327199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16847859696046490172436265 12635894772034867629327199)
            ·
              refine ⟨18953842158052301443990799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12635894772034867629327199 18953842158052301443990799)
              ·
                refine ⟨28430763237078452165986199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18953842158052301443990799 28430763237078452165986199)
                ·
                  refine ⟨42646144855617678248979299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28430763237078452165986199 42646144855617678248979299)
                  ·
                    refine ⟨63969217283426517373468949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42646144855617678248979299 63969217283426517373468949)
                    ·
                      refine ⟨2998557060160618001881357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63969217283426517373468949 2998557060160618001881357)
                      ·
                        rfl

theorem cell23_5839669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_5839669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839669 prefixEnd_5839669 := by exact prefixLift 5839669
  have htrace : WordTrace (prefixWord ++ tailWord_5839669) baseStart_5839669 baseEnd_5839669 := by
    simpa [prefixWord, tailWord_5839669, baseEnd_5839669] using wordTrace_append hprefix tailTrace_5839669
  have hstable : (prefixWord ++ tailWord_5839669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839669).length < 2 ^ (prefixWord ++ tailWord_5839669).sum := by decide
  have hdescent : baseEnd_5839669 < baseStart_5839669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839679 : List Nat := [1, 1, 2, 2, 5, 1, 4, 7]
def baseStart_5839679 : Nat := 118140960795 + 5839679 * 2 ^ 59
def prefixEnd_5839679 : Nat := 4983230072969 + 3 ^ 40 * 5839679 * 2
def baseEnd_5839679 : Nat := 111057859072857887509493

theorem tailTrace_5839679 : CollatzResearch.WordTrace tailWord_5839679 prefixEnd_5839679 111057859072857887509493 := by
  unfold tailWord_5839679
  simp only [CollatzResearch.WordTrace]
  refine ⟨212990591010847795616194091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141993727340565197077462727 212990591010847795616194091)
  ·
    refine ⟨319485886516271693424291137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212990591010847795616194091 319485886516271693424291137)
    ·
      refine ⟨239614414887203770068218353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319485886516271693424291137 239614414887203770068218353)
      ·
        refine ⟨179710811165402827551163765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239614414887203770068218353 179710811165402827551163765)
        ·
          refine ⟨16847888546756515082921603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179710811165402827551163765 16847888546756515082921603)
          ·
            refine ⟨25271832820134772624382405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16847888546756515082921603 25271832820134772624382405)
            ·
              refine ⟨4738468653775269867071701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25271832820134772624382405 4738468653775269867071701)
              ·
                refine ⟨111057859072857887509493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4738468653775269867071701 111057859072857887509493)
                ·
                  rfl

theorem cell23_5839679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 7].length) (baseStart_5839679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839679 prefixEnd_5839679 := by exact prefixLift 5839679
  have htrace : WordTrace (prefixWord ++ tailWord_5839679) baseStart_5839679 baseEnd_5839679 := by
    simpa [prefixWord, tailWord_5839679, baseEnd_5839679] using wordTrace_append hprefix tailTrace_5839679
  have hstable : (prefixWord ++ tailWord_5839679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839679).length < 2 ^ (prefixWord ++ tailWord_5839679).sum := by decide
  have hdescent : baseEnd_5839679 < baseStart_5839679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839684 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5839684 : Nat := 118140960795 + 5839684 * 2 ^ 59
def prefixEnd_5839684 : Nat := 4983230072969 + 3 ^ 40 * 5839684 * 2
def baseEnd_5839684 : Nat := 2998564762370435443193789

theorem tailTrace_5839684 : CollatzResearch.WordTrace tailWord_5839684 prefixEnd_5839684 2998564762370435443193789 := by
  unfold tailWord_5839684
  simp only [CollatzResearch.WordTrace]
  refine ⟨106495386687914840735063053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141993848917219787646750737 106495386687914840735063053)
  ·
    refine ⟨39935770007968065275648645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106495386687914840735063053 39935770007968065275648645)
    ·
      refine ⟨7487956876494012239184121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39935770007968065275648645 7487956876494012239184121)
      ·
        refine ⟨5615967657370509179388091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487956876494012239184121 5615967657370509179388091)
        ·
          refine ⟨8423951486055763769082137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615967657370509179388091 8423951486055763769082137)
          ·
            refine ⟨6317963614541822826811603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423951486055763769082137 6317963614541822826811603)
            ·
              refine ⟨9476945421812734240217405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317963614541822826811603 9476945421812734240217405)
              ·
                refine ⟨3553854533179775340081527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9476945421812734240217405 3553854533179775340081527)
                ·
                  refine ⟨5330781799769663010122291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553854533179775340081527 5330781799769663010122291)
                  ·
                    refine ⟨7996172699654494515183437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5330781799769663010122291 7996172699654494515183437)
                    ·
                      refine ⟨2998564762370435443193789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996172699654494515183437 2998564762370435443193789)
                      ·
                        rfl

theorem cell23_5839684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5839684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839684 prefixEnd_5839684 := by exact prefixLift 5839684
  have htrace : WordTrace (prefixWord ++ tailWord_5839684) baseStart_5839684 baseEnd_5839684 := by
    simpa [prefixWord, tailWord_5839684, baseEnd_5839684] using wordTrace_append hprefix tailTrace_5839684
  have hstable : (prefixWord ++ tailWord_5839684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839684).length < 2 ^ (prefixWord ++ tailWord_5839684).sum := by decide
  have hdescent : baseEnd_5839684 < baseStart_5839684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839693 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5839693 : Nat := 118140960795 + 5839693 * 2 ^ 59
def prefixEnd_5839693 : Nat := 4983230072969 + 3 ^ 40 * 5839693 * 2
def baseEnd_5839693 : Nat := 2998569383696325907981247

theorem tailTrace_5839693 : CollatzResearch.WordTrace tailWord_5839693 prefixEnd_5839693 2998569383696325907981247 := by
  unfold tailWord_5839693
  simp only [CollatzResearch.WordTrace]
  refine ⟨212991101632797076007203733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141994067755198050671469155 212991101632797076007203733)
  ·
    refine ⟨9983957889037362937837675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212991101632797076007203733 9983957889037362937837675)
    ·
      refine ⟨14975936833556044406756513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983957889037362937837675 14975936833556044406756513)
      ·
        refine ⟨11231952625167033305067385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14975936833556044406756513 11231952625167033305067385)
        ·
          refine ⟨8423964468875274978800539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11231952625167033305067385 8423964468875274978800539)
          ·
            refine ⟨12635946703312912468200809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8423964468875274978800539 12635946703312912468200809)
            ·
              refine ⟨9476960027484684351150607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12635946703312912468200809 9476960027484684351150607)
              ·
                refine ⟨14215440041227026526725911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9476960027484684351150607 14215440041227026526725911)
                ·
                  refine ⟨21323160061840539790088867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14215440041227026526725911 21323160061840539790088867)
                  ·
                    refine ⟨31984740092760809685133301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21323160061840539790088867 31984740092760809685133301)
                    ·
                      refine ⟨2998569383696325907981247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31984740092760809685133301 2998569383696325907981247)
                      ·
                        rfl

theorem cell23_5839693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5839693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839693 prefixEnd_5839693 := by exact prefixLift 5839693
  have htrace : WordTrace (prefixWord ++ tailWord_5839693) baseStart_5839693 baseEnd_5839693 := by
    simpa [prefixWord, tailWord_5839693, baseEnd_5839693] using wordTrace_append hprefix tailTrace_5839693
  have hstable : (prefixWord ++ tailWord_5839693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839693).length < 2 ^ (prefixWord ++ tailWord_5839693).sum := by decide
  have hdescent : baseEnd_5839693 < baseStart_5839693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839706 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_5839706 : Nat := 118140960795 + 5839706 * 2 ^ 59
def prefixEnd_5839706 : Nat := 4983230072969 + 3 ^ 40 * 5839706 * 2
def baseEnd_5839706 : Nat := 2998576058944834357118687

theorem tailTrace_5839706 : CollatzResearch.WordTrace tailWord_5839706 prefixEnd_5839706 2998576058944834357118687 := by
  unfold tailWord_5839706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53247893945437494806856743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141994383854499986151617981 53247893945437494806856743)
  ·
    refine ⟨79871840918156242210285115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53247893945437494806856743 79871840918156242210285115)
    ·
      refine ⟨119807761377234363315427673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79871840918156242210285115 119807761377234363315427673)
      ·
        refine ⟨89855821032925772486570755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119807761377234363315427673 89855821032925772486570755)
        ·
          refine ⟨134783731549388658729856133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89855821032925772486570755 134783731549388658729856133)
          ·
            refine ⟨25271949665510373511848025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134783731549388658729856133 25271949665510373511848025)
            ·
              refine ⟨18953962249132780133886019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25271949665510373511848025 18953962249132780133886019)
              ·
                refine ⟨28430943373699170200829029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18953962249132780133886019 28430943373699170200829029)
                ·
                  refine ⟨5330801882568594412655443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28430943373699170200829029 5330801882568594412655443)
                  ·
                    refine ⟨7996202823852891618983165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5330801882568594412655443 7996202823852891618983165)
                    ·
                      refine ⟨2998576058944834357118687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996202823852891618983165 2998576058944834357118687)
                      ·
                        rfl

theorem cell23_5839706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_5839706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839706 prefixEnd_5839706 := by exact prefixLift 5839706
  have htrace : WordTrace (prefixWord ++ tailWord_5839706) baseStart_5839706 baseEnd_5839706 := by
    simpa [prefixWord, tailWord_5839706, baseEnd_5839706] using wordTrace_append hprefix tailTrace_5839706
  have hstable : (prefixWord ++ tailWord_5839706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839706).length < 2 ^ (prefixWord ++ tailWord_5839706).sum := by decide
  have hdescent : baseEnd_5839706 < baseStart_5839706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839723 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 2, 1, 3]
def baseStart_5839723 : Nat := 118140960795 + 5839723 * 2 ^ 59
def prefixEnd_5839723 : Nat := 4983230072969 + 3 ^ 40 * 5839723 * 2
def baseEnd_5839723 : Nat := 2998584788115960790606109

theorem tailTrace_5839723 : CollatzResearch.WordTrace tailWord_5839723 prefixEnd_5839723 2998584788115960790606109 := by
  unfold tailWord_5839723
  simp only [CollatzResearch.WordTrace]
  refine ⟨212992195822688391130795823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141994797215125594087197215 212992195822688391130795823)
  ·
    refine ⟨319488293734032586696193735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212992195822688391130795823 319488293734032586696193735)
    ·
      refine ⟨479232440601048880044290603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319488293734032586696193735 479232440601048880044290603)
      ·
        refine ⟨718848660901573320066435905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479232440601048880044290603 718848660901573320066435905)
        ·
          refine ⟨539136495676179990049826929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718848660901573320066435905 539136495676179990049826929)
          ·
            refine ⟨404352371757134992537370197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539136495676179990049826929 404352371757134992537370197)
            ·
              refine ⟨4738504356528925693797307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 404352371757134992537370197 4738504356528925693797307)
              ·
                refine ⟨7107756534793388540695961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738504356528925693797307 7107756534793388540695961)
                ·
                  refine ⟨5330817401095041405521971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7107756534793388540695961 5330817401095041405521971)
                  ·
                    refine ⟨7996226101642562108282957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5330817401095041405521971 7996226101642562108282957)
                    ·
                      refine ⟨2998584788115960790606109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996226101642562108282957 2998584788115960790606109)
                      ·
                        rfl

theorem cell23_5839723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 1, 3].length) (baseStart_5839723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839723 prefixEnd_5839723 := by exact prefixLift 5839723
  have htrace : WordTrace (prefixWord ++ tailWord_5839723) baseStart_5839723 baseEnd_5839723 := by
    simpa [prefixWord, tailWord_5839723, baseEnd_5839723] using wordTrace_append hprefix tailTrace_5839723
  have hstable : (prefixWord ++ tailWord_5839723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839723).length < 2 ^ (prefixWord ++ tailWord_5839723).sum := by decide
  have hdescent : baseEnd_5839723 < baseStart_5839723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839733 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5839733 : Nat := 118140960795 + 5839733 * 2 ^ 59
def prefixEnd_5839733 : Nat := 4983230072969 + 3 ^ 40 * 5839733 * 2
def baseEnd_5839733 : Nat := 2998589922922505751481063

theorem tailTrace_5839733 : CollatzResearch.WordTrace tailWord_5839733 prefixEnd_5839733 2998589922922505751481063 := by
  unfold tailWord_5839733
  simp only [CollatzResearch.WordTrace]
  refine ⟨212992560552652162838659853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141995040368434775225773235 212992560552652162838659853)
  ·
    refine ⟨79872210207244561064497445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212992560552652162838659853 79872210207244561064497445)
    ·
      refine ⟨14976039413858355199593271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79872210207244561064497445 14976039413858355199593271)
      ·
        refine ⟨22464059120787532799389907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14976039413858355199593271 22464059120787532799389907)
        ·
          refine ⟨33696088681181299199084861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22464059120787532799389907 33696088681181299199084861)
          ·
            refine ⟨12636033255442987199656823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33696088681181299199084861 12636033255442987199656823)
            ·
              refine ⟨18954049883164480799485235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636033255442987199656823 18954049883164480799485235)
              ·
                refine ⟨28431074824746721199227853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18954049883164480799485235 28431074824746721199227853)
                ·
                  refine ⟨10661653059280020449710445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28431074824746721199227853 10661653059280020449710445)
                  ·
                    refine ⟨3998119897230007668641417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10661653059280020449710445 3998119897230007668641417)
                    ·
                      refine ⟨2998589922922505751481063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998119897230007668641417 2998589922922505751481063)
                      ·
                        rfl

theorem cell23_5839733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5839733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839733 prefixEnd_5839733 := by exact prefixLift 5839733
  have htrace : WordTrace (prefixWord ++ tailWord_5839733) baseStart_5839733 baseEnd_5839733 := by
    simpa [prefixWord, tailWord_5839733, baseEnd_5839733] using wordTrace_append hprefix tailTrace_5839733
  have hstable : (prefixWord ++ tailWord_5839733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839733).length < 2 ^ (prefixWord ++ tailWord_5839733).sum := by decide
  have hdescent : baseEnd_5839733 < baseStart_5839733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839749 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_5839749 : Nat := 118140960795 + 5839749 * 2 ^ 59
def prefixEnd_5839749 : Nat := 4983230072969 + 3 ^ 40 * 5839749 * 2
def baseEnd_5839749 : Nat := 2998598138612977688880989

theorem tailTrace_5839749 : CollatzResearch.WordTrace tailWord_5839749 prefixEnd_5839749 2998598138612977688880989 := by
  unfold tailWord_5839749
  simp only [CollatzResearch.WordTrace]
  refine ⟨212993144120594197571242301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141995429413729465047494867 212993144120594197571242301)
  ·
    refine ⟨79872429045222824089215863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212993144120594197571242301 79872429045222824089215863)
    ·
      refine ⟨119808643567834236133823795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79872429045222824089215863 119808643567834236133823795)
      ·
        refine ⟨179712965351751354200735693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119808643567834236133823795 179712965351751354200735693)
        ·
          refine ⟨67392362006906757825275885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179712965351751354200735693 67392362006906757825275885)
          ·
            refine ⟨25272135752590034184478457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67392362006906757825275885 25272135752590034184478457)
            ·
              refine ⟨18954101814442525638358843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25272135752590034184478457 18954101814442525638358843)
              ·
                refine ⟨28431152721663788457538265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18954101814442525638358843 28431152721663788457538265)
                ·
                  refine ⟨21323364541247841343153699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28431152721663788457538265 21323364541247841343153699)
                  ·
                    refine ⟨31985046811871762014730549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21323364541247841343153699 31985046811871762014730549)
                    ·
                      refine ⟨2998598138612977688880989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31985046811871762014730549 2998598138612977688880989)
                      ·
                        rfl

theorem cell23_5839749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_5839749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839749 prefixEnd_5839749 := by exact prefixLift 5839749
  have htrace : WordTrace (prefixWord ++ tailWord_5839749) baseStart_5839749 baseEnd_5839749 := by
    simpa [prefixWord, tailWord_5839749, baseEnd_5839749] using wordTrace_append hprefix tailTrace_5839749
  have hstable : (prefixWord ++ tailWord_5839749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839749).length < 2 ^ (prefixWord ++ tailWord_5839749).sum := by decide
  have hdescent : baseEnd_5839749 < baseStart_5839749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839779 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3]
def baseStart_5839779 : Nat := 118140960795 + 5839779 * 2 ^ 59
def prefixEnd_5839779 : Nat := 4983230072969 + 3 ^ 40 * 5839779 * 2
def baseEnd_5839779 : Nat := 2998613543032612571505851

theorem tailTrace_5839779 : CollatzResearch.WordTrace tailWord_5839779 prefixEnd_5839779 2998613543032612571505851 := by
  unfold tailWord_5839779
  simp only [CollatzResearch.WordTrace]
  refine ⟨212994238310485512694834391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141996158873657008463222927 212994238310485512694834391)
  ·
    refine ⟨319491357465728269042251587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212994238310485512694834391 319491357465728269042251587)
    ·
      refine ⟨479237036198592403563377381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319491357465728269042251587 479237036198592403563377381)
      ·
        refine ⟨89856944287236075668133259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479237036198592403563377381 89856944287236075668133259)
        ·
          refine ⟨134785416430854113502199889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89856944287236075668133259 134785416430854113502199889)
          ·
            refine ⟨101089062323140585126649917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134785416430854113502199889 101089062323140585126649917)
            ·
              refine ⟨37908398371177719422493719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101089062323140585126649917 37908398371177719422493719)
              ·
                refine ⟨56862597556766579133740579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37908398371177719422493719 56862597556766579133740579)
                ·
                  refine ⟨85293896335149868700610869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56862597556766579133740579 85293896335149868700610869)
                  ·
                    refine ⟨7996302781420300190682269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85293896335149868700610869 7996302781420300190682269)
                    ·
                      refine ⟨2998613543032612571505851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996302781420300190682269 2998613543032612571505851)
                      ·
                        rfl

theorem cell23_5839779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_5839779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839779 prefixEnd_5839779 := by exact prefixLift 5839779
  have htrace : WordTrace (prefixWord ++ tailWord_5839779) baseStart_5839779 baseEnd_5839779 := by
    simpa [prefixWord, tailWord_5839779, baseEnd_5839779] using wordTrace_append hprefix tailTrace_5839779
  have hstable : (prefixWord ++ tailWord_5839779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839779).length < 2 ^ (prefixWord ++ tailWord_5839779).sum := by decide
  have hdescent : baseEnd_5839779 < baseStart_5839779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839856 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_5839856 : Nat := 118140960795 + 5839856 * 2 ^ 59
def prefixEnd_5839856 : Nat := 4983230072969 + 3 ^ 40 * 5839856 * 2
def baseEnd_5839856 : Nat := 2998653081043008770242997

theorem tailTrace_5839856 : CollatzResearch.WordTrace tailWord_5839856 prefixEnd_5839856 2998653081043008770242997 := by
  unfold tailWord_5839856
  simp only [CollatzResearch.WordTrace]
  refine ⟨106498523365603277422693711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141998031154137703230258281 106498523365603277422693711)
  ·
    refine ⟨159747785048404916134040567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106498523365603277422693711 159747785048404916134040567)
    ·
      refine ⟨239621677572607374201060851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159747785048404916134040567 239621677572607374201060851)
      ·
        refine ⟨359432516358911061301591277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239621677572607374201060851 359432516358911061301591277)
        ·
          refine ⟨134787193634591647988096729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359432516358911061301591277 134787193634591647988096729)
          ·
            refine ⟨101090395225943735991072547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134787193634591647988096729 101090395225943735991072547)
            ·
              refine ⟨151635592838915603986608821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101090395225943735991072547 151635592838915603986608821)
              ·
                refine ⟨14215836828648337873744577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151635592838915603986608821 14215836828648337873744577)
                ·
                  refine ⟨10661877621486253405308433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14215836828648337873744577 10661877621486253405308433)
                  ·
                    refine ⟨7996408216114690053981325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10661877621486253405308433 7996408216114690053981325)
                    ·
                      refine ⟨2998653081043008770242997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996408216114690053981325 2998653081043008770242997)
                      ·
                        rfl

theorem cell23_5839856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_5839856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839856 prefixEnd_5839856 := by exact prefixLift 5839856
  have htrace : WordTrace (prefixWord ++ tailWord_5839856) baseStart_5839856 baseEnd_5839856 := by
    simpa [prefixWord, tailWord_5839856, baseEnd_5839856] using wordTrace_append hprefix tailTrace_5839856
  have hstable : (prefixWord ++ tailWord_5839856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839856).length < 2 ^ (prefixWord ++ tailWord_5839856).sum := by decide
  have hdescent : baseEnd_5839856 < baseStart_5839856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839870 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5839870 : Nat := 118140960795 + 5839870 * 2 ^ 59
def prefixEnd_5839870 : Nat := 4983230072969 + 3 ^ 40 * 5839870 * 2
def baseEnd_5839870 : Nat := 2998660269772171715467933

theorem tailTrace_5839870 : CollatzResearch.WordTrace tailWord_5839870 prefixEnd_5839870 2998660269772171715467933 := by
  unfold tailWord_5839870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624694669144479404549633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141998371568770556824264709 26624694669144479404549633)
  ·
    refine ⟨19968521001858359553412225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26624694669144479404549633 19968521001858359553412225)
    ·
      refine ⟨14976390751393769665059169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19968521001858359553412225 14976390751393769665059169)
      ·
        refine ⟨11232293063545327248794377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14976390751393769665059169 11232293063545327248794377)
        ·
          refine ⟨8424219797658995436595783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11232293063545327248794377 8424219797658995436595783)
          ·
            refine ⟨12636329696488493154893675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424219797658995436595783 12636329696488493154893675)
            ·
              refine ⟨18954494544732739732340513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636329696488493154893675 18954494544732739732340513)
              ·
                refine ⟨14215870908549554799255385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18954494544732739732340513 14215870908549554799255385)
                ·
                  refine ⟨10661903181412166099441539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14215870908549554799255385 10661903181412166099441539)
                  ·
                    refine ⟨15992854772118249149162309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10661903181412166099441539 15992854772118249149162309)
                    ·
                      refine ⟨2998660269772171715467933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15992854772118249149162309 2998660269772171715467933)
                      ·
                        rfl

theorem cell23_5839870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5839870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839870 prefixEnd_5839870 := by exact prefixLift 5839870
  have htrace : WordTrace (prefixWord ++ tailWord_5839870) baseStart_5839870 baseEnd_5839870 := by
    simpa [prefixWord, tailWord_5839870, baseEnd_5839870] using wordTrace_append hprefix tailTrace_5839870
  have hstable : (prefixWord ++ tailWord_5839870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839870).length < 2 ^ (prefixWord ++ tailWord_5839870).sum := by decide
  have hdescent : baseEnd_5839870 < baseStart_5839870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839873 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_5839873 : Nat := 118140960795 + 5839873 * 2 ^ 59
def prefixEnd_5839873 : Nat := 4983230072969 + 3 ^ 40 * 5839873 * 2
def baseEnd_5839873 : Nat := 2998661810214135203730419

theorem tailTrace_5839873 : CollatzResearch.WordTrace tailWord_5839873 prefixEnd_5839873 2998661810214135203730419 := by
  unfold tailWord_5839873
  simp only [CollatzResearch.WordTrace]
  refine ⟨212997666772144966748756273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141998444514763311165837515 212997666772144966748756273)
  ·
    refine ⟨159748250079108725061567205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212997666772144966748756273 159748250079108725061567205)
    ·
      refine ⟨29952796889832885949043851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159748250079108725061567205 29952796889832885949043851)
      ·
        refine ⟨44929195334749328923565777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29952796889832885949043851 44929195334749328923565777)
        ·
          refine ⟨33696896501061996692674333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44929195334749328923565777 33696896501061996692674333)
          ·
            refine ⟨12636336187898248759752875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33696896501061996692674333 12636336187898248759752875)
            ·
              refine ⟨18954504281847373139629313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636336187898248759752875 18954504281847373139629313)
              ·
                refine ⟨14215878211385529854721985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18954504281847373139629313 14215878211385529854721985)
                ·
                  refine ⟨10661908658539147391041489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14215878211385529854721985 10661908658539147391041489)
                  ·
                    refine ⟨7996431493904360543281117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10661908658539147391041489 7996431493904360543281117)
                    ·
                      refine ⟨2998661810214135203730419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996431493904360543281117 2998661810214135203730419)
                      ·
                        rfl

theorem cell23_5839873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_5839873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839873 prefixEnd_5839873 := by exact prefixLift 5839873
  have htrace : WordTrace (prefixWord ++ tailWord_5839873) baseStart_5839873 baseEnd_5839873 := by
    simpa [prefixWord, tailWord_5839873, baseEnd_5839873] using wordTrace_append hprefix tailTrace_5839873
  have hstable : (prefixWord ++ tailWord_5839873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839873).length < 2 ^ (prefixWord ++ tailWord_5839873).sum := by decide
  have hdescent : baseEnd_5839873 < baseStart_5839873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839893 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 6]
def baseStart_5839893 : Nat := 118140960795 + 5839893 * 2 ^ 59
def prefixEnd_5839893 : Nat := 4983230072969 + 3 ^ 40 * 5839893 * 2
def baseEnd_5839893 : Nat := 333185786647469458386703

theorem tailTrace_5839893 : CollatzResearch.WordTrace tailWord_5839893 prefixEnd_5839893 333185786647469458386703 := by
  unfold tailWord_5839893
  simp only [CollatzResearch.WordTrace]
  refine ⟨212998396232072510164484333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141998930821381673442989555 212998396232072510164484333)
  ·
    refine ⟨79874398587027191311681625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212998396232072510164484333 79874398587027191311681625)
    ·
      refine ⟨59905798940270393483761219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79874398587027191311681625 59905798940270393483761219)
      ·
        refine ⟨89858698410405590225641829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59905798940270393483761219 89858698410405590225641829)
        ·
          refine ⟨16848505951951048167307843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89858698410405590225641829 16848505951951048167307843)
          ·
            refine ⟨25272758927926572250961765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16848505951951048167307843 25272758927926572250961765)
            ·
              refine ⟨4738642298986232297055331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25272758927926572250961765 4738642298986232297055331)
              ·
                refine ⟨7107963448479348445582997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738642298986232297055331 7107963448479348445582997)
                ·
                  refine ⟨333185786647469458386703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7107963448479348445582997 333185786647469458386703)
                  ·
                    rfl

theorem cell23_5839893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_5839893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839893 prefixEnd_5839893 := by exact prefixLift 5839893
  have htrace : WordTrace (prefixWord ++ tailWord_5839893) baseStart_5839893 baseEnd_5839893 := by
    simpa [prefixWord, tailWord_5839893, baseEnd_5839893] using wordTrace_append hprefix tailTrace_5839893
  have hstable : (prefixWord ++ tailWord_5839893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839893).length < 2 ^ (prefixWord ++ tailWord_5839893).sum := by decide
  have hdescent : baseEnd_5839893 < baseStart_5839893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839920 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 1, 1, 3]
def baseStart_5839920 : Nat := 118140960795 + 5839920 * 2 ^ 59
def prefixEnd_5839920 : Nat := 4983230072969 + 3 ^ 40 * 5839920 * 2
def baseEnd_5839920 : Nat := 2998685943804896519842703

theorem tailTrace_5839920 : CollatzResearch.WordTrace tailWord_5839920 prefixEnd_5839920 2998685943804896519842703 := by
  unfold tailWord_5839920
  simp only [CollatzResearch.WordTrace]
  refine ⟨106499690501487346887858607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141999587335316462517144809 106499690501487346887858607)
  ·
    refine ⟨159749535752231020331787911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106499690501487346887858607 159749535752231020331787911)
    ·
      refine ⟨239624303628346530497681867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159749535752231020331787911 239624303628346530497681867)
      ·
        refine ⟨359436455442519795746522801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239624303628346530497681867 359436455442519795746522801)
        ·
          refine ⟨269577341581889846809892101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359436455442519795746522801 269577341581889846809892101)
          ·
            refine ⟨50545751546604346276854769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269577341581889846809892101 50545751546604346276854769)
            ·
              refine ⟨37909313659953259707641077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50545751546604346276854769 37909313659953259707641077)
              ·
                refine ⟨3553998155620618097591351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37909313659953259707641077 3553998155620618097591351)
                ·
                  refine ⟨5330997233430927146387027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553998155620618097591351 5330997233430927146387027)
                  ·
                    refine ⟨7996495850146390719580541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5330997233430927146387027 7996495850146390719580541)
                    ·
                      refine ⟨2998685943804896519842703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996495850146390719580541 2998685943804896519842703)
                      ·
                        rfl

theorem cell23_5839920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 1, 3].length) (baseStart_5839920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839920 prefixEnd_5839920 := by exact prefixLift 5839920
  have htrace : WordTrace (prefixWord ++ tailWord_5839920) baseStart_5839920 baseEnd_5839920 := by
    simpa [prefixWord, tailWord_5839920, baseEnd_5839920] using wordTrace_append hprefix tailTrace_5839920
  have hstable : (prefixWord ++ tailWord_5839920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839920).length < 2 ^ (prefixWord ++ tailWord_5839920).sum := by decide
  have hdescent : baseEnd_5839920 < baseStart_5839920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839946 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_5839946 : Nat := 118140960795 + 5839946 * 2 ^ 59
def prefixEnd_5839946 : Nat := 4983230072969 + 3 ^ 40 * 5839946 * 2
def baseEnd_5839946 : Nat := 2998699294301913418117583

theorem tailTrace_5839946 : CollatzResearch.WordTrace tailWord_5839946 prefixEnd_5839946 2998699294301913418117583 := by
  unfold tailWord_5839946
  simp only [CollatzResearch.WordTrace]
  refine ⟨53250082325220125054040923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142000219533920333477442461 53250082325220125054040923)
  ·
    refine ⟨79875123487830187581061385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53250082325220125054040923 79875123487830187581061385)
    ·
      refine ⟨59906342615872640685796039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79875123487830187581061385 59906342615872640685796039)
      ·
        refine ⟨89859513923808961028694059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59906342615872640685796039 89859513923808961028694059)
        ·
          refine ⟨134789270885713441543041089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89859513923808961028694059 134789270885713441543041089)
          ·
            refine ⟨101091953164285081157280817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134789270885713441543041089 101091953164285081157280817)
            ·
              refine ⟨75818964873213810867960613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101091953164285081157280817 75818964873213810867960613)
              ·
                refine ⟨14216055913727589537742615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75818964873213810867960613 14216055913727589537742615)
                ·
                  refine ⟨21324083870591384306613923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14216055913727589537742615 21324083870591384306613923)
                  ·
                    refine ⟨31986125805887076459920885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21324083870591384306613923 31986125805887076459920885)
                    ·
                      refine ⟨2998699294301913418117583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31986125805887076459920885 2998699294301913418117583)
                      ·
                        rfl

theorem cell23_5839946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_5839946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839946 prefixEnd_5839946 := by exact prefixLift 5839946
  have htrace : WordTrace (prefixWord ++ tailWord_5839946) baseStart_5839946 baseEnd_5839946 := by
    simpa [prefixWord, tailWord_5839946, baseEnd_5839946] using wordTrace_append hprefix tailTrace_5839946
  have hstable : (prefixWord ++ tailWord_5839946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839946).length < 2 ^ (prefixWord ++ tailWord_5839946).sum := by decide
  have hdescent : baseEnd_5839946 < baseStart_5839946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839953 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_5839953 : Nat := 118140960795 + 5839953 * 2 ^ 59
def prefixEnd_5839953 : Nat := 4983230072969 + 3 ^ 40 * 5839953 * 2
def baseEnd_5839953 : Nat := 999567629555498296910017

theorem tailTrace_5839953 : CollatzResearch.WordTrace tailWord_5839953 prefixEnd_5839953 999567629555498296910017 := by
  unfold tailWord_5839953
  simp only [CollatzResearch.WordTrace]
  refine ⟨213000584611855140411668513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142000389741236760274445675 213000584611855140411668513)
  ·
    refine ⟨159750438458891355308751385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213000584611855140411668513 159750438458891355308751385)
    ·
      refine ⟨119812828844168516481563539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159750438458891355308751385 119812828844168516481563539)
      ·
        refine ⟨179719243266252774722345309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119812828844168516481563539 179719243266252774722345309)
        ·
          refine ⟨67394716224844790520879491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179719243266252774722345309 67394716224844790520879491)
          ·
            refine ⟨101092074337267185781319237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67394716224844790520879491 101092074337267185781319237)
            ·
              refine ⟨18954763938237597333997357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101092074337267185781319237 18954763938237597333997357)
              ·
                refine ⟨7108036476839099000249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18954763938237597333997357 7108036476839099000249009)
                ·
                  refine ⟨5331027357629324250186757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7108036476839099000249009 5331027357629324250186757)
                  ·
                    refine ⟨999567629555498296910017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331027357629324250186757 999567629555498296910017)
                    ·
                      rfl

theorem cell23_5839953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_5839953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839953 prefixEnd_5839953 := by exact prefixLift 5839953
  have htrace : WordTrace (prefixWord ++ tailWord_5839953) baseStart_5839953 baseEnd_5839953 := by
    simpa [prefixWord, tailWord_5839953, baseEnd_5839953] using wordTrace_append hprefix tailTrace_5839953
  have hstable : (prefixWord ++ tailWord_5839953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839953).length < 2 ^ (prefixWord ++ tailWord_5839953).sum := by decide
  have hdescent : baseEnd_5839953 < baseStart_5839953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839956 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5839956 : Nat := 118140960795 + 5839956 * 2 ^ 59
def prefixEnd_5839956 : Nat := 4983230072969 + 3 ^ 40 * 5839956 * 2
def baseEnd_5839956 : Nat := 2998704429108458378992537

theorem tailTrace_5839956 : CollatzResearch.WordTrace tailWord_5839956 prefixEnd_5839956 2998704429108458378992537 := by
  unfold tailWord_5839956
  simp only [CollatzResearch.WordTrace]
  refine ⟨106500347015422135962013861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142000462687229514616018481 106500347015422135962013861)
  ·
    refine ⟨19968815065391650492877599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106500347015422135962013861 19968815065391650492877599)
    ·
      refine ⟨29953222598087475739316399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19968815065391650492877599 29953222598087475739316399)
      ·
        refine ⟨44929833897131213608974599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29953222598087475739316399 44929833897131213608974599)
        ·
          refine ⟨67394750845696820413461899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44929833897131213608974599 67394750845696820413461899)
          ·
            refine ⟨101092126268545230620192849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67394750845696820413461899 101092126268545230620192849)
            ·
              refine ⟨75819094701408922965144637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101092126268545230620192849 75819094701408922965144637)
              ·
                refine ⟨28432160513028346111929239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75819094701408922965144637 28432160513028346111929239)
                ·
                  refine ⟨42648240769542519167893859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28432160513028346111929239 42648240769542519167893859)
                  ·
                    refine ⟨63972361154313778751840789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42648240769542519167893859 63972361154313778751840789)
                    ·
                      refine ⟨2998704429108458378992537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63972361154313778751840789 2998704429108458378992537)
                      ·
                        rfl

theorem cell23_5839956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5839956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839956 prefixEnd_5839956 := by exact prefixLift 5839956
  have htrace : WordTrace (prefixWord ++ tailWord_5839956) baseStart_5839956 baseEnd_5839956 := by
    simpa [prefixWord, tailWord_5839956, baseEnd_5839956] using wordTrace_append hprefix tailTrace_5839956
  have hstable : (prefixWord ++ tailWord_5839956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839956).length < 2 ^ (prefixWord ++ tailWord_5839956).sum := by decide
  have hdescent : baseEnd_5839956 < baseStart_5839956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839960 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_5839960 : Nat := 118140960795 + 5839960 * 2 ^ 59
def prefixEnd_5839960 : Nat := 4983230072969 + 3 ^ 40 * 5839960 * 2
def baseEnd_5839960 : Nat := 2998706483031076363342519

theorem tailTrace_5839960 : CollatzResearch.WordTrace tailWord_5839960 prefixEnd_5839960 2998706483031076363342519 := by
  unfold tailWord_5839960
  simp only [CollatzResearch.WordTrace]
  refine ⟨106500419961414890303586667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142000559948553187071448889 106500419961414890303586667)
  ·
    refine ⟨159750629942122335455380001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106500419961414890303586667 159750629942122335455380001)
    ·
      refine ⟨119812972456591751591535001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159750629942122335455380001 119812972456591751591535001)
      ·
        refine ⟨89859729342443813693651251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119812972456591751591535001 89859729342443813693651251)
        ·
          refine ⟨134789594013665720540476877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89859729342443813693651251 134789594013665720540476877)
          ·
            refine ⟨50546097755124645202678829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134789594013665720540476877 50546097755124645202678829)
            ·
              refine ⟨18954786658171741951004561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50546097755124645202678829 18954786658171741951004561)
              ·
                refine ⟨14216089993628806463253421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18954786658171741951004561 14216089993628806463253421)
                ·
                  refine ⟨5331033747610802423720033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14216089993628806463253421 5331033747610802423720033)
                  ·
                    refine ⟨3998275310708101817790025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331033747610802423720033 3998275310708101817790025)
                    ·
                      refine ⟨2998706483031076363342519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998275310708101817790025 2998706483031076363342519)
                      ·
                        rfl

theorem cell23_5839960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_5839960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839960 prefixEnd_5839960 := by exact prefixLift 5839960
  have htrace : WordTrace (prefixWord ++ tailWord_5839960) baseStart_5839960 baseEnd_5839960 := by
    simpa [prefixWord, tailWord_5839960, baseEnd_5839960] using wordTrace_append hprefix tailTrace_5839960
  have hstable : (prefixWord ++ tailWord_5839960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839960).length < 2 ^ (prefixWord ++ tailWord_5839960).sum := by decide
  have hdescent : baseEnd_5839960 < baseStart_5839960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5839977 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 1, 2, 2]
def baseStart_5839977 : Nat := 118140960795 + 5839977 * 2 ^ 59
def prefixEnd_5839977 : Nat := 4983230072969 + 3 ^ 40 * 5839977 * 2
def baseEnd_5839977 : Nat := 2998715212202202796829941

theorem tailTrace_5839977 : CollatzResearch.WordTrace tailWord_5839977 prefixEnd_5839977 2998715212202202796829941 := by
  unfold tailWord_5839977
  simp only [CollatzResearch.WordTrace]
  refine ⟨213001459963768192510542185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142000973309178795007028123 213001459963768192510542185)
  ·
    refine ⟨159751094972826144382906639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213001459963768192510542185 159751094972826144382906639)
    ·
      refine ⟨239626642459239216574359959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159751094972826144382906639 239626642459239216574359959)
      ·
        refine ⟨359439963688858824861539939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239626642459239216574359959 359439963688858824861539939)
        ·
          refine ⟨539159945533288237292309909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359439963688858824861539939 539159945533288237292309909)
          ·
            refine ⟨25273122446872886123077027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 539159945533288237292309909 25273122446872886123077027)
            ·
              refine ⟨37909683670309329184615541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25273122446872886123077027 37909683670309329184615541)
              ·
                refine ⟨3554032844091499611057707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37909683670309329184615541 3554032844091499611057707)
                ·
                  refine ⟨5331049266137249416586561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554032844091499611057707 5331049266137249416586561)
                  ·
                    refine ⟨3998286949602937062439921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331049266137249416586561 3998286949602937062439921)
                    ·
                      refine ⟨2998715212202202796829941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998286949602937062439921 2998715212202202796829941)
                      ·
                        rfl

theorem cell23_5839977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 2, 2].length) (baseStart_5839977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5839977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5839977 prefixEnd_5839977 := by exact prefixLift 5839977
  have htrace : WordTrace (prefixWord ++ tailWord_5839977) baseStart_5839977 baseEnd_5839977 := by
    simpa [prefixWord, tailWord_5839977, baseEnd_5839977] using wordTrace_append hprefix tailTrace_5839977
  have hstable : (prefixWord ++ tailWord_5839977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5839977).length < 2 ^ (prefixWord ++ tailWord_5839977).sum := by decide
  have hdescent : baseEnd_5839977 < baseStart_5839977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5839977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840056 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 7]
def baseStart_5840056 : Nat := 118140960795 + 5840056 * 2 ^ 59
def prefixEnd_5840056 : Nat := 4983230072969 + 3 ^ 40 * 5840056 * 2
def baseEnd_5840056 : Nat := 333195086352656443082453

theorem tailTrace_5840056 : CollatzResearch.WordTrace tailWord_5840056 prefixEnd_5840056 333195086352656443082453 := by
  unfold tailWord_5840056
  simp only [CollatzResearch.WordTrace]
  refine ⟨106502170665240994501334011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142002894220321326001778681 106502170665240994501334011)
  ·
    refine ⟨159753255997861491752001017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106502170665240994501334011 159753255997861491752001017)
    ·
      refine ⟨119814941998396118814000763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159753255997861491752001017 119814941998396118814000763)
      ·
        refine ⟨179722412997594178221001145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119814941998396118814000763 179722412997594178221001145)
        ·
          refine ⟨134791809748195633665750859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179722412997594178221001145 134791809748195633665750859)
          ·
            refine ⟨202187714622293450498626289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134791809748195633665750859 202187714622293450498626289)
            ·
              refine ⟨151640785966720087873969717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202187714622293450498626289 151640785966720087873969717)
              ·
                refine ⟨14216323684380008238184661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151640785966720087873969717 14216323684380008238184661)
                ·
                  refine ⟨333195086352656443082453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14216323684380008238184661 333195086352656443082453)
                  ·
                    rfl

theorem cell23_5840056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_5840056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840056 prefixEnd_5840056 := by exact prefixLift 5840056
  have htrace : WordTrace (prefixWord ++ tailWord_5840056) baseStart_5840056 baseEnd_5840056 := by
    simpa [prefixWord, tailWord_5840056, baseEnd_5840056] using wordTrace_append hprefix tailTrace_5840056
  have hstable : (prefixWord ++ tailWord_5840056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840056).length < 2 ^ (prefixWord ++ tailWord_5840056).sum := by decide
  have hdescent : baseEnd_5840056 < baseStart_5840056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840084 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5840084 : Nat := 118140960795 + 5840084 * 2 ^ 59
def prefixEnd_5840084 : Nat := 4983230072969 + 3 ^ 40 * 5840084 * 2
def baseEnd_5840084 : Nat := 2998770154632233878191949

theorem tailTrace_5840084 : CollatzResearch.WordTrace tailWord_5840084 prefixEnd_5840084 2998770154632233878191949 := by
  unfold tailWord_5840084
  simp only [CollatzResearch.WordTrace]
  refine ⟨106502681287190274892343653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142003575049587033189791537 106502681287190274892343653)
  ·
    refine ⟨19969252741348176542314435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106502681287190274892343653 19969252741348176542314435)
    ·
      refine ⟨29953879112022264813471653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19969252741348176542314435 29953879112022264813471653)
      ·
        refine ⟨5616352333504174652525935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29953879112022264813471653 5616352333504174652525935)
        ·
          refine ⟨8424528500256261978788903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616352333504174652525935 8424528500256261978788903)
          ·
            refine ⟨12636792750384392968183355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424528500256261978788903 12636792750384392968183355)
            ·
              refine ⟨18955189125576589452275033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636792750384392968183355 18955189125576589452275033)
              ·
                refine ⟨14216391844182442089206275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18955189125576589452275033 14216391844182442089206275)
                ·
                  refine ⟨21324587766273663133809413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14216391844182442089206275 21324587766273663133809413)
                  ·
                    refine ⟨3998360206176311837589265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21324587766273663133809413 3998360206176311837589265)
                    ·
                      refine ⟨2998770154632233878191949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998360206176311837589265 2998770154632233878191949)
                      ·
                        rfl

theorem cell23_5840084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5840084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840084 prefixEnd_5840084 := by exact prefixLift 5840084
  have htrace : WordTrace (prefixWord ++ tailWord_5840084) baseStart_5840084 baseEnd_5840084 := by
    simpa [prefixWord, tailWord_5840084, baseEnd_5840084] using wordTrace_append hprefix tailTrace_5840084
  have hstable : (prefixWord ++ tailWord_5840084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840084).length < 2 ^ (prefixWord ++ tailWord_5840084).sum := by decide
  have hdescent : baseEnd_5840084 < baseStart_5840084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840107 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 5]
def baseStart_5840107 : Nat := 118140960795 + 5840107 * 2 ^ 59
def prefixEnd_5840107 : Nat := 4983230072969 + 3 ^ 40 * 5840107 * 2
def baseEnd_5840107 : Nat := 333197996076365254244927

theorem tailTrace_5840107 : CollatzResearch.WordTrace tailWord_5840107 prefixEnd_5840107 333197996076365254244927 := by
  unfold tailWord_5840107
  simp only [CollatzResearch.WordTrace]
  refine ⟨213006201453297224712774575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142004134302198149808516383 213006201453297224712774575)
  ·
    refine ⟨319509302179945837069161863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213006201453297224712774575 319509302179945837069161863)
    ·
      refine ⟨479263953269918755603742795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319509302179945837069161863 479263953269918755603742795)
      ·
        refine ⟨718895929904878133405614193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479263953269918755603742795 718895929904878133405614193)
        ·
          refine ⟨539171947428658600054210645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718895929904878133405614193 539171947428658600054210645)
          ·
            refine ⟨6318421258929592969385281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 539171947428658600054210645 6318421258929592969385281)
            ·
              refine ⟨4738815944197194727038961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6318421258929592969385281 4738815944197194727038961)
              ·
                refine ⟨3554111958147896045279221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738815944197194727038961 3554111958147896045279221)
                ·
                  refine ⟨333197996076365254244927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3554111958147896045279221 333197996076365254244927)
                  ·
                    rfl

theorem cell23_5840107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 5].length) (baseStart_5840107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840107 prefixEnd_5840107 := by exact prefixLift 5840107
  have htrace : WordTrace (prefixWord ++ tailWord_5840107) baseStart_5840107 baseEnd_5840107 := by
    simpa [prefixWord, tailWord_5840107, baseEnd_5840107] using wordTrace_append hprefix tailTrace_5840107
  have hstable : (prefixWord ++ tailWord_5840107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840107).length < 2 ^ (prefixWord ++ tailWord_5840107).sum := by decide
  have hdescent : baseEnd_5840107 < baseStart_5840107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840110 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_5840110 : Nat := 118140960795 + 5840110 * 2 ^ 59
def prefixEnd_5840110 : Nat := 4983230072969 + 3 ^ 40 * 5840110 * 2
def baseEnd_5840110 : Nat := 2998783505129250776466829

theorem tailTrace_5840110 : CollatzResearch.WordTrace tailWord_5840110 prefixEnd_5840110 2998783505129250776466829 := by
  unfold tailWord_5840110
  simp only [CollatzResearch.WordTrace]
  refine ⟨26625788859035794528141723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142004207248190904150089189 26625788859035794528141723)
  ·
    refine ⟨39938683288553691792212585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26625788859035794528141723 39938683288553691792212585)
    ·
      refine ⟨29954012466415268844159439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39938683288553691792212585 29954012466415268844159439)
      ·
        refine ⟨44931018699622903266239159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29954012466415268844159439 44931018699622903266239159)
        ·
          refine ⟨67396528049434354899358739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44931018699622903266239159 67396528049434354899358739)
          ·
            refine ⟨101094792074151532349038109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67396528049434354899358739 101094792074151532349038109)
            ·
              refine ⟨37910547027806824630889291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101094792074151532349038109 37910547027806824630889291)
              ·
                refine ⟨56865820541710236946333937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37910547027806824630889291 56865820541710236946333937)
                ·
                  refine ⟨42649365406282677709750453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56865820541710236946333937 42649365406282677709750453)
                  ·
                    refine ⟨3998378006839001035289105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42649365406282677709750453 3998378006839001035289105)
                    ·
                      refine ⟨2998783505129250776466829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998378006839001035289105 2998783505129250776466829)
                      ·
                        rfl

theorem cell23_5840110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_5840110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840110 prefixEnd_5840110 := by exact prefixLift 5840110
  have htrace : WordTrace (prefixWord ++ tailWord_5840110) baseStart_5840110 baseEnd_5840110 := by
    simpa [prefixWord, tailWord_5840110, baseEnd_5840110] using wordTrace_append hprefix tailTrace_5840110
  have hstable : (prefixWord ++ tailWord_5840110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840110).length < 2 ^ (prefixWord ++ tailWord_5840110).sum := by decide
  have hdescent : baseEnd_5840110 < baseStart_5840110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840140 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_5840140 : Nat := 118140960795 + 5840140 * 2 ^ 59
def prefixEnd_5840140 : Nat := 4983230072969 + 3 ^ 40 * 5840140 * 2
def baseEnd_5840140 : Nat := 2998798909548885659091691

theorem tailTrace_5840140 : CollatzResearch.WordTrace tailWord_5840140 prefixEnd_5840140 2998798909548885659091691 := by
  unfold tailWord_5840140
  simp only [CollatzResearch.WordTrace]
  refine ⟨106503702531088835674362937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142004936708118447565817249 106503702531088835674362937)
  ·
    refine ⟨79877776898316626755772203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106503702531088835674362937 79877776898316626755772203)
    ·
      refine ⟨119816665347474940133658305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79877776898316626755772203 119816665347474940133658305)
      ·
        refine ⟨89862499010606205100243729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119816665347474940133658305 89862499010606205100243729)
        ·
          refine ⟨67396874257954653825182797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89862499010606205100243729 67396874257954653825182797)
          ·
            refine ⟨25273827846732995184443549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67396874257954653825182797 25273827846732995184443549)
            ·
              refine ⟨9477685442524873194166331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25273827846732995184443549 9477685442524873194166331)
              ·
                refine ⟨14216528163787309791249497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9477685442524873194166331 14216528163787309791249497)
                ·
                  refine ⟨10662396122840482343437123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14216528163787309791249497 10662396122840482343437123)
                  ·
                    refine ⟨15993594184260723515155685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10662396122840482343437123 15993594184260723515155685)
                    ·
                      refine ⟨2998798909548885659091691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15993594184260723515155685 2998798909548885659091691)
                      ·
                        rfl

theorem cell23_5840140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_5840140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840140 prefixEnd_5840140 := by exact prefixLift 5840140
  have htrace : WordTrace (prefixWord ++ tailWord_5840140) baseStart_5840140 baseEnd_5840140 := by
    simpa [prefixWord, tailWord_5840140, baseEnd_5840140] using wordTrace_append hprefix tailTrace_5840140
  have hstable : (prefixWord ++ tailWord_5840140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840140).length < 2 ^ (prefixWord ++ tailWord_5840140).sum := by decide
  have hdescent : baseEnd_5840140 < baseStart_5840140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840157 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5840157 : Nat := 118140960795 + 5840157 * 2 ^ 59
def prefixEnd_5840157 : Nat := 4983230072969 + 3 ^ 40 * 5840157 * 2
def baseEnd_5840157 : Nat := 2998807638720012092579113

theorem tailTrace_5840157 : CollatzResearch.WordTrace tailWord_5840157 prefixEnd_5840157 2998807638720012092579113 := by
  unfold tailWord_5840157
  simp only [CollatzResearch.WordTrace]
  refine ⟨213008025103116083252094725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142005350068744055501396483 213008025103116083252094725)
  ·
    refine ⟨39939004706834265609767761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213008025103116083252094725 39939004706834265609767761)
    ·
      refine ⟨29954253530125699207325821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39939004706834265609767761 29954253530125699207325821)
      ·
        refine ⟨11232845073797137202747183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29954253530125699207325821 11232845073797137202747183)
        ·
          refine ⟨16849267610695705804120775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11232845073797137202747183 16849267610695705804120775)
          ·
            refine ⟨25273901416043558706181163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16849267610695705804120775 25273901416043558706181163)
            ·
              refine ⟨37910852124065338059271745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25273901416043558706181163 37910852124065338059271745)
              ·
                refine ⟨28433139093049003544453809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37910852124065338059271745 28433139093049003544453809)
                ·
                  refine ⟨21324854319786752658340357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28433139093049003544453809 21324854319786752658340357)
                  ·
                    refine ⟨3998410184960016123438817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21324854319786752658340357 3998410184960016123438817)
                    ·
                      refine ⟨2998807638720012092579113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998410184960016123438817 2998807638720012092579113)
                      ·
                        rfl

theorem cell23_5840157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5840157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840157 prefixEnd_5840157 := by exact prefixLift 5840157
  have htrace : WordTrace (prefixWord ++ tailWord_5840157) baseStart_5840157 baseEnd_5840157 := by
    simpa [prefixWord, tailWord_5840157, baseEnd_5840157] using wordTrace_append hprefix tailTrace_5840157
  have hstable : (prefixWord ++ tailWord_5840157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840157).length < 2 ^ (prefixWord ++ tailWord_5840157).sum := by decide
  have hdescent : baseEnd_5840157 < baseStart_5840157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840163 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 8]
def baseStart_5840163 : Nat := 118140960795 + 5840163 * 2 ^ 59
def prefixEnd_5840163 : Nat := 4983230072969 + 3 ^ 40 * 5840163 * 2
def baseEnd_5840163 : Nat := 333201191067104341011565

theorem tailTrace_5840163 : CollatzResearch.WordTrace tailWord_5840163 prefixEnd_5840163 333201191067104341011565 := by
  unfold tailWord_5840163
  simp only [CollatzResearch.WordTrace]
  refine ⟨213008243941094346276813143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142005495960729564184542095 213008243941094346276813143)
  ·
    refine ⟨319512365911641519415219715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213008243941094346276813143 319512365911641519415219715)
    ·
      refine ⟨479268548867462279122829573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319512365911641519415219715 479268548867462279122829573)
      ·
        refine ⟨89862852912649177335530545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479268548867462279122829573 89862852912649177335530545)
        ·
          refine ⟨67397139684486883001647909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89862852912649177335530545 67397139684486883001647909)
          ·
            refine ⟨12636963690841290562808983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67397139684486883001647909 12636963690841290562808983)
            ·
              refine ⟨18955445536261935844213475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636963690841290562808983 18955445536261935844213475)
              ·
                refine ⟨28433168304392903766320213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18955445536261935844213475 28433168304392903766320213)
                ·
                  refine ⟨333201191067104341011565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28433168304392903766320213 333201191067104341011565)
                  ·
                    rfl

theorem cell23_5840163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 8].length) (baseStart_5840163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840163 prefixEnd_5840163 := by exact prefixLift 5840163
  have htrace : WordTrace (prefixWord ++ tailWord_5840163) baseStart_5840163 baseEnd_5840163 := by
    simpa [prefixWord, tailWord_5840163, baseEnd_5840163] using wordTrace_append hprefix tailTrace_5840163
  have hstable : (prefixWord ++ tailWord_5840163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840163).length < 2 ^ (prefixWord ++ tailWord_5840163).sum := by decide
  have hdescent : baseEnd_5840163 < baseStart_5840163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840190 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_5840190 : Nat := 118140960795 + 5840190 * 2 ^ 59
def prefixEnd_5840190 : Nat := 4983230072969 + 3 ^ 40 * 5840190 * 2
def baseEnd_5840190 : Nat := 2998824583581610463466461

theorem tailTrace_5840190 : CollatzResearch.WordTrace tailWord_5840190 prefixEnd_5840190 2998824583581610463466461 := by
  unfold tailWord_5840190
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626153588999566236005753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142006152474664353258697349 26626153588999566236005753)
  ·
    refine ⟨19969615191749674677004315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26626153588999566236005753 19969615191749674677004315)
    ·
      refine ⟨29954422787624512015506473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19969615191749674677004315 29954422787624512015506473)
      ·
        refine ⟨22465817090718384011629855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29954422787624512015506473 22465817090718384011629855)
        ·
          refine ⟨33698725636077576017444783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22465817090718384011629855 33698725636077576017444783)
          ·
            refine ⟨50548088454116364026167175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33698725636077576017444783 50548088454116364026167175)
            ·
              refine ⟨75822132681174546039250763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50548088454116364026167175 75822132681174546039250763)
              ·
                refine ⟨113733199021761819058876145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75822132681174546039250763 113733199021761819058876145)
                ·
                  refine ⟨85299899266321364294157109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113733199021761819058876145 85299899266321364294157109)
                  ·
                    refine ⟨7996865556217627902577229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85299899266321364294157109 7996865556217627902577229)
                    ·
                      refine ⟨2998824583581610463466461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996865556217627902577229 2998824583581610463466461)
                      ·
                        rfl

theorem cell23_5840190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_5840190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840190 prefixEnd_5840190 := by exact prefixLift 5840190
  have htrace : WordTrace (prefixWord ++ tailWord_5840190) baseStart_5840190 baseEnd_5840190 := by
    simpa [prefixWord, tailWord_5840190, baseEnd_5840190] using wordTrace_append hprefix tailTrace_5840190
  have hstable : (prefixWord ++ tailWord_5840190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840190).length < 2 ^ (prefixWord ++ tailWord_5840190).sum := by decide
  have hdescent : baseEnd_5840190 < baseStart_5840190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840224 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3]
def baseStart_5840224 : Nat := 118140960795 + 5840224 * 2 ^ 59
def prefixEnd_5840224 : Nat := 4983230072969 + 3 ^ 40 * 5840224 * 2
def baseEnd_5840224 : Nat := 2998842041923863330441305

theorem tailTrace_5840224 : CollatzResearch.WordTrace tailWord_5840224 prefixEnd_5840224 2998842041923863330441305 := by
  unfold tailWord_5840224
  simp only [CollatzResearch.WordTrace]
  refine ⟨106505234396936676847391863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142006979195915569129855817 106505234396936676847391863)
  ·
    refine ⟨159757851595405015271087795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106505234396936676847391863 159757851595405015271087795)
    ·
      refine ⟨239636777393107522906631693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159757851595405015271087795 239636777393107522906631693)
      ·
        refine ⟨89863791522415321089986885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239636777393107522906631693 89863791522415321089986885)
        ·
          refine ⟨16849460910452872704372541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89863791522415321089986885 16849460910452872704372541)
          ·
            refine ⟨6318547841419827264139703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16849460910452872704372541 6318547841419827264139703)
            ·
              refine ⟨9477821762129740896209555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318547841419827264139703 9477821762129740896209555)
              ·
                refine ⟨14216732643194611344314333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9477821762129740896209555 14216732643194611344314333)
                ·
                  refine ⟨5331274741197979254117875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14216732643194611344314333 5331274741197979254117875)
                  ·
                    refine ⟨7996912111796968881176813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331274741197979254117875 7996912111796968881176813)
                    ·
                      refine ⟨2998842041923863330441305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996912111796968881176813 2998842041923863330441305)
                      ·
                        rfl

theorem cell23_5840224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_5840224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840224 prefixEnd_5840224 := by exact prefixLift 5840224
  have htrace : WordTrace (prefixWord ++ tailWord_5840224) baseStart_5840224 baseEnd_5840224 := by
    simpa [prefixWord, tailWord_5840224, baseEnd_5840224] using wordTrace_append hprefix tailTrace_5840224
  have hstable : (prefixWord ++ tailWord_5840224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840224).length < 2 ^ (prefixWord ++ tailWord_5840224).sum := by decide
  have hdescent : baseEnd_5840224 < baseStart_5840224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840233 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_5840233 : Nat := 118140960795 + 5840233 * 2 ^ 59
def prefixEnd_5840233 : Nat := 4983230072969 + 3 ^ 40 * 5840233 * 2
def baseEnd_5840233 : Nat := 2998846663249753795228763

theorem tailTrace_5840233 : CollatzResearch.WordTrace tailWord_5840233 prefixEnd_5840233 2998846663249753795228763 := by
  unfold tailWord_5840233
  simp only [CollatzResearch.WordTrace]
  refine ⟨213010797050840748231861353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142007198033893832154574235 213010797050840748231861353)
  ·
    refine ⟨159758097788130561173896015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213010797050840748231861353 159758097788130561173896015)
    ·
      refine ⟨239637146682195841760844023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159758097788130561173896015 239637146682195841760844023)
      ·
        refine ⟨359455720023293762641266035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239637146682195841760844023 359455720023293762641266035)
        ·
          refine ⟨539183580034940643961899053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359455720023293762641266035 539183580034940643961899053)
          ·
            refine ⟨202193842513102741485712145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539183580034940643961899053 202193842513102741485712145)
            ·
              refine ⟨151645381884827056114284109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202193842513102741485712145 151645381884827056114284109)
              ·
                refine ⟨56867018206810146042856541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151645381884827056114284109 56867018206810146042856541)
                ·
                  refine ⟨21325131827553804766071203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56867018206810146042856541 21325131827553804766071203)
                  ·
                    refine ⟨31987697741330707149106805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21325131827553804766071203 31987697741330707149106805)
                    ·
                      refine ⟨2998846663249753795228763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31987697741330707149106805 2998846663249753795228763)
                      ·
                        rfl

theorem cell23_5840233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_5840233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840233 prefixEnd_5840233 := by exact prefixLift 5840233
  have htrace : WordTrace (prefixWord ++ tailWord_5840233) baseStart_5840233 baseEnd_5840233 := by
    simpa [prefixWord, tailWord_5840233, baseEnd_5840233] using wordTrace_append hprefix tailTrace_5840233
  have hstable : (prefixWord ++ tailWord_5840233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840233).length < 2 ^ (prefixWord ++ tailWord_5840233).sum := by decide
  have hdescent : baseEnd_5840233 < baseStart_5840233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840247 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_5840247 : Nat := 118140960795 + 5840247 * 2 ^ 59
def prefixEnd_5840247 : Nat := 4983230072969 + 3 ^ 40 * 5840247 * 2
def baseEnd_5840247 : Nat := 2998853851978916740453699

theorem tailTrace_5840247 : CollatzResearch.WordTrace tailWord_5840247 prefixEnd_5840247 2998853851978916740453699 := by
  unfold tailWord_5840247
  simp only [CollatzResearch.WordTrace]
  refine ⟨213011307672790028622870995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142007538448526685748580663 213011307672790028622870995)
  ·
    refine ⟨319516961509185042934306493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213011307672790028622870995 319516961509185042934306493)
    ·
      refine ⟨119818860565944391100364935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319516961509185042934306493 119818860565944391100364935)
      ·
        refine ⟨179728290848916586650547403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119818860565944391100364935 179728290848916586650547403)
        ·
          refine ⟨269592436273374879975821105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179728290848916586650547403 269592436273374879975821105)
          ·
            refine ⟨202194327205031159981865829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269592436273374879975821105 202194327205031159981865829)
            ·
              refine ⟨37911436350943342496599843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202194327205031159981865829 37911436350943342496599843)
              ·
                refine ⟨56867154526415013744899765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37911436350943342496599843 56867154526415013744899765)
                ·
                  refine ⟨5331295736851407538584353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56867154526415013744899765 5331295736851407538584353)
                  ·
                    refine ⟨3998471802638555653938265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331295736851407538584353 3998471802638555653938265)
                    ·
                      refine ⟨2998853851978916740453699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998471802638555653938265 2998853851978916740453699)
                      ·
                        rfl

theorem cell23_5840247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_5840247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840247 prefixEnd_5840247 := by exact prefixLift 5840247
  have htrace : WordTrace (prefixWord ++ tailWord_5840247) baseStart_5840247 baseEnd_5840247 := by
    simpa [prefixWord, tailWord_5840247, baseEnd_5840247] using wordTrace_append hprefix tailTrace_5840247
  have hstable : (prefixWord ++ tailWord_5840247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840247).length < 2 ^ (prefixWord ++ tailWord_5840247).sum := by decide
  have hdescent : baseEnd_5840247 < baseStart_5840247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840250 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_5840250 : Nat := 118140960795 + 5840250 * 2 ^ 59
def prefixEnd_5840250 : Nat := 4983230072969 + 3 ^ 40 * 5840250 * 2
def baseEnd_5840250 : Nat := 2998855392420880228716185

theorem tailTrace_5840250 : CollatzResearch.WordTrace tailWord_5840250 prefixEnd_5840250 2998855392420880228716185 := by
  unfold tailWord_5840250
  simp only [CollatzResearch.WordTrace]
  refine ⟨53252854272944790033807551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142007611394519440090153469 53252854272944790033807551)
  ·
    refine ⟨79879281409417185050711327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53252854272944790033807551 79879281409417185050711327)
    ·
      refine ⟨119818922114125777576066991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79879281409417185050711327 119818922114125777576066991)
      ·
        refine ⟨179728383171188666364100487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119818922114125777576066991 179728383171188666364100487)
        ·
          refine ⟨269592574756782999546150731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179728383171188666364100487 269592574756782999546150731)
          ·
            refine ⟨404388862135174499319226097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269592574756782999546150731 404388862135174499319226097)
            ·
              refine ⟨303291646601380874489419573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404388862135174499319226097 303291646601380874489419573)
              ·
                refine ⟨28433591868879456983383085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303291646601380874489419573 28433591868879456983383085)
                ·
                  refine ⟨10662596950829796368768657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28433591868879456983383085 10662596950829796368768657)
                  ·
                    refine ⟨7996947713122347276576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10662596950829796368768657 7996947713122347276576493)
                    ·
                      refine ⟨2998855392420880228716185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7996947713122347276576493 2998855392420880228716185)
                      ·
                        rfl

theorem cell23_5840250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_5840250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840250 prefixEnd_5840250 := by exact prefixLift 5840250
  have htrace : WordTrace (prefixWord ++ tailWord_5840250) baseStart_5840250 baseEnd_5840250 := by
    simpa [prefixWord, tailWord_5840250, baseEnd_5840250] using wordTrace_append hprefix tailTrace_5840250
  have hstable : (prefixWord ++ tailWord_5840250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840250).length < 2 ^ (prefixWord ++ tailWord_5840250).sum := by decide
  have hdescent : baseEnd_5840250 < baseStart_5840250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840253 : List Nat := [1, 4, 1, 1, 2, 2, 1, 11]
def baseStart_5840253 : Nat := 118140960795 + 5840253 * 2 ^ 59
def prefixEnd_5840253 : Nat := 4983230072969 + 3 ^ 40 * 5840253 * 2
def baseEnd_5840253 : Nat := 111068775291216433962173

theorem tailTrace_5840253 : CollatzResearch.WordTrace tailWord_5840253 prefixEnd_5840253 111068775291216433962173 := by
  unfold tailWord_5840253
  simp only [CollatzResearch.WordTrace]
  refine ⟨213011526510768291647589413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142007684340512194431726275 213011526510768291647589413)
  ·
    refine ⟨39939661220769054683923015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213011526510768291647589413 39939661220769054683923015)
    ·
      refine ⟨59909491831153582025884523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39939661220769054683923015 59909491831153582025884523)
      ·
        refine ⟨89864237746730373038826785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59909491831153582025884523 89864237746730373038826785)
        ·
          refine ⟨67398178310047779779120089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89864237746730373038826785 67398178310047779779120089)
          ·
            refine ⟨50548633732535834834340067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67398178310047779779120089 50548633732535834834340067)
            ·
              refine ⟨75822950598803752251510101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50548633732535834834340067 75822950598803752251510101)
              ·
                refine ⟨111068775291216433962173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75822950598803752251510101 111068775291216433962173)
                ·
                  rfl

theorem cell23_5840253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 11].length) (baseStart_5840253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840253 prefixEnd_5840253 := by exact prefixLift 5840253
  have htrace : WordTrace (prefixWord ++ tailWord_5840253) baseStart_5840253 baseEnd_5840253 := by
    simpa [prefixWord, tailWord_5840253, baseEnd_5840253] using wordTrace_append hprefix tailTrace_5840253
  have hstable : (prefixWord ++ tailWord_5840253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840253).length < 2 ^ (prefixWord ++ tailWord_5840253).sum := by decide
  have hdescent : baseEnd_5840253 < baseStart_5840253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840257 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_5840257 : Nat := 118140960795 + 5840257 * 2 ^ 59
def prefixEnd_5840257 : Nat := 4983230072969 + 3 ^ 40 * 5840257 * 2
def baseEnd_5840257 : Nat := 999619662261820567109551

theorem tailTrace_5840257 : CollatzResearch.WordTrace tailWord_5840257 prefixEnd_5840257 999619662261820567109551 := by
  unfold tailWord_5840257
  simp only [CollatzResearch.WordTrace]
  refine ⟨213011672402753800330735025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142007781601835866887156683 213011672402753800330735025)
  ·
    refine ⟨159758754302065350248051269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213011672402753800330735025 159758754302065350248051269)
    ·
      refine ⟨29954766431637253171509613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159758754302065350248051269 29954766431637253171509613)
      ·
        refine ⟨11233037411863969939316105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29954766431637253171509613 11233037411863969939316105)
        ·
          refine ⟨8424778058897977454487079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11233037411863969939316105 8424778058897977454487079)
          ·
            refine ⟨12637167088346966181730619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424778058897977454487079 12637167088346966181730619)
            ·
              refine ⟨18955750632520449272595929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12637167088346966181730619 18955750632520449272595929)
              ·
                refine ⟨14216812974390336954446947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18955750632520449272595929 14216812974390336954446947)
                ·
                  refine ⟨21325219461585505431670421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14216812974390336954446947 21325219461585505431670421)
                  ·
                    refine ⟨999619662261820567109551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21325219461585505431670421 999619662261820567109551)
                    ·
                      rfl

theorem cell23_5840257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_5840257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840257 prefixEnd_5840257 := by exact prefixLift 5840257
  have htrace : WordTrace (prefixWord ++ tailWord_5840257) baseStart_5840257 baseEnd_5840257 := by
    simpa [prefixWord, tailWord_5840257, baseEnd_5840257] using wordTrace_append hprefix tailTrace_5840257
  have hstable : (prefixWord ++ tailWord_5840257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840257).length < 2 ^ (prefixWord ++ tailWord_5840257).sum := by decide
  have hdescent : baseEnd_5840257 < baseStart_5840257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840260 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5840260 : Nat := 118140960795 + 5840260 * 2 ^ 59
def prefixEnd_5840260 : Nat := 4983230072969 + 3 ^ 40 * 5840260 * 2
def baseEnd_5840260 : Nat := 2998860527227425189591139

theorem tailTrace_5840260 : CollatzResearch.WordTrace tailWord_5840260 prefixEnd_5840260 2998860527227425189591139 := by
  unfold tailWord_5840260
  simp only [CollatzResearch.WordTrace]
  refine ⟨106505890910871465921547117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142007854547828621228729489 106505890910871465921547117)
  ·
    refine ⟨39939709091576799720580169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106505890910871465921547117 39939709091576799720580169)
    ·
      refine ⟨29954781818682599790435127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39939709091576799720580169 29954781818682599790435127)
      ·
        refine ⟨44932172728023899685652691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29954781818682599790435127 44932172728023899685652691)
        ·
          refine ⟨67398259092035849528479037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44932172728023899685652691 67398259092035849528479037)
          ·
            refine ⟨25274347159513443573179639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67398259092035849528479037 25274347159513443573179639)
            ·
              refine ⟨37911520739270165359769459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25274347159513443573179639 37911520739270165359769459)
              ·
                refine ⟨56867281108905248039654189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37911520739270165359769459 56867281108905248039654189)
                ·
                  refine ⟨21325230415839468014870321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56867281108905248039654189 21325230415839468014870321)
                  ·
                    refine ⟨15993922811879601011152741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21325230415839468014870321 15993922811879601011152741)
                    ·
                      refine ⟨2998860527227425189591139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15993922811879601011152741 2998860527227425189591139)
                      ·
                        rfl

theorem cell23_5840260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5840260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840260 prefixEnd_5840260 := by exact prefixLift 5840260
  have htrace : WordTrace (prefixWord ++ tailWord_5840260) baseStart_5840260 baseEnd_5840260 := by
    simpa [prefixWord, tailWord_5840260, baseEnd_5840260] using wordTrace_append hprefix tailTrace_5840260
  have hstable : (prefixWord ++ tailWord_5840260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840260).length < 2 ^ (prefixWord ++ tailWord_5840260).sum := by decide
  have hdescent : baseEnd_5840260 < baseStart_5840260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840264 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5840264 : Nat := 118140960795 + 5840264 * 2 ^ 59
def prefixEnd_5840264 : Nat := 4983230072969 + 3 ^ 40 * 5840264 * 2
def baseEnd_5840264 : Nat := 2998862581150043173941121

theorem tailTrace_5840264 : CollatzResearch.WordTrace tailWord_5840264 prefixEnd_5840264 2998862581150043173941121 := by
  unfold tailWord_5840264
  simp only [CollatzResearch.WordTrace]
  refine ⟨106505963856864220263119923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142007951809152293684159897 106505963856864220263119923)
  ·
    refine ⟨159758945785296330394679885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106505963856864220263119923 159758945785296330394679885)
    ·
      refine ⟨59909604669486123898004957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159758945785296330394679885 59909604669486123898004957)
      ·
        refine ⟨22466101751057296461751859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59909604669486123898004957 22466101751057296461751859)
        ·
          refine ⟨33699152626585944692627789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22466101751057296461751859 33699152626585944692627789)
          ·
            refine ⟨12637182234969729259735421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33699152626585944692627789 12637182234969729259735421)
            ·
              refine ⟨4738943338113648472400783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12637182234969729259735421 4738943338113648472400783)
              ·
                refine ⟨7108415007170472708601175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738943338113648472400783 7108415007170472708601175)
                ·
                  refine ⟨10662622510755709062901763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7108415007170472708601175 10662622510755709062901763)
                  ·
                    refine ⟨15993933766133563594352645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10662622510755709062901763 15993933766133563594352645)
                    ·
                      refine ⟨2998862581150043173941121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15993933766133563594352645 2998862581150043173941121)
                      ·
                        rfl

theorem cell23_5840264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5840264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840264 prefixEnd_5840264 := by exact prefixLift 5840264
  have htrace : WordTrace (prefixWord ++ tailWord_5840264) baseStart_5840264 baseEnd_5840264 := by
    simpa [prefixWord, tailWord_5840264, baseEnd_5840264] using wordTrace_append hprefix tailTrace_5840264
  have hstable : (prefixWord ++ tailWord_5840264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840264).length < 2 ^ (prefixWord ++ tailWord_5840264).sum := by decide
  have hdescent : baseEnd_5840264 < baseStart_5840264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840270 : List Nat := [4, 1, 1, 4, 2, 11]
def baseStart_5840270 : Nat := 118140960795 + 5840270 * 2 ^ 59
def prefixEnd_5840270 : Nat := 4983230072969 + 3 ^ 40 * 5840270 * 2
def baseEnd_5840270 : Nat := 12341010954872305145951

theorem tailTrace_5840270 : CollatzResearch.WordTrace tailWord_5840270 prefixEnd_5840270 12341010954872305145951 := by
  unfold tailWord_5840270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26626518318963337943869783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142008097701137802367305509 26626518318963337943869783)
  ·
    refine ⟨39939777478445006915804675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26626518318963337943869783 39939777478445006915804675)
    ·
      refine ⟨59909666217667510373707013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39939777478445006915804675 59909666217667510373707013)
      ·
        refine ⟨11233062415812658195070065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59909666217667510373707013 11233062415812658195070065)
        ·
          refine ⟨8424796811859493646302549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11233062415812658195070065 8424796811859493646302549)
          ·
            refine ⟨12341010954872305145951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8424796811859493646302549 12341010954872305145951)
            ·
              rfl

theorem cell23_5840270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 11].length) (baseStart_5840270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840270 prefixEnd_5840270 := by exact prefixLift 5840270
  have htrace : WordTrace (prefixWord ++ tailWord_5840270) baseStart_5840270 baseEnd_5840270 := by
    simpa [prefixWord, tailWord_5840270, baseEnd_5840270] using wordTrace_append hprefix tailTrace_5840270
  have hstable : (prefixWord ++ tailWord_5840270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840270).length < 2 ^ (prefixWord ++ tailWord_5840270).sum := by decide
  have hdescent : baseEnd_5840270 < baseStart_5840270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840281 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 1, 2, 2]
def baseStart_5840281 : Nat := 118140960795 + 5840281 * 2 ^ 59
def prefixEnd_5840281 : Nat := 4983230072969 + 3 ^ 40 * 5840281 * 2
def baseEnd_5840281 : Nat := 2998871310321169607428543

theorem tailTrace_5840281 : CollatzResearch.WordTrace tailWord_5840281 prefixEnd_5840281 2998871310321169607428543 := by
  unfold tailWord_5840281
  simp only [CollatzResearch.WordTrace]
  refine ⟨213012547754666852429608697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142008365169777901619739131 213012547754666852429608697)
  ·
    refine ⟨159759410816000139322206523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213012547754666852429608697 159759410816000139322206523)
    ·
      refine ⟨239639116224000208983309785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159759410816000139322206523 239639116224000208983309785)
      ·
        refine ⟨179729337168000156737482339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239639116224000208983309785 179729337168000156737482339)
        ·
          refine ⟨269594005752000235106223509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179729337168000156737482339 269594005752000235106223509)
          ·
            refine ⟨12637219019625011020604227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269594005752000235106223509 12637219019625011020604227)
            ·
              refine ⟨18955828529437516530906341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12637219019625011020604227 18955828529437516530906341)
              ·
                refine ⟨3554217849269534349544939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18955828529437516530906341 3554217849269534349544939)
                ·
                  refine ⟨5331326773904301524317409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554217849269534349544939 5331326773904301524317409)
                  ·
                    refine ⟨3998495080428226143238057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331326773904301524317409 3998495080428226143238057)
                    ·
                      refine ⟨2998871310321169607428543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998495080428226143238057 2998871310321169607428543)
                      ·
                        rfl

theorem cell23_5840281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_5840281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840281 prefixEnd_5840281 := by exact prefixLift 5840281
  have htrace : WordTrace (prefixWord ++ tailWord_5840281) baseStart_5840281 baseEnd_5840281 := by
    simpa [prefixWord, tailWord_5840281, baseEnd_5840281] using wordTrace_append hprefix tailTrace_5840281
  have hstable : (prefixWord ++ tailWord_5840281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840281).length < 2 ^ (prefixWord ++ tailWord_5840281).sum := by decide
  have hdescent : baseEnd_5840281 < baseStart_5840281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840330 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_5840330 : Nat := 118140960795 + 5840330 * 2 ^ 59
def prefixEnd_5840330 : Nat := 4983230072969 + 3 ^ 40 * 5840330 * 2
def baseEnd_5840330 : Nat := 999632156957746638571939

theorem tailTrace_5840330 : CollatzResearch.WordTrace tailWord_5840330 prefixEnd_5840330 999632156957746638571939 := by
  unfold tailWord_5840330
  simp only [CollatzResearch.WordTrace]
  refine ⟨53253583732872333449535611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142009556620992889198761629 53253583732872333449535611)
  ·
    refine ⟨79880375599308500174303417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53253583732872333449535611 79880375599308500174303417)
    ·
      refine ⟨59910281699481375130727563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79880375599308500174303417 59910281699481375130727563)
      ·
        refine ⟨89865422549222062696091345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59910281699481375130727563 89865422549222062696091345)
        ·
          refine ⟨67399066911916547022068509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89865422549222062696091345 67399066911916547022068509)
          ·
            refine ⟨25274650091968705133275691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67399066911916547022068509 25274650091968705133275691)
            ·
              refine ⟨37911975137953057699913537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25274650091968705133275691 37911975137953057699913537)
              ·
                refine ⟨28433981353464793274935153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37911975137953057699913537 28433981353464793274935153)
                ·
                  refine ⟨21325486015098594956201365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28433981353464793274935153 21325486015098594956201365)
                  ·
                    refine ⟨999632156957746638571939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21325486015098594956201365 999632156957746638571939)
                    ·
                      rfl

theorem cell23_5840330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_5840330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840330 prefixEnd_5840330 := by exact prefixLift 5840330
  have htrace : WordTrace (prefixWord ++ tailWord_5840330) baseStart_5840330 baseEnd_5840330 := by
    simpa [prefixWord, tailWord_5840330, baseEnd_5840330] using wordTrace_append hprefix tailTrace_5840330
  have hstable : (prefixWord ++ tailWord_5840330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840330).length < 2 ^ (prefixWord ++ tailWord_5840330).sum := by decide
  have hdescent : baseEnd_5840330 < baseStart_5840330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840360 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 7]
def baseStart_5840360 : Nat := 118140960795 + 5840360 * 2 ^ 59
def prefixEnd_5840360 : Nat := 4983230072969 + 3 ^ 40 * 5840360 * 2
def baseEnd_5840360 : Nat := 333212430588097199815631

theorem tailTrace_5840360 : CollatzResearch.WordTrace tailWord_5840360 prefixEnd_5840360 333212430588097199815631 := by
  unfold tailWord_5840360
  simp only [CollatzResearch.WordTrace]
  refine ⟨106507714560690324460867267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142010286080920432614489689 106507714560690324460867267)
  ·
    refine ⟨159761571841035486691300901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106507714560690324460867267 159761571841035486691300901)
    ·
      refine ⟨29955294720194153754618919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159761571841035486691300901 29955294720194153754618919)
      ·
        refine ⟨44932942080291230631928379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29955294720194153754618919 44932942080291230631928379)
        ·
          refine ⟨67399413120436845947892569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44932942080291230631928379 67399413120436845947892569)
          ·
            refine ⟨50549559840327634460919427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67399413120436845947892569 50549559840327634460919427)
            ·
              refine ⟨75824339760491451691379141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50549559840327634460919427 75824339760491451691379141)
              ·
                refine ⟨14217063705092147192133589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75824339760491451691379141 14217063705092147192133589)
                ·
                  refine ⟨333212430588097199815631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14217063705092147192133589 333212430588097199815631)
                  ·
                    rfl

theorem cell23_5840360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_5840360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840360 prefixEnd_5840360 := by exact prefixLift 5840360
  have htrace : WordTrace (prefixWord ++ tailWord_5840360) baseStart_5840360 baseEnd_5840360 := by
    simpa [prefixWord, tailWord_5840360, baseEnd_5840360] using wordTrace_append hprefix tailTrace_5840360
  have hstable : (prefixWord ++ tailWord_5840360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840360).length < 2 ^ (prefixWord ++ tailWord_5840360).sum := by decide
  have hdescent : baseEnd_5840360 < baseStart_5840360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840427 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 6, 4, 2]
def baseStart_5840427 : Nat := 118140960795 + 5840427 * 2 ^ 59
def prefixEnd_5840427 : Nat := 4983230072969 + 3 ^ 40 * 5840427 * 2
def baseEnd_5840427 : Nat := 2998946278496726036202871

theorem tailTrace_5840427 : CollatzResearch.WordTrace tailWord_5840427 prefixEnd_5840427 2998946278496726036202871 := by
  unfold tailWord_5840427
  simp only [CollatzResearch.WordTrace]
  refine ⟨213017872812137919364423535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142011915208091946242949023 213017872812137919364423535)
  ·
    refine ⟨319526809218206879046635303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213017872812137919364423535 319526809218206879046635303)
    ·
      refine ⟨479290213827310318569952955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319526809218206879046635303 479290213827310318569952955)
      ·
        refine ⟨718935320740965477854929433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479290213827310318569952955 718935320740965477854929433)
        ·
          refine ⟨539201490555724108391197075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718935320740965477854929433 539201490555724108391197075)
          ·
            refine ⟨808802235833586162586795613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539201490555724108391197075 808802235833586162586795613)
            ·
              refine ⟨303300838437594810970048355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808802235833586162586795613 303300838437594810970048355)
              ·
                refine ⟨454951257656392216455072533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303300838437594810970048355 454951257656392216455072533)
                ·
                  refine ⟨21325840202643385146331525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 454951257656392216455072533 21325840202643385146331525)
                  ·
                    refine ⟨3998595037995634714937161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21325840202643385146331525 3998595037995634714937161)
                    ·
                      refine ⟨2998946278496726036202871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998595037995634714937161 2998946278496726036202871)
                      ·
                        rfl

theorem cell23_5840427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4, 2].length) (baseStart_5840427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840427 prefixEnd_5840427 := by exact prefixLift 5840427
  have htrace : WordTrace (prefixWord ++ tailWord_5840427) baseStart_5840427 baseEnd_5840427 := by
    simpa [prefixWord, tailWord_5840427, baseEnd_5840427] using wordTrace_append hprefix tailTrace_5840427
  have hstable : (prefixWord ++ tailWord_5840427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840427).length < 2 ^ (prefixWord ++ tailWord_5840427).sum := by decide
  have hdescent : baseEnd_5840427 < baseStart_5840427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840488 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 1, 4]
def baseStart_5840488 : Nat := 118140960795 + 5840488 * 2 ^ 59
def prefixEnd_5840488 : Nat := 4983230072969 + 3 ^ 40 * 5840488 * 2
def baseEnd_5840488 : Nat := 999659200272216765846697

theorem tailTrace_5840488 : CollatzResearch.WordTrace tailWord_5840488 prefixEnd_5840488 999659200272216765846697 := by
  unfold tailWord_5840488
  simp only [CollatzResearch.WordTrace]
  refine ⟨106510048832458463391197059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142013398443277951188262745 106510048832458463391197059)
  ·
    refine ⟨159765073248687695086795589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106510048832458463391197059 159765073248687695086795589)
    ·
      refine ⟨29955951234128942828774173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159765073248687695086795589 29955951234128942828774173)
      ·
        refine ⟨11233481712798353560790315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29955951234128942828774173 11233481712798353560790315)
        ·
          refine ⟨16850222569197530341185473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11233481712798353560790315 16850222569197530341185473)
          ·
            refine ⟨12637666926898147755889105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16850222569197530341185473 12637666926898147755889105)
            ·
              refine ⟨9478250195173610816916829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12637666926898147755889105 9478250195173610816916829)
              ·
                refine ⟨3554343823190104056343811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9478250195173610816916829 3554343823190104056343811)
                ·
                  refine ⟨5331515734785156084515717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554343823190104056343811 5331515734785156084515717)
                  ·
                    refine ⟨999659200272216765846697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331515734785156084515717 999659200272216765846697)
                    ·
                      rfl

theorem cell23_5840488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_5840488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840488 prefixEnd_5840488 := by exact prefixLift 5840488
  have htrace : WordTrace (prefixWord ++ tailWord_5840488) baseStart_5840488 baseEnd_5840488 := by
    simpa [prefixWord, tailWord_5840488, baseEnd_5840488] using wordTrace_append hprefix tailTrace_5840488
  have hstable : (prefixWord ++ tailWord_5840488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840488).length < 2 ^ (prefixWord ++ tailWord_5840488).sum := by decide
  have hdescent : baseEnd_5840488 < baseStart_5840488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840501 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 6]
def baseStart_5840501 : Nat := 118140960795 + 5840501 * 2 ^ 59
def prefixEnd_5840501 : Nat := 4983230072969 + 3 ^ 40 * 5840501 * 2
def baseEnd_5840501 : Nat := 333220475118350971853059

theorem tailTrace_5840501 : CollatzResearch.WordTrace tailWord_5840501 prefixEnd_5840501 333220475118350971853059 := by
  unfold tailWord_5840501
  simp only [CollatzResearch.WordTrace]
  refine ⟨213020571813869830002617357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142013714542579886668411571 213020571813869830002617357)
  ·
    refine ⟨79882714430201186250981509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213020571813869830002617357 79882714430201186250981509)
    ·
      refine ⟨14978008955662722422059033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79882714430201186250981509 14978008955662722422059033)
      ·
        refine ⟨11233506716747041816544275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14978008955662722422059033 11233506716747041816544275)
        ·
          refine ⟨16850260075120562724816413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11233506716747041816544275 16850260075120562724816413)
          ·
            refine ⟨6318847528170211021806155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16850260075120562724816413 6318847528170211021806155)
            ·
              refine ⟨9478271292255316532709233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318847528170211021806155 9478271292255316532709233)
              ·
                refine ⟨7108703469191487399531925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9478271292255316532709233 7108703469191487399531925)
                ·
                  refine ⟨333220475118350971853059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7108703469191487399531925 333220475118350971853059)
                  ·
                    rfl

theorem cell23_5840501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_5840501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840501 prefixEnd_5840501 := by exact prefixLift 5840501
  have htrace : WordTrace (prefixWord ++ tailWord_5840501) baseStart_5840501 baseEnd_5840501 := by
    simpa [prefixWord, tailWord_5840501, baseEnd_5840501] using wordTrace_append hprefix tailTrace_5840501
  have hstable : (prefixWord ++ tailWord_5840501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840501).length < 2 ^ (prefixWord ++ tailWord_5840501).sum := by decide
  have hdescent : baseEnd_5840501 < baseStart_5840501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840527 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 8, 4]
def baseStart_5840527 : Nat := 118140960795 + 5840527 * 2 ^ 59
def prefixEnd_5840527 : Nat := 4983230072969 + 3 ^ 40 * 5840527 * 2
def baseEnd_5840527 : Nat := 999665875520725214984137

theorem tailTrace_5840527 : CollatzResearch.WordTrace tailWord_5840527 prefixEnd_5840527 999665875520725214984137 := by
  unfold tailWord_5840527
  simp only [CollatzResearch.WordTrace]
  refine ⟨213021520111775636443063835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142014346741183757628709223 213021520111775636443063835)
  ·
    refine ⟨319532280167663454664595753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213021520111775636443063835 319532280167663454664595753)
    ·
      refine ⟨239649210125747590998446815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319532280167663454664595753 239649210125747590998446815)
      ·
        refine ⟨359473815188621386497670223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239649210125747590998446815 359473815188621386497670223)
        ·
          refine ⟨539210722782932079746505335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359473815188621386497670223 539210722782932079746505335)
          ·
            refine ⟨808816084174398119619758003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539210722782932079746505335 808816084174398119619758003)
            ·
              refine ⟨1213224126261597179429637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808816084174398119619758003 1213224126261597179429637005)
              ·
                refine ⟨454959047348098942286113877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213224126261597179429637005 454959047348098942286113877)
                ·
                  refine ⟨5331551336110534479915397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 454959047348098942286113877 5331551336110534479915397)
                  ·
                    refine ⟨999665875520725214984137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331551336110534479915397 999665875520725214984137)
                    ·
                      rfl

theorem cell23_5840527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 4].length) (baseStart_5840527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840527 prefixEnd_5840527 := by exact prefixLift 5840527
  have htrace : WordTrace (prefixWord ++ tailWord_5840527) baseStart_5840527 baseEnd_5840527 := by
    simpa [prefixWord, tailWord_5840527, baseEnd_5840527] using wordTrace_append hprefix tailTrace_5840527
  have hstable : (prefixWord ++ tailWord_5840527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840527).length < 2 ^ (prefixWord ++ tailWord_5840527).sum := by decide
  have hdescent : baseEnd_5840527 < baseStart_5840527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840544 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_5840544 : Nat := 118140960795 + 5840544 * 2 ^ 59
def prefixEnd_5840544 : Nat := 4983230072969 + 3 ^ 40 * 5840544 * 2
def baseEnd_5840544 : Nat := 999668785244434026146611

theorem tailTrace_5840544 : CollatzResearch.WordTrace tailWord_5840544 prefixEnd_5840544 999668785244434026146611 := by
  unfold tailWord_5840544
  simp only [CollatzResearch.WordTrace]
  refine ⟨106511070076357024173216343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142014760101809365564288457 106511070076357024173216343)
  ·
    refine ⟨159766605114535536259824515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106511070076357024173216343 159766605114535536259824515)
    ·
      refine ⟨239649907671803304389736773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159766605114535536259824515 239649907671803304389736773)
      ·
        refine ⟨44934357688463119573075645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239649907671803304389736773 44934357688463119573075645)
        ·
          refine ⟨16850384133173669839903367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44934357688463119573075645 16850384133173669839903367)
          ·
            refine ⟨25275576199760504759855051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16850384133173669839903367 25275576199760504759855051)
            ·
              refine ⟨37913364299640757139782577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25275576199760504759855051 37913364299640757139782577)
              ·
                refine ⟨28435023224730567854836933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37913364299640757139782577 28435023224730567854836933)
                ·
                  refine ⟨5331566854636981472781925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28435023224730567854836933 5331566854636981472781925)
                  ·
                    refine ⟨999668785244434026146611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331566854636981472781925 999668785244434026146611)
                    ·
                      rfl

theorem cell23_5840544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_5840544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840544 prefixEnd_5840544 := by exact prefixLift 5840544
  have htrace : WordTrace (prefixWord ++ tailWord_5840544) baseStart_5840544 baseEnd_5840544 := by
    simpa [prefixWord, tailWord_5840544, baseEnd_5840544] using wordTrace_append hprefix tailTrace_5840544
  have hstable : (prefixWord ++ tailWord_5840544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840544).length < 2 ^ (prefixWord ++ tailWord_5840544).sum := by decide
  have hdescent : baseEnd_5840544 < baseStart_5840544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840545 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5840545 : Nat := 118140960795 + 5840545 * 2 ^ 59
def prefixEnd_5840545 : Nat := 4983230072969 + 3 ^ 40 * 5840545 * 2
def baseEnd_5840545 : Nat := 2999006869213956574527329

theorem tailTrace_5840545 : CollatzResearch.WordTrace tailWord_5840545 prefixEnd_5840545 2999006869213956574527329 := by
  unfold tailWord_5840545
  simp only [CollatzResearch.WordTrace]
  refine ⟨213022176625710425517219089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142014784417140283678146059 213022176625710425517219089)
  ·
    refine ⟨159766632469282819137914317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213022176625710425517219089 159766632469282819137914317)
    ·
      refine ⟨59912487175981057176717869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159766632469282819137914317 59912487175981057176717869)
      ·
        refine ⟨22467182690992896441269201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59912487175981057176717869 22467182690992896441269201)
        ·
          refine ⟨16850387018244672330951901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22467182690992896441269201 16850387018244672330951901)
          ·
            refine ⟨6318895131841752124106963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16850387018244672330951901 6318895131841752124106963)
            ·
              refine ⟨9478342697762628186160445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318895131841752124106963 9478342697762628186160445)
              ·
                refine ⟨3554378511660985569810167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9478342697762628186160445 3554378511660985569810167)
                ·
                  refine ⟨5331567767491478354715251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554378511660985569810167 5331567767491478354715251)
                  ·
                    refine ⟨7997351651237217532072877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331567767491478354715251 7997351651237217532072877)
                    ·
                      refine ⟨2999006869213956574527329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7997351651237217532072877 2999006869213956574527329)
                      ·
                        rfl

theorem cell23_5840545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5840545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840545 prefixEnd_5840545 := by exact prefixLift 5840545
  have htrace : WordTrace (prefixWord ++ tailWord_5840545) baseStart_5840545 baseEnd_5840545 := by
    simpa [prefixWord, tailWord_5840545, baseEnd_5840545] using wordTrace_append hprefix tailTrace_5840545
  have hstable : (prefixWord ++ tailWord_5840545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840545).length < 2 ^ (prefixWord ++ tailWord_5840545).sum := by decide
  have hdescent : baseEnd_5840545 < baseStart_5840545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840547 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_5840547 : Nat := 118140960795 + 5840547 * 2 ^ 59
def prefixEnd_5840547 : Nat := 4983230072969 + 3 ^ 40 * 5840547 * 2
def baseEnd_5840547 : Nat := 2999007896175265566702319

theorem tailTrace_5840547 : CollatzResearch.WordTrace tailWord_5840547 prefixEnd_5840547 2999007896175265566702319 := by
  unfold tailWord_5840547
  simp only [CollatzResearch.WordTrace]
  refine ⟨213022249571703179858791895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142014833047802119905861263 213022249571703179858791895)
  ·
    refine ⟨319533374357554769788187843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213022249571703179858791895 319533374357554769788187843)
    ·
      refine ⟨479300061536332154682281765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319533374357554769788187843 479300061536332154682281765)
      ·
        refine ⟨89868761538062279002927831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479300061536332154682281765 89868761538062279002927831)
        ·
          refine ⟨134803142307093418504391747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89868761538062279002927831 134803142307093418504391747)
          ·
            refine ⟨202204713460640127756587621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134803142307093418504391747 202204713460640127756587621)
            ·
              refine ⟨37913383773870023954360179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202204713460640127756587621 37913383773870023954360179)
              ·
                refine ⟨56870075660805035931540269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37913383773870023954360179 56870075660805035931540269)
                ·
                  refine ⟨21326278372801888474327601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56870075660805035931540269 21326278372801888474327601)
                  ·
                    refine ⟨15994708779601416355745701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21326278372801888474327601 15994708779601416355745701)
                    ·
                      refine ⟨2999007896175265566702319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15994708779601416355745701 2999007896175265566702319)
                      ·
                        rfl

theorem cell23_5840547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_5840547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840547 prefixEnd_5840547 := by exact prefixLift 5840547
  have htrace : WordTrace (prefixWord ++ tailWord_5840547) baseStart_5840547 baseEnd_5840547 := by
    simpa [prefixWord, tailWord_5840547, baseEnd_5840547] using wordTrace_append hprefix tailTrace_5840547
  have hstable : (prefixWord ++ tailWord_5840547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840547).length < 2 ^ (prefixWord ++ tailWord_5840547).sum := by decide
  have hdescent : baseEnd_5840547 < baseStart_5840547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840568 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 1, 2, 2]
def baseStart_5840568 : Nat := 118140960795 + 5840568 * 2 ^ 59
def prefixEnd_5840568 : Nat := 4983230072969 + 3 ^ 40 * 5840568 * 2
def baseEnd_5840568 : Nat := 2999018679269009984539723

theorem tailTrace_5840568 : CollatzResearch.WordTrace tailWord_5840568 prefixEnd_5840568 2999018679269009984539723 := by
  unfold tailWord_5840568
  simp only [CollatzResearch.WordTrace]
  refine ⟨106511507752313550222653179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142015343669751400296870905 106511507752313550222653179)
  ·
    refine ⟨159767261628470325333979769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106511507752313550222653179 159767261628470325333979769)
    ·
      refine ⟨119825446221352744000484827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159767261628470325333979769 119825446221352744000484827)
      ·
        refine ⟨179738169332029116000727241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119825446221352744000484827 179738169332029116000727241)
        ·
          refine ⟨134803626999021837000545431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179738169332029116000727241 134803626999021837000545431)
          ·
            refine ⟨202205440498532755500818147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134803626999021837000545431 202205440498532755500818147)
            ·
              refine ⟨303308160747799133251227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202205440498532755500818147 303308160747799133251227221)
              ·
                refine ⟨3554392508763271092787819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 303308160747799133251227221 3554392508763271092787819)
                ·
                  refine ⟨5331588763144906639181729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554392508763271092787819 5331588763144906639181729)
                  ·
                    refine ⟨3998691572358679979386297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331588763144906639181729 3998691572358679979386297)
                    ·
                      refine ⟨2999018679269009984539723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998691572358679979386297 2999018679269009984539723)
                      ·
                        rfl

theorem cell23_5840568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_5840568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840568 prefixEnd_5840568 := by exact prefixLift 5840568
  have htrace : WordTrace (prefixWord ++ tailWord_5840568) baseStart_5840568 baseEnd_5840568 := by
    simpa [prefixWord, tailWord_5840568, baseEnd_5840568] using wordTrace_append hprefix tailTrace_5840568
  have hstable : (prefixWord ++ tailWord_5840568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840568).length < 2 ^ (prefixWord ++ tailWord_5840568).sum := by decide
  have hdescent : baseEnd_5840568 < baseStart_5840568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840574 : List Nat := [4, 2, 1, 1, 2, 3, 2, 8]
def baseStart_5840574 : Nat := 118140960795 + 5840574 * 2 ^ 59
def prefixEnd_5840574 : Nat := 4983230072969 + 3 ^ 40 * 5840574 * 2
def baseEnd_5840574 : Nat := 111074880005664331891285

theorem tailTrace_5840574 : CollatzResearch.WordTrace tailWord_5840574 prefixEnd_5840574 111074880005664331891285 := by
  unfold tailWord_5840574
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627904292825670433753097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142015489561736908980016517 26627904292825670433753097)
  ·
    refine ⟨19970928219619252825314823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26627904292825670433753097 19970928219619252825314823)
    ·
      refine ⟨29956392329428879237972235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19970928219619252825314823 29956392329428879237972235)
      ·
        refine ⟨44934588494143318856958353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29956392329428879237972235 44934588494143318856958353)
        ·
          refine ⟨33700941370607489142718765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44934588494143318856958353 33700941370607489142718765)
          ·
            refine ⟨12637853013977808428519537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33700941370607489142718765 12637853013977808428519537)
            ·
              refine ⟨9478389760483356321389653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12637853013977808428519537 9478389760483356321389653)
              ·
                refine ⟨111074880005664331891285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9478389760483356321389653 111074880005664331891285)
                ·
                  rfl

theorem cell23_5840574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_5840574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840574 prefixEnd_5840574 := by exact prefixLift 5840574
  have htrace : WordTrace (prefixWord ++ tailWord_5840574) baseStart_5840574 baseEnd_5840574 := by
    simpa [prefixWord, tailWord_5840574, baseEnd_5840574] using wordTrace_append hprefix tailTrace_5840574
  have hstable : (prefixWord ++ tailWord_5840574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840574).length < 2 ^ (prefixWord ++ tailWord_5840574).sum := by decide
  have hdescent : baseEnd_5840574 < baseStart_5840574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840584 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_5840584 : Nat := 118140960795 + 5840584 * 2 ^ 59
def prefixEnd_5840584 : Nat := 4983230072969 + 3 ^ 40 * 5840584 * 2
def baseEnd_5840584 : Nat := 2999026894959481921939649

theorem tailTrace_5840584 : CollatzResearch.WordTrace tailWord_5840584 prefixEnd_5840584 2999026894959481921939649 := by
  unfold tailWord_5840584
  simp only [CollatzResearch.WordTrace]
  refine ⟨106511799536284567588944403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142015732715046090118592537 106511799536284567588944403)
  ·
    refine ⟨159767699304426851383416605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106511799536284567588944403 159767699304426851383416605)
    ·
      refine ⟨59912887239160069268781227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159767699304426851383416605 59912887239160069268781227)
      ·
        refine ⟨89869330858740103903171841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59912887239160069268781227 89869330858740103903171841)
        ·
          refine ⟨67401998144055077927378881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89869330858740103903171841 67401998144055077927378881)
          ·
            refine ⟨50551498608041308445534161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67401998144055077927378881 50551498608041308445534161)
            ·
              refine ⟨37913623956030981334150621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50551498608041308445534161 37913623956030981334150621)
              ·
                refine ⟨14217608983511618000306483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37913623956030981334150621 14217608983511618000306483)
                ·
                  refine ⟨21326413475267427000459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14217608983511618000306483 21326413475267427000459725)
                  ·
                    refine ⟨7997405053225285125172397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21326413475267427000459725 7997405053225285125172397)
                    ·
                      refine ⟨2999026894959481921939649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7997405053225285125172397 2999026894959481921939649)
                      ·
                        rfl

theorem cell23_5840584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_5840584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840584 prefixEnd_5840584 := by exact prefixLift 5840584
  have htrace : WordTrace (prefixWord ++ tailWord_5840584) baseStart_5840584 baseEnd_5840584 := by
    simpa [prefixWord, tailWord_5840584, baseEnd_5840584] using wordTrace_append hprefix tailTrace_5840584
  have hstable : (prefixWord ++ tailWord_5840584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840584).length < 2 ^ (prefixWord ++ tailWord_5840584).sum := by decide
  have hdescent : baseEnd_5840584 < baseStart_5840584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840605 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5840605 : Nat := 118140960795 + 5840605 * 2 ^ 59
def prefixEnd_5840605 : Nat := 4983230072969 + 3 ^ 40 * 5840605 * 2
def baseEnd_5840605 : Nat := 2999037678053226339777053

theorem tailTrace_5840605 : CollatzResearch.WordTrace tailWord_5840605 prefixEnd_5840605 2999037678053226339777053 := by
  unfold tailWord_5840605
  simp only [CollatzResearch.WordTrace]
  refine ⟨213024365005493055764403269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142016243336995370509602179 213024365005493055764403269)
  ·
    refine ⟨39942068438529947955825613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213024365005493055764403269 39942068438529947955825613)
    ·
      refine ⟨14978275664448730483434605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39942068438529947955825613 14978275664448730483434605)
      ·
        refine ⟨5616853374168273931287977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14978275664448730483434605 5616853374168273931287977)
        ·
          refine ⟨4212640030626205448465983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616853374168273931287977 4212640030626205448465983)
          ·
            refine ⟨6318960045939308172698975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212640030626205448465983 6318960045939308172698975)
            ·
              refine ⟨9478440068908962259048463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318960045939308172698975 9478440068908962259048463)
              ·
                refine ⟨14217660103363443388572695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9478440068908962259048463 14217660103363443388572695)
                ·
                  refine ⟨21326490155045165082859043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14217660103363443388572695 21326490155045165082859043)
                  ·
                    refine ⟨31989735232567747624288565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21326490155045165082859043 31989735232567747624288565)
                    ·
                      refine ⟨2999037678053226339777053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31989735232567747624288565 2999037678053226339777053)
                      ·
                        rfl

theorem cell23_5840605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5840605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840605 prefixEnd_5840605 := by exact prefixLift 5840605
  have htrace : WordTrace (prefixWord ++ tailWord_5840605) baseStart_5840605 baseEnd_5840605 := by
    simpa [prefixWord, tailWord_5840605, baseEnd_5840605] using wordTrace_append hprefix tailTrace_5840605
  have hstable : (prefixWord ++ tailWord_5840605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840605).length < 2 ^ (prefixWord ++ tailWord_5840605).sum := by decide
  have hdescent : baseEnd_5840605 < baseStart_5840605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840617 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_5840617 : Nat := 118140960795 + 5840617 * 2 ^ 59
def prefixEnd_5840617 : Nat := 4983230072969 + 3 ^ 40 * 5840617 * 2
def baseEnd_5840617 : Nat := 999681279940360097608999

theorem tailTrace_5840617 : CollatzResearch.WordTrace tailWord_5840617 prefixEnd_5840617 999681279940360097608999 := by
  unfold tailWord_5840617
  simp only [CollatzResearch.WordTrace]
  refine ⟨213024802681449581813840105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142016535120966387875893403 213024802681449581813840105)
  ·
    refine ⟨159768602011087186360380079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213024802681449581813840105 159768602011087186360380079)
    ·
      refine ⟨239652903016630779540570119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159768602011087186360380079 239652903016630779540570119)
      ·
        refine ⟨359479354524946169310855179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239652903016630779540570119 359479354524946169310855179)
        ·
          refine ⟨539219031787419253966282769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359479354524946169310855179 539219031787419253966282769)
          ·
            refine ⟨404414273840564440474712077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539219031787419253966282769 404414273840564440474712077)
            ·
              refine ⟨151655352690211665178017029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404414273840564440474712077 151655352690211665178017029)
              ·
                refine ⟨28435378629414687220878193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151655352690211665178017029 28435378629414687220878193)
                ·
                  refine ⟨21326533972061015415658645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28435378629414687220878193 21326533972061015415658645)
                  ·
                    refine ⟨999681279940360097608999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21326533972061015415658645 999681279940360097608999)
                    ·
                      rfl

theorem cell23_5840617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_5840617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840617 prefixEnd_5840617 := by exact prefixLift 5840617
  have htrace : WordTrace (prefixWord ++ tailWord_5840617) baseStart_5840617 baseEnd_5840617 := by
    simpa [prefixWord, tailWord_5840617, baseEnd_5840617] using wordTrace_append hprefix tailTrace_5840617
  have hstable : (prefixWord ++ tailWord_5840617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840617).length < 2 ^ (prefixWord ++ tailWord_5840617).sum := by decide
  have hdescent : baseEnd_5840617 < baseStart_5840617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840627 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_5840627 : Nat := 118140960795 + 5840627 * 2 ^ 59
def prefixEnd_5840627 : Nat := 4983230072969 + 3 ^ 40 * 5840627 * 2
def baseEnd_5840627 : Nat := 2999048974627625253701951

theorem tailTrace_5840627 : CollatzResearch.WordTrace tailWord_5840627 prefixEnd_5840627 2999048974627625253701951 := by
  unfold tailWord_5840627
  simp only [CollatzResearch.WordTrace]
  refine ⟨213025167411413353521704135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142016778274275569014469423 213025167411413353521704135)
  ·
    refine ⟨319537751117120030282556203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213025167411413353521704135 319537751117120030282556203)
    ·
      refine ⟨479306626675680045423834305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319537751117120030282556203 479306626675680045423834305)
      ·
        refine ⟨359479970006760034067875729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479306626675680045423834305 359479970006760034067875729)
        ·
          refine ⟨269609977505070025550906797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359479970006760034067875729 269609977505070025550906797)
          ·
            refine ⟨101103741564401259581590049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269609977505070025550906797 101103741564401259581590049)
            ·
              refine ⟨75827806173300944686192537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101103741564401259581590049 75827806173300944686192537)
              ·
                refine ⟨56870854629975708514644403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75827806173300944686192537 56870854629975708514644403)
                ·
                  refine ⟨85306281944963562771966605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56870854629975708514644403 85306281944963562771966605)
                  ·
                    refine ⟨31989855729361336039487477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85306281944963562771966605 31989855729361336039487477)
                    ·
                      refine ⟨2999048974627625253701951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31989855729361336039487477 2999048974627625253701951)
                      ·
                        rfl

theorem cell23_5840627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_5840627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840627 prefixEnd_5840627 := by exact prefixLift 5840627
  have htrace : WordTrace (prefixWord ++ tailWord_5840627) baseStart_5840627 baseEnd_5840627 := by
    simpa [prefixWord, tailWord_5840627, baseEnd_5840627] using wordTrace_append hprefix tailTrace_5840627
  have hstable : (prefixWord ++ tailWord_5840627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840627).length < 2 ^ (prefixWord ++ tailWord_5840627).sum := by decide
  have hdescent : baseEnd_5840627 < baseStart_5840627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840641 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_5840641 : Nat := 118140960795 + 5840641 * 2 ^ 59
def prefixEnd_5840641 : Nat := 4983230072969 + 3 ^ 40 * 5840641 * 2
def baseEnd_5840641 : Nat := 2999056163356788198926887

theorem tailTrace_5840641 : CollatzResearch.WordTrace tailWord_5840641 prefixEnd_5840641 2999056163356788198926887 := by
  unfold tailWord_5840641
  simp only [CollatzResearch.WordTrace]
  refine ⟨213025678033362633912713777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142017118688908422608475851 213025678033362633912713777)
  ·
    refine ⟨159769258525021975434535333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213025678033362633912713777 159769258525021975434535333)
    ·
      refine ⟨29956735973441620393975375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159769258525021975434535333 29956735973441620393975375)
      ·
        refine ⟨44935103960162430590963063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29956735973441620393975375 44935103960162430590963063)
        ·
          refine ⟨67402655940243645886444595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44935103960162430590963063 67402655940243645886444595)
          ·
            refine ⟨101103983910365468829666893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67402655940243645886444595 101103983910365468829666893)
            ·
              refine ⟨37913993966387050811125085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101103983910365468829666893 37913993966387050811125085)
              ·
                refine ⟨14217747737395144054171907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37913993966387050811125085 14217747737395144054171907)
                ·
                  refine ⟨21326621606092716081257861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14217747737395144054171907 21326621606092716081257861)
                  ·
                    refine ⟨3998741551142384265235849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21326621606092716081257861 3998741551142384265235849)
                    ·
                      refine ⟨2999056163356788198926887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998741551142384265235849 2999056163356788198926887)
                      ·
                        rfl

theorem cell23_5840641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_5840641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840641 prefixEnd_5840641 := by exact prefixLift 5840641
  have htrace : WordTrace (prefixWord ++ tailWord_5840641) baseStart_5840641 baseEnd_5840641 := by
    simpa [prefixWord, tailWord_5840641, baseEnd_5840641] using wordTrace_append hprefix tailTrace_5840641
  have hstable : (prefixWord ++ tailWord_5840641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840641).length < 2 ^ (prefixWord ++ tailWord_5840641).sum := by decide
  have hdescent : baseEnd_5840641 < baseStart_5840641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840653 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5840653 : Nat := 118140960795 + 5840653 * 2 ^ 59
def prefixEnd_5840653 : Nat := 4983230072969 + 3 ^ 40 * 5840653 * 2
def baseEnd_5840653 : Nat := 2999062325124642151976833

theorem tailTrace_5840653 : CollatzResearch.WordTrace tailWord_5840653 prefixEnd_5840653 2999062325124642151976833 := by
  unfold tailWord_5840653
  simp only [CollatzResearch.WordTrace]
  refine ⟨213026115709319159962150613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142017410472879439974767075 213026115709319159962150613)
  ·
    refine ⟨4992799586937167811612905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 213026115709319159962150613 4992799586937167811612905)
    ·
      refine ⟨3744599690202875858709679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4992799586937167811612905 3744599690202875858709679)
      ·
        refine ⟨5616899535304313788064519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744599690202875858709679 5616899535304313788064519)
        ·
          refine ⟨8425349302956470682096779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616899535304313788064519 8425349302956470682096779)
          ·
            refine ⟨12638023954434706023145169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425349302956470682096779 12638023954434706023145169)
            ·
              refine ⟨9478517965826029517358877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12638023954434706023145169 9478517965826029517358877)
              ·
                refine ⟨3554444237184761069009579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9478517965826029517358877 3554444237184761069009579)
                ·
                  refine ⟨5331666355777141603514369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554444237184761069009579 5331666355777141603514369)
                  ·
                    refine ⟨3998749766832856202635777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331666355777141603514369 3998749766832856202635777)
                    ·
                      refine ⟨2999062325124642151976833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998749766832856202635777 2999062325124642151976833)
                      ·
                        rfl

theorem cell23_5840653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5840653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840653 prefixEnd_5840653 := by exact prefixLift 5840653
  have htrace : WordTrace (prefixWord ++ tailWord_5840653) baseStart_5840653 baseEnd_5840653 := by
    simpa [prefixWord, tailWord_5840653, baseEnd_5840653] using wordTrace_append hprefix tailTrace_5840653
  have hstable : (prefixWord ++ tailWord_5840653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840653).length < 2 ^ (prefixWord ++ tailWord_5840653).sum := by decide
  have hdescent : baseEnd_5840653 < baseStart_5840653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840657 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_5840657 : Nat := 118140960795 + 5840657 * 2 ^ 59
def prefixEnd_5840657 : Nat := 4983230072969 + 3 ^ 40 * 5840657 * 2
def baseEnd_5840657 : Nat := 2999064379047260136326813

theorem tailTrace_5840657 : CollatzResearch.WordTrace tailWord_5840657 prefixEnd_5840657 2999064379047260136326813 := by
  unfold tailWord_5840657
  simp only [CollatzResearch.WordTrace]
  refine ⟨213026261601304668645296225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142017507734203112430197483 213026261601304668645296225)
  ·
    refine ⟨159769696200978501483972169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213026261601304668645296225 159769696200978501483972169)
    ·
      refine ⟨119827272150733876112979127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159769696200978501483972169 119827272150733876112979127)
      ·
        refine ⟨179740908226100814169468691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119827272150733876112979127 179740908226100814169468691)
        ·
          refine ⟨269611362339151221254203037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179740908226100814169468691 269611362339151221254203037)
          ·
            refine ⟨101104260877181707970326139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269611362339151221254203037 101104260877181707970326139)
            ·
              refine ⟨151656391315772561955489209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101104260877181707970326139 151656391315772561955489209)
              ·
                refine ⟨113742293486829421466616907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151656391315772561955489209 113742293486829421466616907)
                ·
                  refine ⟨170613440230244132199925361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113742293486829421466616907 170613440230244132199925361)
                  ·
                    refine ⟨127960080172683099149944021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170613440230244132199925361 127960080172683099149944021)
                    ·
                      refine ⟨2999064379047260136326813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127960080172683099149944021 2999064379047260136326813)
                      ·
                        rfl

theorem cell23_5840657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_5840657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840657 prefixEnd_5840657 := by exact prefixLift 5840657
  have htrace : WordTrace (prefixWord ++ tailWord_5840657) baseStart_5840657 baseEnd_5840657 := by
    simpa [prefixWord, tailWord_5840657, baseEnd_5840657] using wordTrace_append hprefix tailTrace_5840657
  have hstable : (prefixWord ++ tailWord_5840657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840657).length < 2 ^ (prefixWord ++ tailWord_5840657).sum := by decide
  have hdescent : baseEnd_5840657 < baseStart_5840657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840714 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_5840714 : Nat := 118140960795 + 5840714 * 2 ^ 59
def prefixEnd_5840714 : Nat := 4983230072969 + 3 ^ 40 * 5840714 * 2
def baseEnd_5840714 : Nat := 2999093647444566413314051

theorem tailTrace_5840714 : CollatzResearch.WordTrace tailWord_5840714 prefixEnd_5840714 2999093647444566413314051 := by
  unfold tailWord_5840714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53257085140524541845030299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142018893708065444920080797 53257085140524541845030299)
  ·
    refine ⟨79885627710786812767545449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53257085140524541845030299 79885627710786812767545449)
    ·
      refine ⟨59914220783090109575659087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79885627710786812767545449 59914220783090109575659087)
      ·
        refine ⟨89871331174635164363488631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59914220783090109575659087 89871331174635164363488631)
        ·
          refine ⟨134806996761952746545232947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89871331174635164363488631 134806996761952746545232947)
          ·
            refine ⟨202210495142929119817849421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134806996761952746545232947 202210495142929119817849421)
            ·
              refine ⟨75828935678598419931693533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202210495142929119817849421 75828935678598419931693533)
              ·
                refine ⟨28435850879474407474385075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75828935678598419931693533 28435850879474407474385075)
                ·
                  refine ⟨42653776319211611211577613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28435850879474407474385075 42653776319211611211577613)
                  ·
                    refine ⟨15995166119704354204341605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42653776319211611211577613 15995166119704354204341605)
                    ·
                      refine ⟨2999093647444566413314051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15995166119704354204341605 2999093647444566413314051)
                      ·
                        rfl

theorem cell23_5840714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_5840714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840714 prefixEnd_5840714 := by exact prefixLift 5840714
  have htrace : WordTrace (prefixWord ++ tailWord_5840714) baseStart_5840714 baseEnd_5840714 := by
    simpa [prefixWord, tailWord_5840714, baseEnd_5840714] using wordTrace_append hprefix tailTrace_5840714
  have hstable : (prefixWord ++ tailWord_5840714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840714).length < 2 ^ (prefixWord ++ tailWord_5840714).sum := by decide
  have hdescent : baseEnd_5840714 < baseStart_5840714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840784 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_5840784 : Nat := 118140960795 + 5840784 * 2 ^ 59
def prefixEnd_5840784 : Nat := 4983230072969 + 3 ^ 40 * 5840784 * 2
def baseEnd_5840784 : Nat := 999709863696793713146243

theorem tailTrace_5840784 : CollatzResearch.WordTrace tailWord_5840784 prefixEnd_5840784 999709863696793713146243 := by
  unfold tailWord_5840784
  simp only [CollatzResearch.WordTrace]
  refine ⟨106515446835922284667584703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142020595781229712890112937 106515446835922284667584703)
  ·
    refine ⟨159773170253883427001377055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106515446835922284667584703 159773170253883427001377055)
    ·
      refine ⟨239659755380825140502065583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159773170253883427001377055 239659755380825140502065583)
      ·
        refine ⟨359489633071237710753098375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239659755380825140502065583 359489633071237710753098375)
        ·
          refine ⟨539234449606856566129647563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359489633071237710753098375 539234449606856566129647563)
          ·
            refine ⟨808851674410284849194471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539234449606856566129647563 808851674410284849194471345)
            ·
              refine ⟨606638755807713636895853509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808851674410284849194471345 606638755807713636895853509)
              ·
                refine ⟨113744766713946306917972533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606638755807713636895853509 113744766713946306917972533)
                ·
                  refine ⟨10663571879432466273559925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113744766713946306917972533 10663571879432466273559925)
                  ·
                    refine ⟨999709863696793713146243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10663571879432466273559925 999709863696793713146243)
                    ·
                      rfl

theorem cell23_5840784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_5840784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840784 prefixEnd_5840784 := by exact prefixLift 5840784
  have htrace : WordTrace (prefixWord ++ tailWord_5840784) baseStart_5840784 baseEnd_5840784 := by
    simpa [prefixWord, tailWord_5840784, baseEnd_5840784] using wordTrace_append hprefix tailTrace_5840784
  have hstable : (prefixWord ++ tailWord_5840784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840784).length < 2 ^ (prefixWord ++ tailWord_5840784).sum := by decide
  have hdescent : baseEnd_5840784 < baseStart_5840784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840788 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 6]
def baseStart_5840788 : Nat := 118140960795 + 5840788 * 2 ^ 59
def prefixEnd_5840788 : Nat := 4983230072969 + 3 ^ 40 * 5840788 * 2
def baseEnd_5840788 : Nat := 333236849445888791532079

theorem tailTrace_5840788 : CollatzResearch.WordTrace tailWord_5840788 prefixEnd_5840788 333236849445888791532079 := by
  unfold tailWord_5840788
  simp only [CollatzResearch.WordTrace]
  refine ⟨106515519781915039009157509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142020693042553385345543345 106515519781915039009157509)
  ·
    refine ⟨19971659959109069814217033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106515519781915039009157509 19971659959109069814217033)
    ·
      refine ⟨14978744969331802360662775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19971659959109069814217033 14978744969331802360662775)
      ·
        refine ⟨22468117453997703540994163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14978744969331802360662775 22468117453997703540994163)
        ·
          refine ⟨33702176180996555311491245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22468117453997703540994163 33702176180996555311491245)
          ·
            refine ⟨12638316067873708241809217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33702176180996555311491245 12638316067873708241809217)
            ·
              refine ⟨9478737050905281181356913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12638316067873708241809217 9478737050905281181356913)
              ·
                refine ⟨7109052788178960886017685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9478737050905281181356913 7109052788178960886017685)
                ·
                  refine ⟨333236849445888791532079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7109052788178960886017685 333236849445888791532079)
                  ·
                    rfl

theorem cell23_5840788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_5840788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840788 prefixEnd_5840788 := by exact prefixLift 5840788
  have htrace : WordTrace (prefixWord ++ tailWord_5840788) baseStart_5840788 baseEnd_5840788 := by
    simpa [prefixWord, tailWord_5840788, baseEnd_5840788] using wordTrace_append hprefix tailTrace_5840788
  have hstable : (prefixWord ++ tailWord_5840788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840788).length < 2 ^ (prefixWord ++ tailWord_5840788).sum := by decide
  have hdescent : baseEnd_5840788 < baseStart_5840788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840792 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 1, 4]
def baseStart_5840792 : Nat := 118140960795 + 5840792 * 2 ^ 59
def prefixEnd_5840792 : Nat := 4983230072969 + 3 ^ 40 * 5840792 * 2
def baseEnd_5840792 : Nat := 999711232978539036046231

theorem tailTrace_5840792 : CollatzResearch.WordTrace tailWord_5840792 prefixEnd_5840792 999711232978539036046231 := by
  unfold tailWord_5840792
  simp only [CollatzResearch.WordTrace]
  refine ⟨106515592727907793350730315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142020790303877057800973753 106515592727907793350730315)
  ·
    refine ⟨159773389091861690026095473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106515592727907793350730315 159773389091861690026095473)
    ·
      refine ⟨119830041818896267519571605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159773389091861690026095473 119830041818896267519571605)
      ·
        refine ⟨5617033210260762539979919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119830041818896267519571605 5617033210260762539979919)
        ·
          refine ⟨8425549815391143809969879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617033210260762539979919 8425549815391143809969879)
          ·
            refine ⟨12638324723086715714954819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425549815391143809969879 12638324723086715714954819)
            ·
              refine ⟨18957487084630073572432229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638324723086715714954819 18957487084630073572432229)
              ·
                refine ⟨3554528828368138794831043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18957487084630073572432229 3554528828368138794831043)
                ·
                  refine ⟨5331793242552208192246565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554528828368138794831043 5331793242552208192246565)
                  ·
                    refine ⟨999711232978539036046231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331793242552208192246565 999711232978539036046231)
                    ·
                      rfl

theorem cell23_5840792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_5840792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840792 prefixEnd_5840792 := by exact prefixLift 5840792
  have htrace : WordTrace (prefixWord ++ tailWord_5840792) baseStart_5840792 baseEnd_5840792 := by
    simpa [prefixWord, tailWord_5840792, baseEnd_5840792] using wordTrace_append hprefix tailTrace_5840792
  have hstable : (prefixWord ++ tailWord_5840792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840792).length < 2 ^ (prefixWord ++ tailWord_5840792).sum := by decide
  have hdescent : baseEnd_5840792 < baseStart_5840792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840831 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 4, 4]
def baseStart_5840831 : Nat := 118140960795 + 5840831 * 2 ^ 59
def prefixEnd_5840831 : Nat := 4983230072969 + 3 ^ 40 * 5840831 * 2
def baseEnd_5840831 : Nat := 999717908227047485183671

theorem tailTrace_5840831 : CollatzResearch.WordTrace tailWord_5840831 prefixEnd_5840831 999717908227047485183671 := by
  unfold tailWord_5840831
  simp only [CollatzResearch.WordTrace]
  refine ⟨213032607902674296362130347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142021738601782864241420231 213032607902674296362130347)
  ·
    refine ⟨319548911854011444543195521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213032607902674296362130347 319548911854011444543195521)
    ·
      refine ⟨239661683890508583407396641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319548911854011444543195521 239661683890508583407396641)
      ·
        refine ⟨179746262917881437555547481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239661683890508583407396641 179746262917881437555547481)
        ·
          refine ⟨134809697188411078166660611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179746262917881437555547481 134809697188411078166660611)
          ·
            refine ⟨202214545782616617249990917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134809697188411078166660611 202214545782616617249990917)
            ·
              refine ⟨37915227334240615734373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202214545782616617249990917 37915227334240615734373297)
              ·
                refine ⟨28436420500680461800779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37915227334240615734373297 28436420500680461800779973)
                ·
                  refine ⟨5331828843877586587646245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28436420500680461800779973 5331828843877586587646245)
                  ·
                    refine ⟨999717908227047485183671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331828843877586587646245 999717908227047485183671)
                    ·
                      rfl

theorem cell23_5840831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 4].length) (baseStart_5840831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840831 prefixEnd_5840831 := by exact prefixLift 5840831
  have htrace : WordTrace (prefixWord ++ tailWord_5840831) baseStart_5840831 baseEnd_5840831 := by
    simpa [prefixWord, tailWord_5840831, baseEnd_5840831] using wordTrace_append hprefix tailTrace_5840831
  have hstable : (prefixWord ++ tailWord_5840831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840831).length < 2 ^ (prefixWord ++ tailWord_5840831).sum := by decide
  have hdescent : baseEnd_5840831 < baseStart_5840831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840848 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 2, 4]
def baseStart_5840848 : Nat := 118140960795 + 5840848 * 2 ^ 59
def prefixEnd_5840848 : Nat := 4983230072969 + 3 ^ 40 * 5840848 * 2
def baseEnd_5840848 : Nat := 999720817950756296346145

theorem tailTrace_5840848 : CollatzResearch.WordTrace tailWord_5840848 prefixEnd_5840848 999720817950756296346145 := by
  unfold tailWord_5840848
  simp only [CollatzResearch.WordTrace]
  refine ⟨106516613971806354132749599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142022151962408472176999465 106516613971806354132749599)
  ·
    refine ⟨159774920957709531199124399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106516613971806354132749599 159774920957709531199124399)
    ·
      refine ⟨239662381436564296798686599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159774920957709531199124399 239662381436564296798686599)
      ·
        refine ⟨359493572154846445198029899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239662381436564296798686599 359493572154846445198029899)
        ·
          refine ⟨539240358232269667797044849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359493572154846445198029899 539240358232269667797044849)
          ·
            refine ⟨404430268674202250847783637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539240358232269667797044849 404430268674202250847783637)
            ·
              refine ⟨9478834422051615254244929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 404430268674202250847783637 9478834422051615254244929)
              ·
                refine ⟨7109125816538711440683697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9478834422051615254244929 7109125816538711440683697)
                ·
                  refine ⟨5331844362404033580512773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109125816538711440683697 5331844362404033580512773)
                  ·
                    refine ⟨999720817950756296346145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331844362404033580512773 999720817950756296346145)
                    ·
                      rfl

theorem cell23_5840848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_5840848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840848 prefixEnd_5840848 := by exact prefixLift 5840848
  have htrace : WordTrace (prefixWord ++ tailWord_5840848) baseStart_5840848 baseEnd_5840848 := by
    simpa [prefixWord, tailWord_5840848, baseEnd_5840848] using wordTrace_append hprefix tailTrace_5840848
  have hstable : (prefixWord ++ tailWord_5840848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840848).length < 2 ^ (prefixWord ++ tailWord_5840848).sum := by decide
  have hdescent : baseEnd_5840848 < baseStart_5840848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840855 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_5840855 : Nat := 118140960795 + 5840855 * 2 ^ 59
def prefixEnd_5840855 : Nat := 4983230072969 + 3 ^ 40 * 5840855 * 2
def baseEnd_5840855 : Nat := 2999166048216850361650903

theorem tailTrace_5840855 : CollatzResearch.WordTrace tailWord_5840855 prefixEnd_5840855 2999166048216850361650903 := by
  unfold tailWord_5840855
  simp only [CollatzResearch.WordTrace]
  refine ⟨213033483254587348461004019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142022322169724898974002679 213033483254587348461004019)
  ·
    refine ⟨319550224881881022691506029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213033483254587348461004019 319550224881881022691506029)
    ·
      refine ⟨119831334330705383509314761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319550224881881022691506029 119831334330705383509314761)
      ·
        refine ⟨89873500748029037631986071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119831334330705383509314761 89873500748029037631986071)
        ·
          refine ⟨134810251122043556447979107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89873500748029037631986071 134810251122043556447979107)
          ·
            refine ⟨202215376683065334671968661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134810251122043556447979107 202215376683065334671968661)
            ·
              refine ⟨9478845782018687562748531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202215376683065334671968661 9478845782018687562748531)
              ·
                refine ⟨14218268673028031344122797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9478845782018687562748531 14218268673028031344122797)
                ·
                  refine ⟨5331850752385511754046049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14218268673028031344122797 5331850752385511754046049)
                  ·
                    refine ⟨3998888064289133815534537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331850752385511754046049 3998888064289133815534537)
                    ·
                      refine ⟨2999166048216850361650903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998888064289133815534537 2999166048216850361650903)
                      ·
                        rfl

theorem cell23_5840855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_5840855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840855 prefixEnd_5840855 := by exact prefixLift 5840855
  have htrace : WordTrace (prefixWord ++ tailWord_5840855) baseStart_5840855 baseEnd_5840855 := by
    simpa [prefixWord, tailWord_5840855, baseEnd_5840855] using wordTrace_append hprefix tailTrace_5840855
  have hstable : (prefixWord ++ tailWord_5840855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840855).length < 2 ^ (prefixWord ++ tailWord_5840855).sum := by decide
  have hdescent : baseEnd_5840855 < baseStart_5840855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840858 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_5840858 : Nat := 118140960795 + 5840858 * 2 ^ 59
def prefixEnd_5840858 : Nat := 4983230072969 + 3 ^ 40 * 5840858 * 2
def baseEnd_5840858 : Nat := 2999167588658813849913389

theorem tailTrace_5840858 : CollatzResearch.WordTrace tailWord_5840858 prefixEnd_5840858 2999167588658813849913389 := by
  unfold tailWord_5840858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53258398168394119993340807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142022395115717653315575485 53258398168394119993340807)
  ·
    refine ⟨79887597252591179990011211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53258398168394119993340807 79887597252591179990011211)
    ·
      refine ⟨119831395878886769985016817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79887597252591179990011211 119831395878886769985016817)
      ·
        refine ⟨89873546909165077488762613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119831395878886769985016817 89873546909165077488762613)
        ·
          refine ⟨8425645022734226014571495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89873546909165077488762613 8425645022734226014571495)
          ·
            refine ⟨12638467534101339021857243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425645022734226014571495 12638467534101339021857243)
            ·
              refine ⟨18957701301152008532785865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638467534101339021857243 18957701301152008532785865)
              ·
                refine ⟨14218275975864006399589399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18957701301152008532785865 14218275975864006399589399)
                ·
                  refine ⟨21327413963796009599384099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14218275975864006399589399 21327413963796009599384099)
                  ·
                    refine ⟨31991120945694014399076149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21327413963796009599384099 31991120945694014399076149)
                    ·
                      refine ⟨2999167588658813849913389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31991120945694014399076149 2999167588658813849913389)
                      ·
                        rfl

theorem cell23_5840858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_5840858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840858 prefixEnd_5840858 := by exact prefixLift 5840858
  have htrace : WordTrace (prefixWord ++ tailWord_5840858) baseStart_5840858 baseEnd_5840858 := by
    simpa [prefixWord, tailWord_5840858, baseEnd_5840858] using wordTrace_append hprefix tailTrace_5840858
  have hstable : (prefixWord ++ tailWord_5840858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840858).length < 2 ^ (prefixWord ++ tailWord_5840858).sum := by decide
  have hdescent : baseEnd_5840858 < baseStart_5840858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840878 : List Nat := [4, 1, 2, 1, 3, 1, 4, 7]
def baseStart_5840878 : Nat := 118140960795 + 5840878 * 2 ^ 59
def prefixEnd_5840878 : Nat := 4983230072969 + 3 ^ 40 * 5840878 * 2
def baseEnd_5840878 : Nat := 111080661417477917469011

theorem tailTrace_5840878 : CollatzResearch.WordTrace tailWord_5840878 prefixEnd_5840878 111080661417477917469011 := by
  unfold tailWord_5840878
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629290266688002923636411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142022881422336015592727525 26629290266688002923636411)
  ·
    refine ⟨39943935400032004385454617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26629290266688002923636411 39943935400032004385454617)
    ·
      refine ⟨29957951550024003289090963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39943935400032004385454617 29957951550024003289090963)
      ·
        refine ⟨44936927325036004933636445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29957951550024003289090963 44936927325036004933636445)
        ·
          refine ⟨16851347746888501850113667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44936927325036004933636445 16851347746888501850113667)
          ·
            refine ⟨25277021620332752775170501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16851347746888501850113667 25277021620332752775170501)
            ·
              refine ⟨4739441553812391145344469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25277021620332752775170501 4739441553812391145344469)
              ·
                refine ⟨111080661417477917469011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4739441553812391145344469 111080661417477917469011)
                ·
                  rfl

theorem cell23_5840878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_5840878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840878 prefixEnd_5840878 := by exact prefixLift 5840878
  have htrace : WordTrace (prefixWord ++ tailWord_5840878) baseStart_5840878 baseEnd_5840878 := by
    simpa [prefixWord, tailWord_5840878, baseEnd_5840878] using wordTrace_append hprefix tailTrace_5840878
  have hstable : (prefixWord ++ tailWord_5840878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840878).length < 2 ^ (prefixWord ++ tailWord_5840878).sum := by decide
  have hdescent : baseEnd_5840878 < baseStart_5840878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840888 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_5840888 : Nat := 118140960795 + 5840888 * 2 ^ 59
def prefixEnd_5840888 : Nat := 4983230072969 + 3 ^ 40 * 5840888 * 2
def baseEnd_5840888 : Nat := 2999182993078448732538251

theorem tailTrace_5840888 : CollatzResearch.WordTrace tailWord_5840888 prefixEnd_5840888 2999182993078448732538251 := by
  unfold tailWord_5840888
  simp only [CollatzResearch.WordTrace]
  refine ⟨106517343431733897548477659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142023124575645196731303545 106517343431733897548477659)
  ·
    refine ⟨159776015147600846322716489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106517343431733897548477659 159776015147600846322716489)
    ·
      refine ⟨119832011360700634742037367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159776015147600846322716489 119832011360700634742037367)
      ·
        refine ⟨179748017041050952113056051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119832011360700634742037367 179748017041050952113056051)
        ·
          refine ⟨269622025561576428169584077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179748017041050952113056051 269622025561576428169584077)
          ·
            refine ⟨101108259585591160563594029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269622025561576428169584077 101108259585591160563594029)
            ·
              refine ⟨37915597344596685211347761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101108259585591160563594029 37915597344596685211347761)
              ·
                refine ⟨28436698008447513908510821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37915597344596685211347761 28436698008447513908510821)
                ·
                  refine ⟨5331880876583908857845779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28436698008447513908510821 5331880876583908857845779)
                  ·
                    refine ⟨7997821314875863286768669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331880876583908857845779 7997821314875863286768669)
                    ·
                      refine ⟨2999182993078448732538251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7997821314875863286768669 2999182993078448732538251)
                      ·
                        rfl

theorem cell23_5840888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_5840888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840888 prefixEnd_5840888 := by exact prefixLift 5840888
  have htrace : WordTrace (prefixWord ++ tailWord_5840888) baseStart_5840888 baseEnd_5840888 := by
    simpa [prefixWord, tailWord_5840888, baseEnd_5840888] using wordTrace_append hprefix tailTrace_5840888
  have hstable : (prefixWord ++ tailWord_5840888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840888).length < 2 ^ (prefixWord ++ tailWord_5840888).sum := by decide
  have hdescent : baseEnd_5840888 < baseStart_5840888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840889 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 1, 2, 2]
def baseStart_5840889 : Nat := 118140960795 + 5840889 * 2 ^ 59
def prefixEnd_5840889 : Nat := 4983230072969 + 3 ^ 40 * 5840889 * 2
def baseEnd_5840889 : Nat := 2999183506559103228625747

theorem tailTrace_5840889 : CollatzResearch.WordTrace tailWord_5840889 prefixEnd_5840889 2999183506559103228625747 := by
  unfold tailWord_5840889
  simp only [CollatzResearch.WordTrace]
  refine ⟨213034723336464172267741721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142023148890976114845161147 213034723336464172267741721)
  ·
    refine ⟨159776042502348129200806291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213034723336464172267741721 159776042502348129200806291)
    ·
      refine ⟨239664063753522193801209437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159776042502348129200806291 239664063753522193801209437)
      ·
        refine ⟨89874023907570822675453539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239664063753522193801209437 89874023907570822675453539)
        ·
          refine ⟨134811035861356234013180309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89874023907570822675453539 134811035861356234013180309)
          ·
            refine ⟨6319267306001073469367827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134811035861356234013180309 6319267306001073469367827)
            ·
              refine ⟨9478900959001610204051741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319267306001073469367827 9478900959001610204051741)
              ·
                refine ⟨3554587859625603826519403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9478900959001610204051741 3554587859625603826519403)
                ·
                  refine ⟨5331881789438405739779105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554587859625603826519403 5331881789438405739779105)
                  ·
                    refine ⟨3998911342078804304834329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331881789438405739779105 3998911342078804304834329)
                    ·
                      refine ⟨2999183506559103228625747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998911342078804304834329 2999183506559103228625747)
                      ·
                        rfl

theorem cell23_5840889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_5840889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840889 prefixEnd_5840889 := by exact prefixLift 5840889
  have htrace : WordTrace (prefixWord ++ tailWord_5840889) baseStart_5840889 baseEnd_5840889 := by
    simpa [prefixWord, tailWord_5840889, baseEnd_5840889] using wordTrace_append hprefix tailTrace_5840889
  have hstable : (prefixWord ++ tailWord_5840889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840889).length < 2 ^ (prefixWord ++ tailWord_5840889).sum := by decide
  have hdescent : baseEnd_5840889 < baseStart_5840889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840906 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_5840906 : Nat := 118140960795 + 5840906 * 2 ^ 59
def prefixEnd_5840906 : Nat := 4983230072969 + 3 ^ 40 * 5840906 * 2
def baseEnd_5840906 : Nat := 2999192235730229662113169

theorem tailTrace_5840906 : CollatzResearch.WordTrace tailWord_5840906 prefixEnd_5840906 2999192235730229662113169 := by
  unfold tailWord_5840906
  simp only [CollatzResearch.WordTrace]
  refine ⟨53258835844350646042777643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142023562251601722780740381 53258835844350646042777643)
  ·
    refine ⟨79888253766525969064166465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53258835844350646042777643 79888253766525969064166465)
    ·
      refine ⟨59916190324894476798124849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79888253766525969064166465 59916190324894476798124849)
      ·
        refine ⟨44937142743670857598593637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59916190324894476798124849 44937142743670857598593637)
        ·
          refine ⟨8425714264438285799736307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44937142743670857598593637 8425714264438285799736307)
          ·
            refine ⟨12638571396657428699604461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425714264438285799736307 12638571396657428699604461)
            ·
              refine ⟨4739464273746535762351673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12638571396657428699604461 4739464273746535762351673)
              ·
                refine ⟨3554598205309901821763755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4739464273746535762351673 3554598205309901821763755)
                ·
                  refine ⟨5331897307964852732645633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554598205309901821763755 5331897307964852732645633)
                  ·
                    refine ⟨3998922980973639549484225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331897307964852732645633 3998922980973639549484225)
                    ·
                      refine ⟨2999192235730229662113169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998922980973639549484225 2999192235730229662113169)
                      ·
                        rfl

theorem cell23_5840906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_5840906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840906 prefixEnd_5840906 := by exact prefixLift 5840906
  have htrace : WordTrace (prefixWord ++ tailWord_5840906) baseStart_5840906 baseEnd_5840906 := by
    simpa [prefixWord, tailWord_5840906, baseEnd_5840906] using wordTrace_append hprefix tailTrace_5840906
  have hstable : (prefixWord ++ tailWord_5840906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840906).length < 2 ^ (prefixWord ++ tailWord_5840906).sum := by decide
  have hdescent : baseEnd_5840906 < baseStart_5840906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840916 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5840916 : Nat := 118140960795 + 5840916 * 2 ^ 59
def prefixEnd_5840916 : Nat := 4983230072969 + 3 ^ 40 * 5840916 * 2
def baseEnd_5840916 : Nat := 999732456845591540996041

theorem tailTrace_5840916 : CollatzResearch.WordTrace tailWord_5840916 prefixEnd_5840916 999732456845591540996041 := by
  unfold tailWord_5840916
  simp only [CollatzResearch.WordTrace]
  refine ⟨106517854053683177939487301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142023805404910903919316401 106517854053683177939487301)
  ·
    refine ⟨19972097635065595863653869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106517854053683177939487301 19972097635065595863653869)
    ·
      refine ⟨7489536613149598448870201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19972097635065595863653869 7489536613149598448870201)
      ·
        refine ⟨5617152459862198836652651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7489536613149598448870201 5617152459862198836652651)
        ·
          refine ⟨8425728689793298254978977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617152459862198836652651 8425728689793298254978977)
          ·
            refine ⟨6319296517344973691234233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8425728689793298254978977 6319296517344973691234233)
            ·
              refine ⟨4739472388008730268425675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6319296517344973691234233 4739472388008730268425675)
              ·
                refine ⟨7109208582013095402638513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739472388008730268425675 7109208582013095402638513)
                ·
                  refine ⟨5331906436509821551978885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109208582013095402638513 5331906436509821551978885)
                  ·
                    refine ⟨999732456845591540996041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5331906436509821551978885 999732456845591540996041)
                    ·
                      rfl

theorem cell23_5840916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5840916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840916 prefixEnd_5840916 := by exact prefixLift 5840916
  have htrace : WordTrace (prefixWord ++ tailWord_5840916) baseStart_5840916 baseEnd_5840916 := by
    simpa [prefixWord, tailWord_5840916, baseEnd_5840916] using wordTrace_append hprefix tailTrace_5840916
  have hstable : (prefixWord ++ tailWord_5840916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840916).length < 2 ^ (prefixWord ++ tailWord_5840916).sum := by decide
  have hdescent : baseEnd_5840916 < baseStart_5840916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840922 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_5840922 : Nat := 118140960795 + 5840922 * 2 ^ 59
def prefixEnd_5840922 : Nat := 4983230072969 + 3 ^ 40 * 5840922 * 2
def baseEnd_5840922 : Nat := 2999200451420701599513095

theorem tailTrace_5840922 : CollatzResearch.WordTrace tailWord_5840922 prefixEnd_5840922 2999200451420701599513095 := by
  unfold tailWord_5840922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53258981736336154725923255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142023951296896412602462013 53258981736336154725923255)
  ·
    refine ⟨79888472604504232088884883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53258981736336154725923255 79888472604504232088884883)
    ·
      refine ⟨119832708906756348133327325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79888472604504232088884883 119832708906756348133327325)
      ·
        refine ⟨44937265840033630549997747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119832708906756348133327325 44937265840033630549997747)
        ·
          refine ⟨67405898760050445824996621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44937265840033630549997747 67405898760050445824996621)
          ·
            refine ⟨25277212035018917184373733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67405898760050445824996621 25277212035018917184373733)
            ·
              refine ⟨4739477256566046972070075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25277212035018917184373733 4739477256566046972070075)
              ·
                refine ⟨7109215884849070458105113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739477256566046972070075 7109215884849070458105113)
                ·
                  refine ⟨5331911913636802843578835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109215884849070458105113 5331911913636802843578835)
                  ·
                    refine ⟨7997867870455204265368253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331911913636802843578835 7997867870455204265368253)
                    ·
                      refine ⟨2999200451420701599513095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7997867870455204265368253 2999200451420701599513095)
                      ·
                        rfl

theorem cell23_5840922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_5840922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840922 prefixEnd_5840922 := by exact prefixLift 5840922
  have htrace : WordTrace (prefixWord ++ tailWord_5840922) baseStart_5840922 baseEnd_5840922 := by
    simpa [prefixWord, tailWord_5840922, baseEnd_5840922] using wordTrace_append hprefix tailTrace_5840922
  have hstable : (prefixWord ++ tailWord_5840922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840922).length < 2 ^ (prefixWord ++ tailWord_5840922).sum := by decide
  have hdescent : baseEnd_5840922 < baseStart_5840922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840931 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_5840931 : Nat := 118140960795 + 5840931 * 2 ^ 59
def prefixEnd_5840931 : Nat := 4983230072969 + 3 ^ 40 * 5840931 * 2
def baseEnd_5840931 : Nat := 2999205072746592064300553

theorem tailTrace_5840931 : CollatzResearch.WordTrace tailWord_5840931 prefixEnd_5840931 2999205072746592064300553 := by
  unfold tailWord_5840931
  simp only [CollatzResearch.WordTrace]
  refine ⟨213036255202312013440770647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142024170134874675627180431 213036255202312013440770647)
  ·
    refine ⟨319554382803468020161155971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213036255202312013440770647 319554382803468020161155971)
    ·
      refine ⟨479331574205202030241733957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319554382803468020161155971 479331574205202030241733957)
      ·
        refine ⟨89874670163475380670325117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 479331574205202030241733957 89874670163475380670325117)
        ·
          refine ⟨33703001311303267751371919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89874670163475380670325117 33703001311303267751371919)
          ·
            refine ⟨50554501966954901627057879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33703001311303267751371919 50554501966954901627057879)
            ·
              refine ⟨75831752950432352440586819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50554501966954901627057879 75831752950432352440586819)
              ·
                refine ⟨113747629425648528660880229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75831752950432352440586819 113747629425648528660880229)
                ·
                  refine ⟨21327680517309099123915043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113747629425648528660880229 21327680517309099123915043)
                  ·
                    refine ⟨31991520775963648685872565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21327680517309099123915043 31991520775963648685872565)
                    ·
                      refine ⟨2999205072746592064300553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31991520775963648685872565 2999205072746592064300553)
                      ·
                        rfl

theorem cell23_5840931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_5840931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840931 prefixEnd_5840931 := by exact prefixLift 5840931
  have htrace : WordTrace (prefixWord ++ tailWord_5840931) baseStart_5840931 baseEnd_5840931 := by
    simpa [prefixWord, tailWord_5840931, baseEnd_5840931] using wordTrace_append hprefix tailTrace_5840931
  have hstable : (prefixWord ++ tailWord_5840931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840931).length < 2 ^ (prefixWord ++ tailWord_5840931).sum := by decide
  have hdescent : baseEnd_5840931 < baseStart_5840931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840932 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5840932 : Nat := 118140960795 + 5840932 * 2 ^ 59
def prefixEnd_5840932 : Nat := 4983230072969 + 3 ^ 40 * 5840932 * 2
def baseEnd_5840932 : Nat := 2999205586227246560388049

theorem tailTrace_5840932 : CollatzResearch.WordTrace tailWord_5840932 prefixEnd_5840932 2999205586227246560388049 := by
  unfold tailWord_5840932
  simp only [CollatzResearch.WordTrace]
  refine ⟨106518145837654195305778525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142024194450205593741038033 106518145837654195305778525)
  ·
    refine ⟨39944304689120323239666947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106518145837654195305778525 39944304689120323239666947)
    ·
      refine ⟨59916457033680484859500421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39944304689120323239666947 59916457033680484859500421)
      ·
        refine ⟨11234335693815090911156329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59916457033680484859500421 11234335693815090911156329)
        ·
          refine ⟨8425751770361318183367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11234335693815090911156329 8425751770361318183367247)
          ·
            refine ⟨12638627655541977275050871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425751770361318183367247 12638627655541977275050871)
            ·
              refine ⟨18957941483312965912576307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638627655541977275050871 18957941483312965912576307)
              ·
                refine ⟨28436912224969448868864461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18957941483312965912576307 28436912224969448868864461)
                ·
                  refine ⟨10663842084363543325824173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28436912224969448868864461 10663842084363543325824173)
                  ·
                    refine ⟨3998940781636328747184065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10663842084363543325824173 3998940781636328747184065)
                    ·
                      refine ⟨2999205586227246560388049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998940781636328747184065 2999205586227246560388049)
                      ·
                        rfl

theorem cell23_5840932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5840932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840932 prefixEnd_5840932 := by exact prefixLift 5840932
  have htrace : WordTrace (prefixWord ++ tailWord_5840932) baseStart_5840932 baseEnd_5840932 := by
    simpa [prefixWord, tailWord_5840932, baseEnd_5840932] using wordTrace_append hprefix tailTrace_5840932
  have hstable : (prefixWord ++ tailWord_5840932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840932).length < 2 ^ (prefixWord ++ tailWord_5840932).sum := by decide
  have hdescent : baseEnd_5840932 < baseStart_5840932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840945 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_5840945 : Nat := 118140960795 + 5840945 * 2 ^ 59
def prefixEnd_5840945 : Nat := 4983230072969 + 3 ^ 40 * 5840945 * 2
def baseEnd_5840945 : Nat := 2999212261475755009525489

theorem tailTrace_5840945 : CollatzResearch.WordTrace tailWord_5840945 prefixEnd_5840945 2999212261475755009525489 := by
  unfold tailWord_5840945
  simp only [CollatzResearch.WordTrace]
  refine ⟨213036765824261293831780289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142024510549507529221186859 213036765824261293831780289)
  ·
    refine ⟨159777574368195970373835217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213036765824261293831780289 159777574368195970373835217)
    ·
      refine ⟨119833180776146977780376413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159777574368195970373835217 119833180776146977780376413)
      ·
        refine ⟨44937442791055116667641155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119833180776146977780376413 44937442791055116667641155)
        ·
          refine ⟨67406164186582675001461733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44937442791055116667641155 67406164186582675001461733)
          ·
            refine ⟨12638655784984251562774075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67406164186582675001461733 12638655784984251562774075)
            ·
              refine ⟨18957983677476377344161113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638655784984251562774075 18957983677476377344161113)
              ·
                refine ⟨14218487758107283008120835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18957983677476377344161113 14218487758107283008120835)
                ·
                  refine ⟨21327731637160924512181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14218487758107283008120835 21327731637160924512181253)
                  ·
                    refine ⟨3998949681967673346033985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21327731637160924512181253 3998949681967673346033985)
                    ·
                      refine ⟨2999212261475755009525489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3998949681967673346033985 2999212261475755009525489)
                      ·
                        rfl

theorem cell23_5840945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_5840945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840945 prefixEnd_5840945 := by exact prefixLift 5840945
  have htrace : WordTrace (prefixWord ++ tailWord_5840945) baseStart_5840945 baseEnd_5840945 := by
    simpa [prefixWord, tailWord_5840945, baseEnd_5840945] using wordTrace_append hprefix tailTrace_5840945
  have hstable : (prefixWord ++ tailWord_5840945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840945).length < 2 ^ (prefixWord ++ tailWord_5840945).sum := by decide
  have hdescent : baseEnd_5840945 < baseStart_5840945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5840991 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_5840991 : Nat := 118140960795 + 5840991 * 2 ^ 59
def prefixEnd_5840991 : Nat := 4983230072969 + 3 ^ 40 * 5840991 * 2
def baseEnd_5840991 : Nat := 2999235881585861829550277

theorem tailTrace_5840991 : CollatzResearch.WordTrace tailWord_5840991 prefixEnd_5840991 2999235881585861829550277 := by
  unfold tailWord_5840991
  simp only [CollatzResearch.WordTrace]
  refine ⟨213038443582094643687954827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142025629054729762458636551 213038443582094643687954827)
  ·
    refine ⟨319557665373141965531932241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213038443582094643687954827 319557665373141965531932241)
    ·
      refine ⟨239668249029856474148949181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319557665373141965531932241 239668249029856474148949181)
      ·
        refine ⟨89875593386196177805855943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239668249029856474148949181 89875593386196177805855943)
        ·
          refine ⟨134813390079294266708783915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89875593386196177805855943 134813390079294266708783915)
          ·
            refine ⟨202220085118941400063175873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134813390079294266708783915 202220085118941400063175873)
            ·
              refine ⟨151665063839206050047381905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202220085118941400063175873 151665063839206050047381905)
              ·
                refine ⟨113748797879404537535536429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151665063839206050047381905 113748797879404537535536429)
                ·
                  refine ⟨42655799204776701575826161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113748797879404537535536429 42655799204776701575826161)
                  ·
                    refine ⟨31991849403582526181869621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42655799204776701575826161 31991849403582526181869621)
                    ·
                      refine ⟨2999235881585861829550277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31991849403582526181869621 2999235881585861829550277)
                      ·
                        rfl

theorem cell23_5840991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_5840991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5840991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5840991 prefixEnd_5840991 := by exact prefixLift 5840991
  have htrace : WordTrace (prefixWord ++ tailWord_5840991) baseStart_5840991 baseEnd_5840991 := by
    simpa [prefixWord, tailWord_5840991, baseEnd_5840991] using wordTrace_append hprefix tailTrace_5840991
  have hstable : (prefixWord ++ tailWord_5840991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5840991).length < 2 ^ (prefixWord ++ tailWord_5840991).sum := by decide
  have hdescent : baseEnd_5840991 < baseStart_5840991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5840991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841002 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_5841002 : Nat := 118140960795 + 5841002 * 2 ^ 59
def prefixEnd_5841002 : Nat := 4983230072969 + 3 ^ 40 * 5841002 * 2
def baseEnd_5841002 : Nat := 333249058874784587390303

theorem tailTrace_5841002 : CollatzResearch.WordTrace tailWord_5841002 prefixEnd_5841002 333249058874784587390303 := by
  unfold tailWord_5841002
  simp only [CollatzResearch.WordTrace]
  refine ⟨53259711196263698141651315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142025896523369861711070173 53259711196263698141651315)
  ·
    refine ⟨79889566794395547212476973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53259711196263698141651315 79889566794395547212476973)
    ·
      refine ⟨29958587547898330204678865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79889566794395547212476973 29958587547898330204678865)
      ·
        refine ⟨22468940660923747653509149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29958587547898330204678865 22468940660923747653509149)
        ·
          refine ⟨8425852747846405370065931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22468940660923747653509149 8425852747846405370065931)
          ·
            refine ⟨12638779121769608055098897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425852747846405370065931 12638779121769608055098897)
            ·
              refine ⟨9479084341327206041324173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12638779121769608055098897 9479084341327206041324173)
              ·
                refine ⟨3554656627997702265496565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9479084341327206041324173 3554656627997702265496565)
                ·
                  refine ⟨333249058874784587390303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3554656627997702265496565 333249058874784587390303)
                  ·
                    rfl

theorem cell23_5841002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_5841002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841002 prefixEnd_5841002 := by exact prefixLift 5841002
  have htrace : WordTrace (prefixWord ++ tailWord_5841002) baseStart_5841002 baseEnd_5841002 := by
    simpa [prefixWord, tailWord_5841002, baseEnd_5841002] using wordTrace_append hprefix tailTrace_5841002
  have hstable : (prefixWord ++ tailWord_5841002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841002).length < 2 ^ (prefixWord ++ tailWord_5841002).sum := by decide
  have hdescent : baseEnd_5841002 < baseStart_5841002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841055 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5841055 : Nat := 118140960795 + 5841055 * 2 ^ 59
def prefixEnd_5841055 : Nat := 4983230072969 + 3 ^ 40 * 5841055 * 2
def baseEnd_5841055 : Nat := 2999268744347749579149983

theorem tailTrace_5841055 : CollatzResearch.WordTrace tailWord_5841055 prefixEnd_5841055 2999268744347749579149983 := by
  unfold tailWord_5841055
  simp only [CollatzResearch.WordTrace]
  refine ⟨213040777853862782618284619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142027185235908521745523079 213040777853862782618284619)
  ·
    refine ⟨319561166780794173927426929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213040777853862782618284619 319561166780794173927426929)
    ·
      refine ⟨239670875085595630445570197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319561166780794173927426929 239670875085595630445570197)
      ·
        refine ⟨11234572269637295177136103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 239670875085595630445570197 11234572269637295177136103)
        ·
          refine ⟨16851858404455942765704155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11234572269637295177136103 16851858404455942765704155)
          ·
            refine ⟨25277787606683914148556233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16851858404455942765704155 25277787606683914148556233)
            ·
              refine ⟨18958340705012935611417175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25277787606683914148556233 18958340705012935611417175)
              ·
                refine ⟨28437511057519403417125763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18958340705012935611417175 28437511057519403417125763)
                ·
                  refine ⟨42656266586279105125688645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28437511057519403417125763 42656266586279105125688645)
                  ·
                    refine ⟨7998049984927332211066621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42656266586279105125688645 7998049984927332211066621)
                    ·
                      refine ⟨2999268744347749579149983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7998049984927332211066621 2999268744347749579149983)
                      ·
                        rfl

theorem cell23_5841055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5841055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841055 prefixEnd_5841055 := by exact prefixLift 5841055
  have htrace : WordTrace (prefixWord ++ tailWord_5841055) baseStart_5841055 baseEnd_5841055 := by
    simpa [prefixWord, tailWord_5841055, baseEnd_5841055] using wordTrace_append hprefix tailTrace_5841055
  have hstable : (prefixWord ++ tailWord_5841055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841055).length < 2 ^ (prefixWord ++ tailWord_5841055).sum := by decide
  have hdescent : baseEnd_5841055 < baseStart_5841055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841079 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 1, 4]
def baseStart_5841079 : Nat := 118140960795 + 5841079 * 2 ^ 59
def prefixEnd_5841079 : Nat := 4983230072969 + 3 ^ 40 * 5841079 * 2
def baseEnd_5841079 : Nat := 999760355961152495083291

theorem tailTrace_5841079 : CollatzResearch.WordTrace tailWord_5841079 prefixEnd_5841079 999760355961152495083291 := by
  unfold tailWord_5841079
  simp only [CollatzResearch.WordTrace]
  refine ⟨213041653205775834717158291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142027768803850556478105527 213041653205775834717158291)
  ·
    refine ⟨319562479808663752075737437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213041653205775834717158291 319562479808663752075737437)
    ·
      refine ⟨119835929928248907028401539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319562479808663752075737437 119835929928248907028401539)
      ·
        refine ⟨179753894892373360542602309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119835929928248907028401539 179753894892373360542602309)
        ·
          refine ⟨33703855292320005101737933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179753894892373360542602309 33703855292320005101737933)
          ·
            refine ⟨12638945734620001913151725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33703855292320005101737933 12638945734620001913151725)
            ·
              refine ⟨4739604650482500717431897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12638945734620001913151725 4739604650482500717431897)
              ·
                refine ⟨3554703487861875538073923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4739604650482500717431897 3554703487861875538073923)
                ·
                  refine ⟨5332055231792813307110885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554703487861875538073923 5332055231792813307110885)
                  ·
                    refine ⟨999760355961152495083291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5332055231792813307110885 999760355961152495083291)
                    ·
                      rfl

theorem cell23_5841079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_5841079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841079 prefixEnd_5841079 := by exact prefixLift 5841079
  have htrace : WordTrace (prefixWord ++ tailWord_5841079) baseStart_5841079 baseEnd_5841079 := by
    simpa [prefixWord, tailWord_5841079, baseEnd_5841079] using wordTrace_append hprefix tailTrace_5841079
  have hstable : (prefixWord ++ tailWord_5841079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841079).length < 2 ^ (prefixWord ++ tailWord_5841079).sum := by decide
  have hdescent : baseEnd_5841079 < baseStart_5841079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841092 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 6]
def baseStart_5841092 : Nat := 118140960795 + 5841092 * 2 ^ 59
def prefixEnd_5841092 : Nat := 4983230072969 + 3 ^ 40 * 5841092 * 2
def baseEnd_5841092 : Nat := 333254193681329548265257

theorem tailTrace_5841092 : CollatzResearch.WordTrace tailWord_5841092 prefixEnd_5841092 333254193681329548265257 := by
  unfold tailWord_5841092
  simp only [CollatzResearch.WordTrace]
  refine ⟨106521063677364368968690765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142028084903152491958254353 106521063677364368968690765)
  ·
    refine ⟨39945398879011638363259037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106521063677364368968690765 39945398879011638363259037)
    ·
      refine ⟨14979524579629364386222139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39945398879011638363259037 14979524579629364386222139)
      ·
        refine ⟨22469286869444046579333209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14979524579629364386222139 22469286869444046579333209)
        ·
          refine ⟨16851965152083034934499907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22469286869444046579333209 16851965152083034934499907)
          ·
            refine ⟨25277947728124552401749861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16851965152083034934499907 25277947728124552401749861)
            ·
              refine ⟨4739615199023353575328099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25277947728124552401749861 4739615199023353575328099)
              ·
                refine ⟨7109422798535030362992149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739615199023353575328099 7109422798535030362992149)
                ·
                  refine ⟨333254193681329548265257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7109422798535030362992149 333254193681329548265257)
                  ·
                    rfl

theorem cell23_5841092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_5841092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841092 prefixEnd_5841092 := by exact prefixLift 5841092
  have htrace : WordTrace (prefixWord ++ tailWord_5841092) baseStart_5841092 baseEnd_5841092 := by
    simpa [prefixWord, tailWord_5841092, baseEnd_5841092] using wordTrace_append hprefix tailTrace_5841092
  have hstable : (prefixWord ++ tailWord_5841092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841092).length < 2 ^ (prefixWord ++ tailWord_5841092).sum := by decide
  have hdescent : baseEnd_5841092 < baseStart_5841092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841105 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_5841105 : Nat := 118140960795 + 5841105 * 2 ^ 59
def prefixEnd_5841105 : Nat := 4983230072969 + 3 ^ 40 * 5841105 * 2
def baseEnd_5841105 : Nat := 999764806126824794508251

theorem tailTrace_5841105 : CollatzResearch.WordTrace tailWord_5841105 prefixEnd_5841105 999764806126824794508251 := by
  unfold tailWord_5841105
  simp only [CollatzResearch.WordTrace]
  refine ⟨213042601503681641157604769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142028401002454427438403179 213042601503681641157604769)
  ·
    refine ⟨159781951127761230868203577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213042601503681641157604769 159781951127761230868203577)
    ·
      refine ⟨119836463345820923151152683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159781951127761230868203577 119836463345820923151152683)
      ·
        refine ⟨179754695018731384726729025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119836463345820923151152683 179754695018731384726729025)
        ·
          refine ⟨134816021264048538545046769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179754695018731384726729025 134816021264048538545046769)
          ·
            refine ⟨101112015948036403908785077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134816021264048538545046769 101112015948036403908785077)
            ·
              refine ⟨9479251495128412866448601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101112015948036403908785077 9479251495128412866448601)
              ·
                refine ⟨7109438621346309649836451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9479251495128412866448601 7109438621346309649836451)
                ·
                  refine ⟨10664157932019464474754677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7109438621346309649836451 10664157932019464474754677)
                  ·
                    refine ⟨999764806126824794508251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10664157932019464474754677 999764806126824794508251)
                    ·
                      rfl

theorem cell23_5841105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_5841105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841105 prefixEnd_5841105 := by exact prefixLift 5841105
  have htrace : WordTrace (prefixWord ++ tailWord_5841105) baseStart_5841105 baseEnd_5841105 := by
    simpa [prefixWord, tailWord_5841105, baseEnd_5841105] using wordTrace_append hprefix tailTrace_5841105
  have hstable : (prefixWord ++ tailWord_5841105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841105).length < 2 ^ (prefixWord ++ tailWord_5841105).sum := by decide
  have hdescent : baseEnd_5841105 < baseStart_5841105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841112 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_5841112 : Nat := 118140960795 + 5841112 * 2 ^ 59
def prefixEnd_5841112 : Nat := 4983230072969 + 3 ^ 40 * 5841112 * 2
def baseEnd_5841112 : Nat := 2999298012745055856137221

theorem tailTrace_5841112 : CollatzResearch.WordTrace tailWord_5841112 prefixEnd_5841112 2999298012745055856137221 := by
  unfold tailWord_5841112
  simp only [CollatzResearch.WordTrace]
  refine ⟨106521428407328140676554795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142028571209770854235406393 106521428407328140676554795)
  ·
    refine ⟨159782142610992211014832193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106521428407328140676554795 159782142610992211014832193)
    ·
      refine ⟨119836606958244158261124145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159782142610992211014832193 119836606958244158261124145)
      ·
        refine ⟨89877455218683118695843109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119836606958244158261124145 89877455218683118695843109)
        ·
          refine ⟨16852022853503084755470583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89877455218683118695843109 16852022853503084755470583)
          ·
            refine ⟨25278034280254627133205875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16852022853503084755470583 25278034280254627133205875)
            ·
              refine ⟨37917051420381940699808813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25278034280254627133205875 37917051420381940699808813)
              ·
                refine ⟨14218894282643227762428305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37917051420381940699808813 14218894282643227762428305)
                ·
                  refine ⟨10664170711982420821821229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14218894282643227762428305 10664170711982420821821229)
                  ·
                    refine ⟨3999064016993407808182961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10664170711982420821821229 3999064016993407808182961)
                    ·
                      refine ⟨2999298012745055856137221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999064016993407808182961 2999298012745055856137221)
                      ·
                        rfl

theorem cell23_5841112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_5841112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841112 prefixEnd_5841112 := by exact prefixLift 5841112
  have htrace : WordTrace (prefixWord ++ tailWord_5841112) baseStart_5841112 baseEnd_5841112 := by
    simpa [prefixWord, tailWord_5841112, baseEnd_5841112] using wordTrace_append hprefix tailTrace_5841112
  have hstable : (prefixWord ++ tailWord_5841112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841112).length < 2 ^ (prefixWord ++ tailWord_5841112).sum := by decide
  have hdescent : baseEnd_5841112 < baseStart_5841112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841155 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4]
def baseStart_5841155 : Nat := 118140960795 + 5841155 * 2 ^ 59
def prefixEnd_5841155 : Nat := 4983230072969 + 3 ^ 40 * 5841155 * 2
def baseEnd_5841155 : Nat := 2999320092413199187899523

theorem tailTrace_5841155 : CollatzResearch.WordTrace tailWord_5841155 prefixEnd_5841155 2999320092413199187899523 := by
  unfold tailWord_5841155
  simp only [CollatzResearch.WordTrace]
  refine ⟨213044425153500499696924919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142029616769000333131283279 213044425153500499696924919)
  ·
    refine ⟨319566637730250749545387379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213044425153500499696924919 319566637730250749545387379)
    ·
      refine ⟨479349956595376124318081069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319566637730250749545387379 479349956595376124318081069)
      ·
        refine ⟨179756233723266046619280401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479349956595376124318081069 179756233723266046619280401)
        ·
          refine ⟨134817175292449534964460301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179756233723266046619280401 134817175292449534964460301)
          ·
            refine ⟨50556440734668575611672613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134817175292449534964460301 50556440734668575611672613)
            ·
              refine ⟨9479332637750357927188615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50556440734668575611672613 9479332637750357927188615)
              ·
                refine ⟨14218998956625536890782923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9479332637750357927188615 14218998956625536890782923)
                ·
                  refine ⟨21328498434938305336174385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14218998956625536890782923 21328498434938305336174385)
                  ·
                    refine ⟨15996373826203729002130789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21328498434938305336174385 15996373826203729002130789)
                    ·
                      refine ⟨2999320092413199187899523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15996373826203729002130789 2999320092413199187899523)
                      ·
                        rfl

theorem cell23_5841155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_5841155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841155 prefixEnd_5841155 := by exact prefixLift 5841155
  have htrace : WordTrace (prefixWord ++ tailWord_5841155) baseStart_5841155 baseEnd_5841155 := by
    simpa [prefixWord, tailWord_5841155, baseEnd_5841155] using wordTrace_append hprefix tailTrace_5841155
  have hstable : (prefixWord ++ tailWord_5841155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841155).length < 2 ^ (prefixWord ++ tailWord_5841155).sum := by decide
  have hdescent : baseEnd_5841155 < baseStart_5841155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841176 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 1, 2, 2]
def baseStart_5841176 : Nat := 118140960795 + 5841176 * 2 ^ 59
def prefixEnd_5841176 : Nat := 4983230072969 + 3 ^ 40 * 5841176 * 2
def baseEnd_5841176 : Nat := 2999330875506943605736927

theorem tailTrace_5841176 : CollatzResearch.WordTrace tailWord_5841176 prefixEnd_5841176 2999330875506943605736927 := by
  unfold tailWord_5841176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106522595543212210141719691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142030127390949613522292921 106522595543212210141719691)
  ·
    refine ⟨159783893314818315212579537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106522595543212210141719691 159783893314818315212579537)
    ·
      refine ⟨119837919986113736409434653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159783893314818315212579537 119837919986113736409434653)
      ·
        refine ⟨44939219994792651153537995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119837919986113736409434653 44939219994792651153537995)
        ·
          refine ⟨67408829992188976730306993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44939219994792651153537995 67408829992188976730306993)
          ·
            refine ⟨50556622494141732547730245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67408829992188976730306993 50556622494141732547730245)
            ·
              refine ⟨9479366717651574852699421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50556622494141732547730245 9479366717651574852699421)
              ·
                refine ⟨3554762519119340569762283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9479366717651574852699421 3554762519119340569762283)
                ·
                  refine ⟨5332143778679010854643425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554762519119340569762283 5332143778679010854643425)
                  ·
                    refine ⟨3999107834009258140982569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332143778679010854643425 3999107834009258140982569)
                    ·
                      refine ⟨2999330875506943605736927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999107834009258140982569 2999330875506943605736927)
                      ·
                        rfl

theorem cell23_5841176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_5841176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841176 prefixEnd_5841176 := by exact prefixLift 5841176
  have htrace : WordTrace (prefixWord ++ tailWord_5841176) baseStart_5841176 baseEnd_5841176 := by
    simpa [prefixWord, tailWord_5841176, baseEnd_5841176] using wordTrace_append hprefix tailTrace_5841176
  have hstable : (prefixWord ++ tailWord_5841176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841176).length < 2 ^ (prefixWord ++ tailWord_5841176).sum := by decide
  have hdescent : baseEnd_5841176 < baseStart_5841176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841182 : List Nat := [4, 3, 2, 1, 1, 2, 10]
def baseStart_5841182 : Nat := 118140960795 + 5841182 * 2 ^ 59
def prefixEnd_5841182 : Nat := 4983230072969 + 3 ^ 40 * 5841182 * 2
def baseEnd_5841182 : Nat := 37028814276430501015579

theorem tailTrace_5841182 : CollatzResearch.WordTrace tailWord_5841182 prefixEnd_5841182 37028814276430501015579 := by
  unfold tailWord_5841182
  simp only [CollatzResearch.WordTrace]
  refine ⟨26630676240550335413519725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142030273282935122205438533 26630676240550335413519725)
  ·
    refine ⟨9986503590206375780069897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26630676240550335413519725 9986503590206375780069897)
    ·
      refine ⟨7489877692654781835052423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9986503590206375780069897 7489877692654781835052423)
      ·
        refine ⟨11234816538982172752578635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7489877692654781835052423 11234816538982172752578635)
        ·
          refine ⟨16852224808473259128867953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11234816538982172752578635 16852224808473259128867953)
          ·
            refine ⟨12639168606354944346650965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16852224808473259128867953 12639168606354944346650965)
            ·
              refine ⟨37028814276430501015579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12639168606354944346650965 37028814276430501015579)
              ·
                rfl

theorem cell23_5841182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 10].length) (baseStart_5841182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841182 prefixEnd_5841182 := by exact prefixLift 5841182
  have htrace : WordTrace (prefixWord ++ tailWord_5841182) baseStart_5841182 baseEnd_5841182 := by
    simpa [prefixWord, tailWord_5841182, baseEnd_5841182] using wordTrace_append hprefix tailTrace_5841182
  have hstable : (prefixWord ++ tailWord_5841182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841182).length < 2 ^ (prefixWord ++ tailWord_5841182).sum := by decide
  have hdescent : baseEnd_5841182 < baseStart_5841182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841209 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5841209 : Nat := 118140960795 + 5841209 * 2 ^ 59
def prefixEnd_5841209 : Nat := 4983230072969 + 3 ^ 40 * 5841209 * 2
def baseEnd_5841209 : Nat := 2999347820368541976624275

theorem tailTrace_5841209 : CollatzResearch.WordTrace tailWord_5841209 prefixEnd_5841209 2999347820368541976624275 := by
  unfold tailWord_5841209
  simp only [CollatzResearch.WordTrace]
  refine ⟨213046394695304866919390681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142030929796869911279593787 213046394695304866919390681)
  ·
    refine ⟨159784796021478650189543011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213046394695304866919390681 159784796021478650189543011)
    ·
      refine ⟨239677194032217975284314517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159784796021478650189543011 239677194032217975284314517)
      ·
        refine ⟨11234868470260217591452243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 239677194032217975284314517 11234868470260217591452243)
        ·
          refine ⟨16852302705390326387178365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11234868470260217591452243 16852302705390326387178365)
          ·
            refine ⟨6319613514521372395191887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16852302705390326387178365 6319613514521372395191887)
            ·
              refine ⟨9479420271782058592787831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319613514521372395191887 9479420271782058592787831)
              ·
                refine ⟨14219130407673087889181747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9479420271782058592787831 14219130407673087889181747)
                ·
                  refine ⟨21328695611509631833772621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14219130407673087889181747 21328695611509631833772621)
                  ·
                    refine ⟨7998260854316111937664733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21328695611509631833772621 7998260854316111937664733)
                    ·
                      refine ⟨2999347820368541976624275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7998260854316111937664733 2999347820368541976624275)
                      ·
                        rfl

theorem cell23_5841209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5841209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841209 prefixEnd_5841209 := by exact prefixLift 5841209
  have htrace : WordTrace (prefixWord ++ tailWord_5841209) baseStart_5841209 baseEnd_5841209 := by
    simpa [prefixWord, tailWord_5841209, baseEnd_5841209] using wordTrace_append hprefix tailTrace_5841209
  have hstable : (prefixWord ++ tailWord_5841209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841209).length < 2 ^ (prefixWord ++ tailWord_5841209).sum := by decide
  have hdescent : baseEnd_5841209 < baseStart_5841209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841265 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_5841265 : Nat := 118140960795 + 5841265 * 2 ^ 59
def prefixEnd_5841265 : Nat := 4983230072969 + 3 ^ 40 * 5841265 * 2
def baseEnd_5841265 : Nat := 2999376575285193757524017

theorem tailTrace_5841265 : CollatzResearch.WordTrace tailWord_5841265 prefixEnd_5841265 2999376575285193757524017 := by
  unfold tailWord_5841265
  simp only [CollatzResearch.WordTrace]
  refine ⟨213048437183101988483429249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142032291455401325655619499 213048437183101988483429249)
  ·
    refine ⟨159786327887326491362571937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213048437183101988483429249 159786327887326491362571937)
    ·
      refine ⟨119839745915494868521928953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159786327887326491362571937 119839745915494868521928953)
      ·
        refine ⟨89879809436621151391446715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119839745915494868521928953 89879809436621151391446715)
        ·
          refine ⟨134819714154931727087170073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89879809436621151391446715 134819714154931727087170073)
          ·
            refine ⟨101114785616198795315377555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134819714154931727087170073 101114785616198795315377555)
            ·
              refine ⟨151672178424298192973066333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101114785616198795315377555 151672178424298192973066333)
              ·
                refine ⟨56877066909111822364899875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151672178424298192973066333 56877066909111822364899875)
                ·
                  refine ⟨85315600363667733547349813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56877066909111822364899875 85315600363667733547349813)
                  ·
                    refine ⟨7998337534093850020064045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85315600363667733547349813 7998337534093850020064045)
                    ·
                      refine ⟨2999376575285193757524017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7998337534093850020064045 2999376575285193757524017)
                      ·
                        rfl

theorem cell23_5841265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_5841265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841265 prefixEnd_5841265 := by exact prefixLift 5841265
  have htrace : WordTrace (prefixWord ++ tailWord_5841265) baseStart_5841265 baseEnd_5841265 := by
    simpa [prefixWord, tailWord_5841265, baseEnd_5841265] using wordTrace_append hprefix tailTrace_5841265
  have hstable : (prefixWord ++ tailWord_5841265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841265).length < 2 ^ (prefixWord ++ tailWord_5841265).sum := by decide
  have hdescent : baseEnd_5841265 < baseStart_5841265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841266 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_5841266 : Nat := 118140960795 + 5841266 * 2 ^ 59
def prefixEnd_5841266 : Nat := 4983230072969 + 3 ^ 40 * 5841266 * 2
def baseEnd_5841266 : Nat := 2999377088765848253611513

theorem tailTrace_5841266 : CollatzResearch.WordTrace tailWord_5841266 prefixEnd_5841266 2999377088765848253611513 := by
  unfold tailWord_5841266
  simp only [CollatzResearch.WordTrace]
  refine ⟨53262118414024591413553913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142032315770732243769477101 53262118414024591413553913)
  ·
    refine ⟨39946588810518443560165435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53262118414024591413553913 39946588810518443560165435)
    ·
      refine ⟨59919883215777665340248153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39946588810518443560165435 59919883215777665340248153)
      ·
        refine ⟨44939912411833249005186115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59919883215777665340248153 44939912411833249005186115)
        ·
          refine ⟨67409868617749873507779173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44939912411833249005186115 67409868617749873507779173)
          ·
            refine ⟨12639350365828101282708595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67409868617749873507779173 12639350365828101282708595)
            ·
              refine ⟨18959025548742151924062893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12639350365828101282708595 18959025548742151924062893)
              ·
                refine ⟨7109634580778306971523585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18959025548742151924062893 7109634580778306971523585)
                ·
                  refine ⟨5332225935583730228642689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109634580778306971523585 5332225935583730228642689)
                  ·
                    refine ⟨3999169451687797671482017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332225935583730228642689 3999169451687797671482017)
                    ·
                      refine ⟨2999377088765848253611513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999169451687797671482017 2999377088765848253611513)
                      ·
                        rfl

theorem cell23_5841266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_5841266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841266 prefixEnd_5841266 := by exact prefixLift 5841266
  have htrace : WordTrace (prefixWord ++ tailWord_5841266) baseStart_5841266 baseEnd_5841266 := by
    simpa [prefixWord, tailWord_5841266, baseEnd_5841266] using wordTrace_append hprefix tailTrace_5841266
  have hstable : (prefixWord ++ tailWord_5841266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841266).length < 2 ^ (prefixWord ++ tailWord_5841266).sum := by decide
  have hdescent : baseEnd_5841266 < baseStart_5841266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841270 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5841270 : Nat := 118140960795 + 5841270 * 2 ^ 59
def prefixEnd_5841270 : Nat := 4983230072969 + 3 ^ 40 * 5841270 * 2
def baseEnd_5841270 : Nat := 2999379142688466237961495

theorem tailTrace_5841270 : CollatzResearch.WordTrace tailWord_5841270 prefixEnd_5841270 2999379142688466237961495 := by
  unfold tailWord_5841270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13315538721755242146085079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142032413032055916224907509 13315538721755242146085079)
  ·
    refine ⟨19973308082632863219127619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13315538721755242146085079 19973308082632863219127619)
    ·
      refine ⟨29959962123949294828691429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19973308082632863219127619 29959962123949294828691429)
      ·
        refine ⟨5617492898240492780379643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29959962123949294828691429 5617492898240492780379643)
        ·
          refine ⟨8426239347360739170569465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617492898240492780379643 8426239347360739170569465)
          ·
            refine ⟨6319679510520554377927099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8426239347360739170569465 6319679510520554377927099)
            ·
              refine ⟨9479519265780831566890649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319679510520554377927099 9479519265780831566890649)
              ·
                refine ⟨7109639449335623675167987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9479519265780831566890649 7109639449335623675167987)
                ·
                  refine ⟨10664459174003435512751981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7109639449335623675167987 10664459174003435512751981)
                  ·
                    refine ⟨3999172190251288317281993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10664459174003435512751981 3999172190251288317281993)
                    ·
                      refine ⟨2999379142688466237961495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999172190251288317281993 2999379142688466237961495)
                      ·
                        rfl

theorem cell23_5841270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5841270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841270 prefixEnd_5841270 := by exact prefixLift 5841270
  have htrace : WordTrace (prefixWord ++ tailWord_5841270) baseStart_5841270 baseEnd_5841270 := by
    simpa [prefixWord, tailWord_5841270, baseEnd_5841270] using wordTrace_append hprefix tailTrace_5841270
  have hstable : (prefixWord ++ tailWord_5841270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841270).length < 2 ^ (prefixWord ++ tailWord_5841270).sum := by decide
  have hdescent : baseEnd_5841270 < baseStart_5841270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841306 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_5841306 : Nat := 118140960795 + 5841306 * 2 ^ 59
def prefixEnd_5841306 : Nat := 4983230072969 + 3 ^ 40 * 5841306 * 2
def baseEnd_5841306 : Nat := 333266403110225344123481

theorem tailTrace_5841306 : CollatzResearch.WordTrace tailWord_5841306 prefixEnd_5841306 333266403110225344123481 := by
  unfold tailWord_5841306
  simp only [CollatzResearch.WordTrace]
  refine ⟨53262483143988363121417943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142033288383968968323781181 53262483143988363121417943)
  ·
    refine ⟨79893724715982544682126915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53262483143988363121417943 79893724715982544682126915)
    ·
      refine ⟨119840587073973817023190373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79893724715982544682126915 119840587073973817023190373)
      ·
        refine ⟨22470110076370090691848195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119840587073973817023190373 22470110076370090691848195)
        ·
          refine ⟨33705165114555136037772293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22470110076370090691848195 33705165114555136037772293)
          ·
            refine ⟨6319718458979088007082305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33705165114555136037772293 6319718458979088007082305)
            ·
              refine ⟨4739788844234316005311729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6319718458979088007082305 4739788844234316005311729)
              ·
                refine ⟨3554841633175737003983797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4739788844234316005311729 3554841633175737003983797)
                ·
                  refine ⟨333266403110225344123481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3554841633175737003983797 333266403110225344123481)
                  ·
                    rfl

theorem cell23_5841306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_5841306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841306 prefixEnd_5841306 := by exact prefixLift 5841306
  have htrace : WordTrace (prefixWord ++ tailWord_5841306) baseStart_5841306 baseEnd_5841306 := by
    simpa [prefixWord, tailWord_5841306, baseEnd_5841306] using wordTrace_append hprefix tailTrace_5841306
  have hstable : (prefixWord ++ tailWord_5841306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841306).length < 2 ^ (prefixWord ++ tailWord_5841306).sum := by decide
  have hdescent : baseEnd_5841306 < baseStart_5841306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841366 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5841366 : Nat := 118140960795 + 5841366 * 2 ^ 59
def prefixEnd_5841366 : Nat := 4983230072969 + 3 ^ 40 * 5841366 * 2
def baseEnd_5841366 : Nat := 999809478943765954120351

theorem tailTrace_5841366 : CollatzResearch.WordTrace tailWord_5841366 prefixEnd_5841366 999809478943765954120351 := by
  unfold tailWord_5841366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13315757559733505170803497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142034747303824055155237301 13315757559733505170803497)
  ·
    refine ⟨9986818169800128878102623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13315757559733505170803497 9986818169800128878102623)
    ·
      refine ⟨14980227254700193317153935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986818169800128878102623 14980227254700193317153935)
      ·
        refine ⟨22470340882050289975730903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14980227254700193317153935 22470340882050289975730903)
        ·
          refine ⟨33705511323075434963596355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22470340882050289975730903 33705511323075434963596355)
          ·
            refine ⟨50558266984613152445394533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33705511323075434963596355 50558266984613152445394533)
            ·
              refine ⟨9479675059614966083511475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50558266984613152445394533 9479675059614966083511475)
              ·
                refine ⟨14219512589422449125267213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9479675059614966083511475 14219512589422449125267213)
                ·
                  refine ⟨5332317221033418421975205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14219512589422449125267213 5332317221033418421975205)
                  ·
                    refine ⟨999809478943765954120351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5332317221033418421975205 999809478943765954120351)
                    ·
                      rfl

theorem cell23_5841366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5841366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841366 prefixEnd_5841366 := by exact prefixLift 5841366
  have htrace : WordTrace (prefixWord ++ tailWord_5841366) baseStart_5841366 baseEnd_5841366 := by
    simpa [prefixWord, tailWord_5841366, baseEnd_5841366] using wordTrace_append hprefix tailTrace_5841366
  have hstable : (prefixWord ++ tailWord_5841366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841366).length < 2 ^ (prefixWord ++ tailWord_5841366).sum := by decide
  have hdescent : baseEnd_5841366 < baseStart_5841366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841409 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_5841409 : Nat := 118140960795 + 5841409 * 2 ^ 59
def prefixEnd_5841409 : Nat := 4983230072969 + 3 ^ 40 * 5841409 * 2
def baseEnd_5841409 : Nat := 999816838833147064707785

theorem tailTrace_5841409 : CollatzResearch.WordTrace tailWord_5841409 prefixEnd_5841409 999816838833147064707785 := by
  unfold tailWord_5841409
  simp only [CollatzResearch.WordTrace]
  refine ⟨213053689294580301076671281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142035792863053534051114187 213053689294580301076671281)
  ·
    refine ⟨159790266970935225807503461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213053689294580301076671281 159790266970935225807503461)
    ·
      refine ⟨29960675057050354838906899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159790266970935225807503461 29960675057050354838906899)
      ·
        refine ⟨44941012585575532258360349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29960675057050354838906899 44941012585575532258360349)
        ·
          refine ⟨16852879719590824596885131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44941012585575532258360349 16852879719590824596885131)
          ·
            refine ⟨25279319579386236895327697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16852879719590824596885131 25279319579386236895327697)
            ·
              refine ⟨18959489684539677671495773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25279319579386236895327697 18959489684539677671495773)
              ·
                refine ⟨7109808631702379126810915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18959489684539677671495773 7109808631702379126810915)
                ·
                  refine ⟨10664712947553568690216373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7109808631702379126810915 10664712947553568690216373)
                  ·
                    refine ⟨999816838833147064707785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10664712947553568690216373 999816838833147064707785)
                    ·
                      rfl

theorem cell23_5841409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_5841409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841409 prefixEnd_5841409 := by exact prefixLift 5841409
  have htrace : WordTrace (prefixWord ++ tailWord_5841409) baseStart_5841409 baseEnd_5841409 := by
    simpa [prefixWord, tailWord_5841409, baseEnd_5841409] using wordTrace_append hprefix tailTrace_5841409
  have hstable : (prefixWord ++ tailWord_5841409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841409).length < 2 ^ (prefixWord ++ tailWord_5841409).sum := by decide
  have hdescent : baseEnd_5841409 < baseStart_5841409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841460 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_5841460 : Nat := 118140960795 + 5841460 * 2 ^ 59
def prefixEnd_5841460 : Nat := 4983230072969 + 3 ^ 40 * 5841460 * 2
def baseEnd_5841460 : Nat := 999825568004273498195207

theorem tailTrace_5841460 : CollatzResearch.WordTrace tailWord_5841460 prefixEnd_5841460 999825568004273498195207 := by
  unfold tailWord_5841460
  simp only [CollatzResearch.WordTrace]
  refine ⟨106527774708697768393388917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142037032944930357857851889 106527774708697768393388917)
  ·
    refine ⟨9986978878940415786880211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106527774708697768393388917 9986978878940415786880211)
    ·
      refine ⟨14980468318410623680320317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986978878940415786880211 14980468318410623680320317)
      ·
        refine ⟨5617675619403983880120119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14980468318410623680320317 5617675619403983880120119)
        ·
          refine ⟨8426513429105975820180179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617675619403983880120119 8426513429105975820180179)
          ·
            refine ⟨12639770143658963730270269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8426513429105975820180179 12639770143658963730270269)
            ·
              refine ⟨4739913803872111398851351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12639770143658963730270269 4739913803872111398851351)
              ·
                refine ⟨7109870705808167098277027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739913803872111398851351 7109870705808167098277027)
                ·
                  refine ⟨10664806058712250647415541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7109870705808167098277027 10664806058712250647415541)
                  ·
                    refine ⟨999825568004273498195207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10664806058712250647415541 999825568004273498195207)
                    ·
                      rfl

theorem cell23_5841460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_5841460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841460 prefixEnd_5841460 := by exact prefixLift 5841460
  have htrace : WordTrace (prefixWord ++ tailWord_5841460) baseStart_5841460 baseEnd_5841460 := by
    simpa [prefixWord, tailWord_5841460, baseEnd_5841460] using wordTrace_append hprefix tailTrace_5841460
  have hstable : (prefixWord ++ tailWord_5841460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841460).length < 2 ^ (prefixWord ++ tailWord_5841460).sum := by decide
  have hdescent : baseEnd_5841460 < baseStart_5841460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841463 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 1, 2, 2]
def baseStart_5841463 : Nat := 118140960795 + 5841463 * 2 ^ 59
def prefixEnd_5841463 : Nat := 4983230072969 + 3 ^ 40 * 5841463 * 2
def baseEnd_5841463 : Nat := 2999478244454783982848107

theorem tailTrace_5841463 : CollatzResearch.WordTrace tailWord_5841463 prefixEnd_5841463 2999478244454783982848107 := by
  unfold tailWord_5841463
  simp only [CollatzResearch.WordTrace]
  refine ⟨213055658836384668299137043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142037105890923112199424695 213055658836384668299137043)
  ·
    refine ⟨319583488254577002448705565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213055658836384668299137043 319583488254577002448705565)
    ·
      refine ⟨119843808095466375918264587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319583488254577002448705565 119843808095466375918264587)
      ·
        refine ⟨179765712143199563877396881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119843808095466375918264587 179765712143199563877396881)
        ·
          refine ⟨134824284107399672908047661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179765712143199563877396881 134824284107399672908047661)
          ·
            refine ⟨50559106540274877340517873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134824284107399672908047661 50559106540274877340517873)
            ·
              refine ⟨37919329905206158005388405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50559106540274877340517873 37919329905206158005388405)
              ·
                refine ⟨3554937178613077313005163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37919329905206158005388405 3554937178613077313005163)
                ·
                  refine ⟨5332405767919615969507745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554937178613077313005163 5332405767919615969507745)
                  ·
                    refine ⟨3999304325939711977130809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332405767919615969507745 3999304325939711977130809)
                    ·
                      refine ⟨2999478244454783982848107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999304325939711977130809 2999478244454783982848107)
                      ·
                        rfl

theorem cell23_5841463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_5841463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841463 prefixEnd_5841463 := by exact prefixLift 5841463
  have htrace : WordTrace (prefixWord ++ tailWord_5841463) baseStart_5841463 baseEnd_5841463 := by
    simpa [prefixWord, tailWord_5841463, baseEnd_5841463] using wordTrace_append hprefix tailTrace_5841463
  have hstable : (prefixWord ++ tailWord_5841463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841463).length < 2 ^ (prefixWord ++ tailWord_5841463).sum := by decide
  have hdescent : baseEnd_5841463 < baseStart_5841463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841482 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_5841482 : Nat := 118140960795 + 5841482 * 2 ^ 59
def prefixEnd_5841482 : Nat := 4983230072969 + 3 ^ 40 * 5841482 * 2
def baseEnd_5841482 : Nat := 999829333529073136170173

theorem tailTrace_5841482 : CollatzResearch.WordTrace tailWord_5841482 prefixEnd_5841482 999829333529073136170173 := by
  unfold tailWord_5841482
  simp only [CollatzResearch.WordTrace]
  refine ⟨53264087955828958636019675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142037567882210556362719133 53264087955828958636019675)
  ·
    refine ⟨79896131933743437954029513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53264087955828958636019675 79896131933743437954029513)
    ·
      refine ⟨59922098950307578465522135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79896131933743437954029513 59922098950307578465522135)
      ·
        refine ⟨89883148425461367698283203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59922098950307578465522135 89883148425461367698283203)
        ·
          refine ⟨134824722638192051547424805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89883148425461367698283203 134824722638192051547424805)
          ·
            refine ⟨25279635494661009665142151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134824722638192051547424805 25279635494661009665142151)
            ·
              refine ⟨37919453241991514497713227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25279635494661009665142151 37919453241991514497713227)
              ·
                refine ⟨56879179862987271746569841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37919453241991514497713227 56879179862987271746569841)
                ·
                  refine ⟨42659384897240453809927381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56879179862987271746569841 42659384897240453809927381)
                  ·
                    refine ⟨999829333529073136170173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42659384897240453809927381 999829333529073136170173)
                    ·
                      rfl

theorem cell23_5841482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_5841482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841482 prefixEnd_5841482 := by exact prefixLift 5841482
  have htrace : WordTrace (prefixWord ++ tailWord_5841482) baseStart_5841482 baseEnd_5841482 := by
    simpa [prefixWord, tailWord_5841482, baseEnd_5841482] using wordTrace_append hprefix tailTrace_5841482
  have hstable : (prefixWord ++ tailWord_5841482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841482).length < 2 ^ (prefixWord ++ tailWord_5841482).sum := by decide
  have hdescent : baseEnd_5841482 < baseStart_5841482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841496 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_5841496 : Nat := 118140960795 + 5841496 * 2 ^ 59
def prefixEnd_5841496 : Nat := 4983230072969 + 3 ^ 40 * 5841496 * 2
def baseEnd_5841496 : Nat := 2999495189316382353735455

theorem tailTrace_5841496 : CollatzResearch.WordTrace tailWord_5841496 prefixEnd_5841496 2999495189316382353735455 := by
  unfold tailWord_5841496
  simp only [CollatzResearch.WordTrace]
  refine ⟨106528431222632557467544171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142037908296843409956725561 106528431222632557467544171)
  ·
    refine ⟨159792646833948836201316257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106528431222632557467544171 159792646833948836201316257)
    ·
      refine ⟨119844485125461627150987193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159792646833948836201316257 119844485125461627150987193)
      ·
        refine ⟨89883363844096220363240395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119844485125461627150987193 89883363844096220363240395)
        ·
          refine ⟨134825045766144330544860593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89883363844096220363240395 134825045766144330544860593)
          ·
            refine ⟨101118784324608247908645445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134825045766144330544860593 101118784324608247908645445)
            ·
              refine ⟨18959772060864046482871021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101118784324608247908645445 18959772060864046482871021)
              ·
                refine ⟨7109914522824017431076633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18959772060864046482871021 7109914522824017431076633)
                ·
                  refine ⟨5332435892118013073307475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109914522824017431076633 5332435892118013073307475)
                  ·
                    refine ⟨7998653838177019609961213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5332435892118013073307475 7998653838177019609961213)
                    ·
                      refine ⟨2999495189316382353735455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7998653838177019609961213 2999495189316382353735455)
                      ·
                        rfl

theorem cell23_5841496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_5841496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841496 prefixEnd_5841496 := by exact prefixLift 5841496
  have htrace : WordTrace (prefixWord ++ tailWord_5841496) baseStart_5841496 baseEnd_5841496 := by
    simpa [prefixWord, tailWord_5841496, baseEnd_5841496] using wordTrace_append hprefix tailTrace_5841496
  have hstable : (prefixWord ++ tailWord_5841496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841496).length < 2 ^ (prefixWord ++ tailWord_5841496).sum := by decide
  have hdescent : baseEnd_5841496 < baseStart_5841496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841592 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_5841592 : Nat := 118140960795 + 5841592 * 2 ^ 59
def prefixEnd_5841592 : Nat := 4983230072969 + 3 ^ 40 * 5841592 * 2
def baseEnd_5841592 : Nat := 2999544483459213978135013

theorem tailTrace_5841592 : CollatzResearch.WordTrace tailWord_5841592 prefixEnd_5841592 2999544483459213978135013 := by
  unfold tailWord_5841592
  simp only [CollatzResearch.WordTrace]
  refine ⟨106530181926458661665291515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142040242568611548887055353 106530181926458661665291515)
  ·
    refine ⟨159795272889687992497937273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106530181926458661665291515 159795272889687992497937273)
    ·
      refine ⟨119846454667265994373452955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159795272889687992497937273 119846454667265994373452955)
      ·
        refine ⟨179769682000898991560179433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119846454667265994373452955 179769682000898991560179433)
        ·
          refine ⟨134827261500674243670134575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179769682000898991560179433 134827261500674243670134575)
          ·
            refine ⟨202240892251011365505201863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134827261500674243670134575 202240892251011365505201863)
            ·
              refine ⟨303361338376517048257802795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202240892251011365505201863 303361338376517048257802795)
              ·
                refine ⟨455042007564775572386704193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303361338376517048257802795 455042007564775572386704193)
                ·
                  refine ⟨341281505673581679290028145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455042007564775572386704193 341281505673581679290028145)
                  ·
                    refine ⟨255961129255186259467521109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341281505673581679290028145 255961129255186259467521109)
                    ·
                      refine ⟨2999544483459213978135013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255961129255186259467521109 2999544483459213978135013)
                      ·
                        rfl

theorem cell23_5841592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_5841592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841592 prefixEnd_5841592 := by exact prefixLift 5841592
  have htrace : WordTrace (prefixWord ++ tailWord_5841592) baseStart_5841592 baseEnd_5841592 := by
    simpa [prefixWord, tailWord_5841592, baseEnd_5841592] using wordTrace_append hprefix tailTrace_5841592
  have hstable : (prefixWord ++ tailWord_5841592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841592).length < 2 ^ (prefixWord ++ tailWord_5841592).sum := by decide
  have hdescent : baseEnd_5841592 < baseStart_5841592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841596 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5841596 : Nat := 118140960795 + 5841596 * 2 ^ 59
def prefixEnd_5841596 : Nat := 4983230072969 + 3 ^ 40 * 5841596 * 2
def baseEnd_5841596 : Nat := 2999546537381831962484995

theorem tailTrace_5841596 : CollatzResearch.WordTrace tailWord_5841596 prefixEnd_5841596 2999546537381831962484995 := by
  unfold tailWord_5841596
  simp only [CollatzResearch.WordTrace]
  refine ⟨106530254872451416006864321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142040339829935221342485761 106530254872451416006864321)
  ·
    refine ⟨79897691154338562005148241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106530254872451416006864321 79897691154338562005148241)
    ·
      refine ⟨59923268365753921503861181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79897691154338562005148241 59923268365753921503861181)
      ·
        refine ⟨22471225637157720563947943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59923268365753921503861181 22471225637157720563947943)
        ·
          refine ⟨33706838455736580845921915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471225637157720563947943 33706838455736580845921915)
          ·
            refine ⟨50560257683604871268882873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33706838455736580845921915 50560257683604871268882873)
            ·
              refine ⟨37920193262703653451662155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50560257683604871268882873 37920193262703653451662155)
              ·
                refine ⟨56880289894055480177493233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37920193262703653451662155 56880289894055480177493233)
                ·
                  refine ⟨42660217420541610133119925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56880289894055480177493233 42660217420541610133119925)
                  ·
                    refine ⟨3999395383175775949979993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42660217420541610133119925 3999395383175775949979993)
                    ·
                      refine ⟨2999546537381831962484995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999395383175775949979993 2999546537381831962484995)
                      ·
                        rfl

theorem cell23_5841596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5841596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841596 prefixEnd_5841596 := by exact prefixLift 5841596
  have htrace : WordTrace (prefixWord ++ tailWord_5841596) baseStart_5841596 baseEnd_5841596 := by
    simpa [prefixWord, tailWord_5841596, baseEnd_5841596] using wordTrace_append hprefix tailTrace_5841596
  have hstable : (prefixWord ++ tailWord_5841596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841596).length < 2 ^ (prefixWord ++ tailWord_5841596).sum := by decide
  have hdescent : baseEnd_5841596 < baseStart_5841596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841599 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_5841599 : Nat := 118140960795 + 5841599 * 2 ^ 59
def prefixEnd_5841599 : Nat := 4983230072969 + 3 ^ 40 * 5841599 * 2
def baseEnd_5841599 : Nat := 2999548077823795450747481

theorem tailTrace_5841599 : CollatzResearch.WordTrace tailWord_5841599 prefixEnd_5841599 2999548077823795450747481 := by
  unfold tailWord_5841599
  simp only [CollatzResearch.WordTrace]
  refine ⟨213060619163891963526087851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142040412775927975684058567 213060619163891963526087851)
  ·
    refine ⟨319590928745837945289131777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213060619163891963526087851 319590928745837945289131777)
    ·
      refine ⟨239693196559378458966848833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319590928745837945289131777 239693196559378458966848833)
      ·
        refine ⟨179769897419533844225136625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239693196559378458966848833 179769897419533844225136625)
        ·
          refine ⟨134827423064650383168852469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179769897419533844225136625 134827423064650383168852469)
          ·
            refine ⟨12640070912310973422079919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134827423064650383168852469 12640070912310973422079919)
            ·
              refine ⟨18960106368466460133119879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12640070912310973422079919 18960106368466460133119879)
              ·
                refine ⟨28440159552699690199679819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18960106368466460133119879 28440159552699690199679819)
                ·
                  refine ⟨42660239329049535299519729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28440159552699690199679819 42660239329049535299519729)
                  ·
                    refine ⟨31995179496787151474639797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42660239329049535299519729 31995179496787151474639797)
                    ·
                      refine ⟨2999548077823795450747481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31995179496787151474639797 2999548077823795450747481)
                      ·
                        rfl

theorem cell23_5841599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_5841599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841599 prefixEnd_5841599 := by exact prefixLift 5841599
  have htrace : WordTrace (prefixWord ++ tailWord_5841599) baseStart_5841599 baseEnd_5841599 := by
    simpa [prefixWord, tailWord_5841599, baseEnd_5841599] using wordTrace_append hprefix tailTrace_5841599
  have hstable : (prefixWord ++ tailWord_5841599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841599).length < 2 ^ (prefixWord ++ tailWord_5841599).sum := by decide
  have hdescent : baseEnd_5841599 < baseStart_5841599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841626 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_5841626 : Nat := 118140960795 + 5841626 * 2 ^ 59
def prefixEnd_5841626 : Nat := 4983230072969 + 3 ^ 40 * 5841626 * 2
def baseEnd_5841626 : Nat := 2999561941801466845109857

theorem tailTrace_5841626 : CollatzResearch.WordTrace tailWord_5841626 prefixEnd_5841626 2999561941801466845109857 := by
  unfold tailWord_5841626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53265400983698536784330183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142041069289862764758213821 53265400983698536784330183)
  ·
    refine ⟨79898101475547805176495275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53265400983698536784330183 79898101475547805176495275)
    ·
      refine ⟨119847152213321707764742913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79898101475547805176495275 119847152213321707764742913)
      ·
        refine ⟨89885364159991280823557185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119847152213321707764742913 89885364159991280823557185)
        ·
          refine ⟨67414023119993460617667889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89885364159991280823557185 67414023119993460617667889)
          ·
            refine ⟨50560517339995095463250917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67414023119993460617667889 50560517339995095463250917)
            ·
              refine ⟨9480097001249080399359547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50560517339995095463250917 9480097001249080399359547)
              ·
                refine ⟨14220145501873620599039321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9480097001249080399359547 14220145501873620599039321)
                ·
                  refine ⟨10665109126405215449279491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14220145501873620599039321 10665109126405215449279491)
                  ·
                    refine ⟨15997663689607823173919237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10665109126405215449279491 15997663689607823173919237)
                    ·
                      refine ⟨2999561941801466845109857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15997663689607823173919237 2999561941801466845109857)
                      ·
                        rfl

theorem cell23_5841626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_5841626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841626 prefixEnd_5841626 := by exact prefixLift 5841626
  have htrace : WordTrace (prefixWord ++ tailWord_5841626) baseStart_5841626 baseEnd_5841626 := by
    simpa [prefixWord, tailWord_5841626, baseEnd_5841626] using wordTrace_append hprefix tailTrace_5841626
  have hstable : (prefixWord ++ tailWord_5841626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841626).length < 2 ^ (prefixWord ++ tailWord_5841626).sum := by decide
  have hdescent : baseEnd_5841626 < baseStart_5841626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841679 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 3, 5]
def baseStart_5841679 : Nat := 118140960795 + 5841679 * 2 ^ 59
def prefixEnd_5841679 : Nat := 4983230072969 + 3 ^ 40 * 5841679 * 2
def baseEnd_5841679 : Nat := 999863052092051712582371

theorem tailTrace_5841679 : CollatzResearch.WordTrace tailWord_5841679 prefixEnd_5841679 999863052092051712582371 := by
  unfold tailWord_5841679
  simp only [CollatzResearch.WordTrace]
  refine ⟨213063537003602137189000091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142042358002401424792666727 213063537003602137189000091)
  ·
    refine ⟨319595305505403205783500137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213063537003602137189000091 319595305505403205783500137)
    ·
      refine ⟨239696479129052404337625103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319595305505403205783500137 239696479129052404337625103)
      ·
        refine ⟨359544718693578606506437655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239696479129052404337625103 359544718693578606506437655)
        ·
          refine ⟨539317078040367909759656483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359544718693578606506437655 539317078040367909759656483)
          ·
            refine ⟨808975617060551864639484725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539317078040367909759656483 808975617060551864639484725)
            ·
              refine ⟨75841464099426737309951693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 808975617060551864639484725 75841464099426737309951693)
              ·
                refine ⟨28440549037285026491231885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75841464099426737309951693 28440549037285026491231885)
                ·
                  refine ⟨10665205888981884934211957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28440549037285026491231885 10665205888981884934211957)
                  ·
                    refine ⟨999863052092051712582371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10665205888981884934211957 999863052092051712582371)
                    ·
                      rfl

theorem cell23_5841679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_5841679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841679 prefixEnd_5841679 := by exact prefixLift 5841679
  have htrace : WordTrace (prefixWord ++ tailWord_5841679) baseStart_5841679 baseEnd_5841679 := by
    simpa [prefixWord, tailWord_5841679, baseEnd_5841679] using wordTrace_append hprefix tailTrace_5841679
  have hstable : (prefixWord ++ tailWord_5841679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841679).length < 2 ^ (prefixWord ++ tailWord_5841679).sum := by decide
  have hdescent : baseEnd_5841679 < baseStart_5841679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841700 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 6]
def baseStart_5841700 : Nat := 118140960795 + 5841700 * 2 ^ 59
def prefixEnd_5841700 : Nat := 4983230072969 + 3 ^ 40 * 5841700 * 2
def baseEnd_5841700 : Nat := 333288882152211061731613

theorem tailTrace_5841700 : CollatzResearch.WordTrace tailWord_5841700 prefixEnd_5841700 333288882152211061731613 := by
  unfold tailWord_5841700
  simp only [CollatzResearch.WordTrace]
  refine ⟨106532151468263028887757277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142042868624350705183676369 106532151468263028887757277)
  ·
    refine ⟨39949556800598635832908979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106532151468263028887757277 39949556800598635832908979)
    ·
      refine ⟨59924335200897953749363469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39949556800598635832908979 59924335200897953749363469)
      ·
        refine ⟨22471625700336732656011301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59924335200897953749363469 22471625700336732656011301)
        ·
          refine ⟨4213429818813137373002119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22471625700336732656011301 4213429818813137373002119)
          ·
            refine ⟨6320144728219706059503179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213429818813137373002119 6320144728219706059503179)
            ·
              refine ⟨9480217092329559089254769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320144728219706059503179 9480217092329559089254769)
              ·
                refine ⟨7110162819247169316941077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9480217092329559089254769 7110162819247169316941077)
                ·
                  refine ⟨333288882152211061731613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7110162819247169316941077 333288882152211061731613)
                  ·
                    rfl

theorem cell23_5841700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_5841700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841700 prefixEnd_5841700 := by exact prefixLift 5841700
  have htrace : WordTrace (prefixWord ++ tailWord_5841700) baseStart_5841700 baseEnd_5841700 := by
    simpa [prefixWord, tailWord_5841700, baseEnd_5841700] using wordTrace_append hprefix tailTrace_5841700
  have hstable : (prefixWord ++ tailWord_5841700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841700).length < 2 ^ (prefixWord ++ tailWord_5841700).sum := by decide
  have hdescent : baseEnd_5841700 < baseStart_5841700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841710 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5841710 : Nat := 118140960795 + 5841710 * 2 ^ 59
def prefixEnd_5841710 : Nat := 4983230072969 + 3 ^ 40 * 5841710 * 2
def baseEnd_5841710 : Nat := 2999605074176444516459471

theorem tailTrace_5841710 : CollatzResearch.WordTrace tailWord_5841710 prefixEnd_5841710 2999605074176444516459471 := by
  unfold tailWord_5841710
  simp only [CollatzResearch.WordTrace]
  refine ⟨26633083458311228685422323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142043111777659886322252389 26633083458311228685422323)
  ·
    refine ⟨39949625187466843028133485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26633083458311228685422323 39949625187466843028133485)
    ·
      refine ⟨14981109445300066135550057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39949625187466843028133485 14981109445300066135550057)
      ·
        refine ⟨11235832083975049601662543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14981109445300066135550057 11235832083975049601662543)
        ·
          refine ⟨16853748125962574402493815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11235832083975049601662543 16853748125962574402493815)
          ·
            refine ⟨25280622188943861603740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16853748125962574402493815 25280622188943861603740723)
            ·
              refine ⟨37920933283415792405611085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25280622188943861603740723 37920933283415792405611085)
              ·
                refine ⟨14220349981280922152104157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37920933283415792405611085 14220349981280922152104157)
                ·
                  refine ⟨5332631242980345807039059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14220349981280922152104157 5332631242980345807039059)
                  ·
                    refine ⟨7998946864470518710558589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5332631242980345807039059 7998946864470518710558589)
                    ·
                      refine ⟨2999605074176444516459471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7998946864470518710558589 2999605074176444516459471)
                      ·
                        rfl

theorem cell23_5841710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5841710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841710 prefixEnd_5841710 := by exact prefixLift 5841710
  have htrace : WordTrace (prefixWord ++ tailWord_5841710) baseStart_5841710 baseEnd_5841710 := by
    simpa [prefixWord, tailWord_5841710, baseEnd_5841710] using wordTrace_append hprefix tailTrace_5841710
  have hstable : (prefixWord ++ tailWord_5841710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841710).length < 2 ^ (prefixWord ++ tailWord_5841710).sum := by decide
  have hdescent : baseEnd_5841710 < baseStart_5841710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841733 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_5841733 : Nat := 118140960795 + 5841733 * 2 ^ 59
def prefixEnd_5841733 : Nat := 4983230072969 + 3 ^ 40 * 5841733 * 2
def baseEnd_5841733 : Nat := 2999616884231497926471865

theorem tailTrace_5841733 : CollatzResearch.WordTrace tailWord_5841733 prefixEnd_5841733 2999616884231497926471865 := by
  unfold tailWord_5841733
  simp only [CollatzResearch.WordTrace]
  refine ⟨213065506545406504411465853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142043671030271002940977235 213065506545406504411465853)
  ·
    refine ⟨79899564954527439154299695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213065506545406504411465853 79899564954527439154299695)
    ·
      refine ⟨119849347431791158731449543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79899564954527439154299695 119849347431791158731449543)
      ·
        refine ⟨179774021147686738097174315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119849347431791158731449543 179774021147686738097174315)
        ·
          refine ⟨269661031721530107145761473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179774021147686738097174315 269661031721530107145761473)
          ·
            refine ⟨202245773791147580359321105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269661031721530107145761473 202245773791147580359321105)
            ·
              refine ⟨151684330343360685269490829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202245773791147580359321105 151684330343360685269490829)
              ·
                refine ⟨56881623878760256976059061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151684330343360685269490829 56881623878760256976059061)
                ·
                  refine ⟨5332652238633774091505537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56881623878760256976059061 5332652238633774091505537)
                  ·
                    refine ⟨3999489178975330568629153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332652238633774091505537 3999489178975330568629153)
                    ·
                      refine ⟨2999616884231497926471865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999489178975330568629153 2999616884231497926471865)
                      ·
                        rfl

theorem cell23_5841733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_5841733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841733 prefixEnd_5841733 := by exact prefixLift 5841733
  have htrace : WordTrace (prefixWord ++ tailWord_5841733) baseStart_5841733 baseEnd_5841733 := by
    simpa [prefixWord, tailWord_5841733, baseEnd_5841733] using wordTrace_append hprefix tailTrace_5841733
  have hstable : (prefixWord ++ tailWord_5841733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841733).length < 2 ^ (prefixWord ++ tailWord_5841733).sum := by decide
  have hdescent : baseEnd_5841733 < baseStart_5841733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841746 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5841746 : Nat := 118140960795 + 5841746 * 2 ^ 59
def prefixEnd_5841746 : Nat := 4983230072969 + 3 ^ 40 * 5841746 * 2
def baseEnd_5841746 : Nat := 2999623559480006375609305

theorem tailTrace_5841746 : CollatzResearch.WordTrace tailWord_5841746 prefixEnd_5841746 2999623559480006375609305 := by
  unfold tailWord_5841746
  simp only [CollatzResearch.WordTrace]
  refine ⟨53266495173589851907922273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142043987129572938421126061 53266495173589851907922273)
  ·
    refine ⟨39949871380192388930941705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53266495173589851907922273 39949871380192388930941705)
    ·
      refine ⟨29962403535144291698206279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39949871380192388930941705 29962403535144291698206279)
      ·
        refine ⟨44943605302716437547309419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29962403535144291698206279 44943605302716437547309419)
        ·
          refine ⟨67415407954074656320964129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44943605302716437547309419 67415407954074656320964129)
          ·
            refine ⟨50561555965555992240723097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67415407954074656320964129 50561555965555992240723097)
            ·
              refine ⟨37921166974166994180542323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50561555965555992240723097 37921166974166994180542323)
              ·
                refine ⟨56881750461250491270813485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37921166974166994180542323 56881750461250491270813485)
                ·
                  refine ⟨21330656422968934226555057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56881750461250491270813485 21330656422968934226555057)
                  ·
                    refine ⟨15997992317226700669916293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21330656422968934226555057 15997992317226700669916293)
                    ·
                      refine ⟨2999623559480006375609305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15997992317226700669916293 2999623559480006375609305)
                      ·
                        rfl

theorem cell23_5841746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5841746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841746 prefixEnd_5841746 := by exact prefixLift 5841746
  have htrace : WordTrace (prefixWord ++ tailWord_5841746) baseStart_5841746 baseEnd_5841746 := by
    simpa [prefixWord, tailWord_5841746, baseEnd_5841746] using wordTrace_append hprefix tailTrace_5841746
  have hstable : (prefixWord ++ tailWord_5841746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841746).length < 2 ^ (prefixWord ++ tailWord_5841746).sum := by decide
  have hdescent : baseEnd_5841746 < baseStart_5841746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841753 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_5841753 : Nat := 118140960795 + 5841753 * 2 ^ 59
def prefixEnd_5841753 : Nat := 4983230072969 + 3 ^ 40 * 5841753 * 2
def baseEnd_5841753 : Nat := 2999627153844587848221773

theorem tailTrace_5841753 : CollatzResearch.WordTrace tailWord_5841753 prefixEnd_5841753 2999627153844587848221773 := by
  unfold tailWord_5841753
  simp only [CollatzResearch.WordTrace]
  refine ⟨213066236005334047827193913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142044157336889365218129275 213066236005334047827193913)
  ·
    refine ⟨159799677004000535870395435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213066236005334047827193913 159799677004000535870395435)
    ·
      refine ⟨239699515506000803805593153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159799677004000535870395435 239699515506000803805593153)
      ·
        refine ⟨179774636629500602854194865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239699515506000803805593153 179774636629500602854194865)
        ·
          refine ⟨134830977472125452140646149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179774636629500602854194865 134830977472125452140646149)
          ·
            refine ⟨25280808276023522276371153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134830977472125452140646149 25280808276023522276371153)
            ·
              refine ⟨18960606207017641707278365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25280808276023522276371153 18960606207017641707278365)
              ·
                refine ⟨7110227327631615640229387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18960606207017641707278365 7110227327631615640229387)
                ·
                  refine ⟨10665340991447423460344081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110227327631615640229387 10665340991447423460344081)
                  ·
                    refine ⟨7999005743585567595258061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10665340991447423460344081 7999005743585567595258061)
                    ·
                      refine ⟨2999627153844587848221773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999005743585567595258061 2999627153844587848221773)
                      ·
                        rfl

theorem cell23_5841753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_5841753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841753 prefixEnd_5841753 := by exact prefixLift 5841753
  have htrace : WordTrace (prefixWord ++ tailWord_5841753) baseStart_5841753 baseEnd_5841753 := by
    simpa [prefixWord, tailWord_5841753, baseEnd_5841753] using wordTrace_append hprefix tailTrace_5841753
  have hstable : (prefixWord ++ tailWord_5841753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841753).length < 2 ^ (prefixWord ++ tailWord_5841753).sum := by decide
  have hdescent : baseEnd_5841753 < baseStart_5841753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841756 : List Nat := [2, 2, 4, 2, 1, 1, 11]
def baseStart_5841756 : Nat := 118140960795 + 5841756 * 2 ^ 59
def prefixEnd_5841756 : Nat := 4983230072969 + 3 ^ 40 * 5841756 * 2
def baseEnd_5841756 : Nat := 37032453015883349833139

theorem tailTrace_5841756 : CollatzResearch.WordTrace tailWord_5841756 prefixEnd_5841756 37032453015883349833139 := by
  unfold tailWord_5841756
  simp only [CollatzResearch.WordTrace]
  refine ⟨106533172712161589669776561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142044230282882119559702081 106533172712161589669776561)
  ·
    refine ⟨79899879534121192252332421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106533172712161589669776561 79899879534121192252332421)
    ·
      refine ⟨14981227412647723547312329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79899879534121192252332421 14981227412647723547312329)
      ·
        refine ⟨11235920559485792660484247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14981227412647723547312329 11235920559485792660484247)
        ·
          refine ⟨16853880839228688990726371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11235920559485792660484247 16853880839228688990726371)
          ·
            refine ⟨25280821258843033486089557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16853880839228688990726371 25280821258843033486089557)
            ·
              refine ⟨37032453015883349833139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25280821258843033486089557 37032453015883349833139)
              ·
                rfl

theorem cell23_5841756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 11].length) (baseStart_5841756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841756 prefixEnd_5841756 := by exact prefixLift 5841756
  have htrace : WordTrace (prefixWord ++ tailWord_5841756) baseStart_5841756 baseEnd_5841756 := by
    simpa [prefixWord, tailWord_5841756, baseEnd_5841756] using wordTrace_append hprefix tailTrace_5841756
  have hstable : (prefixWord ++ tailWord_5841756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841756).length < 2 ^ (prefixWord ++ tailWord_5841756).sum := by decide
  have hdescent : baseEnd_5841756 < baseStart_5841756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841767 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_5841767 : Nat := 118140960795 + 5841767 * 2 ^ 59
def prefixEnd_5841767 : Nat := 4983230072969 + 3 ^ 40 * 5841767 * 2
def baseEnd_5841767 : Nat := 2999634342573750793446709

theorem tailTrace_5841767 : CollatzResearch.WordTrace tailWord_5841767 prefixEnd_5841767 2999634342573750793446709 := by
  unfold tailWord_5841767
  simp only [CollatzResearch.WordTrace]
  refine ⟨213066746627283328218203555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142044497751522218812135703 213066746627283328218203555)
  ·
    refine ⟨319600119940924992327305333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213066746627283328218203555 319600119940924992327305333)
    ·
      refine ⟨29962511244461718030684875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 319600119940924992327305333 29962511244461718030684875)
      ·
        refine ⟨44943766866692577046027313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29962511244461718030684875 44943766866692577046027313)
        ·
          refine ⟨33707825150019432784520485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44943766866692577046027313 33707825150019432784520485)
          ·
            refine ⟨6320217215628643647097591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33707825150019432784520485 6320217215628643647097591)
            ·
              refine ⟨9480325823442965470646387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320217215628643647097591 9480325823442965470646387)
              ·
                refine ⟨14220488735164448205969581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9480325823442965470646387 14220488735164448205969581)
                ·
                  refine ⟨5332683275686668077238593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14220488735164448205969581 5332683275686668077238593)
                  ·
                    refine ⟨3999512456765001057928945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332683275686668077238593 3999512456765001057928945)
                    ·
                      refine ⟨2999634342573750793446709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999512456765001057928945 2999634342573750793446709)
                      ·
                        rfl

theorem cell23_5841767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_5841767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841767 prefixEnd_5841767 := by exact prefixLift 5841767
  have htrace : WordTrace (prefixWord ++ tailWord_5841767) baseStart_5841767 baseEnd_5841767 := by
    simpa [prefixWord, tailWord_5841767, baseEnd_5841767] using wordTrace_append hprefix tailTrace_5841767
  have hstable : (prefixWord ++ tailWord_5841767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841767).length < 2 ^ (prefixWord ++ tailWord_5841767).sum := by decide
  have hdescent : baseEnd_5841767 < baseStart_5841767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841818 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5841818 : Nat := 118140960795 + 5841818 * 2 ^ 59
def prefixEnd_5841818 : Nat := 4983230072969 + 3 ^ 40 * 5841818 * 2
def baseEnd_5841818 : Nat := 2999660530087130093908975

theorem tailTrace_5841818 : CollatzResearch.WordTrace tailWord_5841818 prefixEnd_5841818 2999660530087130093908975 := by
  unfold tailWord_5841818
  simp only [CollatzResearch.WordTrace]
  refine ⟨53267151687524640982077527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142045737833399042618873405 53267151687524640982077527)
  ·
    refine ⟨79900727531286961473116291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53267151687524640982077527 79900727531286961473116291)
    ·
      refine ⟨119851091296930442209674437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79900727531286961473116291 119851091296930442209674437)
      ·
        refine ⟨22472079618174457914313957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119851091296930442209674437 22472079618174457914313957)
        ·
          refine ⟨4213514928407710858933867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22472079618174457914313957 4213514928407710858933867)
          ·
            refine ⟨6320272392611566288400801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213514928407710858933867 6320272392611566288400801)
            ·
              refine ⟨4740204294458674716300601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320272392611566288400801 4740204294458674716300601)
              ·
                refine ⟨3555153220844006037225451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740204294458674716300601 3555153220844006037225451)
                ·
                  refine ⟨5332729831266009055838177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555153220844006037225451 5332729831266009055838177)
                  ·
                    refine ⟨3999547373449506791878633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332729831266009055838177 3999547373449506791878633)
                    ·
                      refine ⟨2999660530087130093908975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999547373449506791878633 2999660530087130093908975)
                      ·
                        rfl

theorem cell23_5841818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5841818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841818 prefixEnd_5841818 := by exact prefixLift 5841818
  have htrace : WordTrace (prefixWord ++ tailWord_5841818) baseStart_5841818 baseEnd_5841818 := by
    simpa [prefixWord, tailWord_5841818, baseEnd_5841818] using wordTrace_append hprefix tailTrace_5841818
  have hstable : (prefixWord ++ tailWord_5841818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841818).length < 2 ^ (prefixWord ++ tailWord_5841818).sum := by decide
  have hdescent : baseEnd_5841818 < baseStart_5841818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841836 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_5841836 : Nat := 118140960795 + 5841836 * 2 ^ 59
def prefixEnd_5841836 : Nat := 4983230072969 + 3 ^ 40 * 5841836 * 2
def baseEnd_5841836 : Nat := 2999669772738911023483891

theorem tailTrace_5841836 : CollatzResearch.WordTrace tailWord_5841836 prefixEnd_5841836 2999669772738911023483891 := by
  unfold tailWord_5841836
  simp only [CollatzResearch.WordTrace]
  refine ⟨106534631632016676501232681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142046175509355568668310241 106534631632016676501232681)
  ·
    refine ⟨79900973724012507375924511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106534631632016676501232681 79900973724012507375924511)
    ·
      refine ⟨119851460586018761063886767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79900973724012507375924511 119851460586018761063886767)
      ·
        refine ⟨179777190879028141595830151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119851460586018761063886767 179777190879028141595830151)
        ·
          refine ⟨269665786318542212393745227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179777190879028141595830151 269665786318542212393745227)
          ·
            refine ⟨404498679477813318590617841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269665786318542212393745227 404498679477813318590617841)
            ·
              refine ⟨303374009608359988942963381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404498679477813318590617841 303374009608359988942963381)
              ·
                refine ⟨28441313400783748963402817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303374009608359988942963381 28441313400783748963402817)
                ·
                  refine ⟨21330985050587811722552113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28441313400783748963402817 21330985050587811722552113)
                  ·
                    refine ⟨15998238787940858791914085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21330985050587811722552113 15998238787940858791914085)
                    ·
                      refine ⟨2999669772738911023483891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15998238787940858791914085 2999669772738911023483891)
                      ·
                        rfl

theorem cell23_5841836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_5841836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841836 prefixEnd_5841836 := by exact prefixLift 5841836
  have htrace : WordTrace (prefixWord ++ tailWord_5841836) baseStart_5841836 baseEnd_5841836 := by
    simpa [prefixWord, tailWord_5841836, baseEnd_5841836] using wordTrace_append hprefix tailTrace_5841836
  have hstable : (prefixWord ++ tailWord_5841836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841836).length < 2 ^ (prefixWord ++ tailWord_5841836).sum := by decide
  have hdescent : baseEnd_5841836 < baseStart_5841836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841863 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 5]
def baseStart_5841863 : Nat := 118140960795 + 5841863 * 2 ^ 59
def prefixEnd_5841863 : Nat := 4983230072969 + 3 ^ 40 * 5841863 * 2
def baseEnd_5841863 : Nat := 333298181857398046427363

theorem tailTrace_5841863 : CollatzResearch.WordTrace tailWord_5841863 prefixEnd_5841863 333298181857398046427363 := by
  unfold tailWord_5841863
  simp only [CollatzResearch.WordTrace]
  refine ⟨213070248034935536613698243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142046832023290357742465495 213070248034935536613698243)
  ·
    refine ⟨319605372052403304920547365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213070248034935536613698243 319605372052403304920547365)
    ·
      refine ⟨59926007259825619672602631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319605372052403304920547365 59926007259825619672602631)
      ·
        refine ⟨89889010889738429508903947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59926007259825619672602631 89889010889738429508903947)
        ·
          refine ⟨134833516334607644263355921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89889010889738429508903947 134833516334607644263355921)
          ·
            refine ⟨101125137250955733197516941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134833516334607644263355921 101125137250955733197516941)
            ·
              refine ⟨37921926469108399949068853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101125137250955733197516941 37921926469108399949068853)
              ·
                refine ⟨3555180606478912495225205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37921926469108399949068853 3555180606478912495225205)
                ·
                  refine ⟨333298181857398046427363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3555180606478912495225205 333298181857398046427363)
                  ·
                    rfl

theorem cell23_5841863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 5].length) (baseStart_5841863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841863 prefixEnd_5841863 := by exact prefixLift 5841863
  have htrace : WordTrace (prefixWord ++ tailWord_5841863) baseStart_5841863 baseEnd_5841863 := by
    simpa [prefixWord, tailWord_5841863, baseEnd_5841863] using wordTrace_append hprefix tailTrace_5841863
  have hstable : (prefixWord ++ tailWord_5841863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841863).length < 2 ^ (prefixWord ++ tailWord_5841863).sum := by decide
  have hdescent : baseEnd_5841863 < baseStart_5841863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841874 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5841874 : Nat := 118140960795 + 5841874 * 2 ^ 59
def prefixEnd_5841874 : Nat := 4983230072969 + 3 ^ 40 * 5841874 * 2
def baseEnd_5841874 : Nat := 2999689285003781874808717

theorem tailTrace_5841874 : CollatzResearch.WordTrace tailWord_5841874 prefixEnd_5841874 2999689285003781874808717 := by
  unfold tailWord_5841874
  simp only [CollatzResearch.WordTrace]
  refine ⟨53267662309473921373087169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142047099491930456994899117 53267662309473921373087169)
  ·
    refine ⟨39950746732105441029815377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53267662309473921373087169 39950746732105441029815377)
    ·
      refine ⟨29963060049079080772361533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39950746732105441029815377 29963060049079080772361533)
      ·
        refine ⟨11236147518404655289635575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29963060049079080772361533 11236147518404655289635575)
        ·
          refine ⟨16854221277606982934453363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236147518404655289635575 16854221277606982934453363)
          ·
            refine ⟨25281331916410474401680045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16854221277606982934453363 25281331916410474401680045)
            ·
              refine ⟨9480499468653927900630017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25281331916410474401680045 9480499468653927900630017)
              ·
                refine ⟨7110374601490445925472513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9480499468653927900630017 7110374601490445925472513)
                ·
                  refine ⟨5332780951117834444104385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7110374601490445925472513 5332780951117834444104385)
                  ·
                    refine ⟨3999585713338375833078289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5332780951117834444104385 3999585713338375833078289)
                    ·
                      refine ⟨2999689285003781874808717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999585713338375833078289 2999689285003781874808717)
                      ·
                        rfl

theorem cell23_5841874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5841874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841874 prefixEnd_5841874 := by exact prefixLift 5841874
  have htrace : WordTrace (prefixWord ++ tailWord_5841874) baseStart_5841874 baseEnd_5841874 := by
    simpa [prefixWord, tailWord_5841874, baseEnd_5841874] using wordTrace_append hprefix tailTrace_5841874
  have hstable : (prefixWord ++ tailWord_5841874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841874).length < 2 ^ (prefixWord ++ tailWord_5841874).sum := by decide
  have hdescent : baseEnd_5841874 < baseStart_5841874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841913 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5841913 : Nat := 118140960795 + 5841913 * 2 ^ 59
def prefixEnd_5841913 : Nat := 4983230072969 + 3 ^ 40 * 5841913 * 2
def baseEnd_5841913 : Nat := 2999709310749307222221037

theorem tailTrace_5841913 : CollatzResearch.WordTrace tailWord_5841913 prefixEnd_5841913 2999709310749307222221037 := by
  unfold tailWord_5841913
  simp only [CollatzResearch.WordTrace]
  refine ⟨213072071684754395153018393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142048047789836263435345595 213072071684754395153018393)
  ·
    refine ⟨159804053763565796364763795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213072071684754395153018393 159804053763565796364763795)
    ·
      refine ⟨239706080645348694547145693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159804053763565796364763795 239706080645348694547145693)
      ·
        refine ⟨89889780242005760455179635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239706080645348694547145693 89889780242005760455179635)
        ·
          refine ⟨134834670363008640682769453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89889780242005760455179635 134834670363008640682769453)
          ·
            refine ⟨50563001386128240256038545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134834670363008640682769453 50563001386128240256038545)
            ·
              refine ⟨37922251039596180192028909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50563001386128240256038545 37922251039596180192028909)
              ·
                refine ⟨14220844139848567572010841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37922251039596180192028909 14220844139848567572010841)
                ·
                  refine ⟨10665633104886425679008131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14220844139848567572010841 10665633104886425679008131)
                  ·
                    refine ⟨15998449657329638518512197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10665633104886425679008131 15998449657329638518512197)
                    ·
                      refine ⟨2999709310749307222221037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15998449657329638518512197 2999709310749307222221037)
                      ·
                        rfl

theorem cell23_5841913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5841913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841913 prefixEnd_5841913 := by exact prefixLift 5841913
  have htrace : WordTrace (prefixWord ++ tailWord_5841913) baseStart_5841913 baseEnd_5841913 := by
    simpa [prefixWord, tailWord_5841913, baseEnd_5841913] using wordTrace_append hprefix tailTrace_5841913
  have hstable : (prefixWord ++ tailWord_5841913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841913).length < 2 ^ (prefixWord ++ tailWord_5841913).sum := by decide
  have hdescent : baseEnd_5841913 < baseStart_5841913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5841930 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5841930 : Nat := 118140960795 + 5841930 * 2 ^ 59
def prefixEnd_5841930 : Nat := 4983230072969 + 3 ^ 40 * 5841930 * 2
def baseEnd_5841930 : Nat := 2999718039920433655708459

theorem tailTrace_5841930 : CollatzResearch.WordTrace tailWord_5841930 prefixEnd_5841930 2999718039920433655708459 := by
  unfold tailWord_5841930
  simp only [CollatzResearch.WordTrace]
  refine ⟨53268172931423201764096811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142048461150461871370924829 53268172931423201764096811)
  ·
    refine ⟨79902259397134802646145217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53268172931423201764096811 79902259397134802646145217)
    ·
      refine ⟨59926694547851101984608913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79902259397134802646145217 59926694547851101984608913)
      ·
        refine ⟨44945020910888326488456685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59926694547851101984608913 44945020910888326488456685)
        ·
          refine ⟨16854382841583122433171257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44945020910888326488456685 16854382841583122433171257)
          ·
            refine ⟨12640787131187341824878443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16854382841583122433171257 12640787131187341824878443)
            ·
              refine ⟨18961180696781012737317665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12640787131187341824878443 18961180696781012737317665)
              ·
                refine ⟨14220885522585759552988249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18961180696781012737317665 14220885522585759552988249)
                ·
                  refine ⟨10665664141939319664741187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14220885522585759552988249 10665664141939319664741187)
                  ·
                    refine ⟨15998496212908979497111781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10665664141939319664741187 15998496212908979497111781)
                    ·
                      refine ⟨2999718039920433655708459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15998496212908979497111781 2999718039920433655708459)
                      ·
                        rfl

theorem cell23_5841930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5841930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5841930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5841930 prefixEnd_5841930 := by exact prefixLift 5841930
  have htrace : WordTrace (prefixWord ++ tailWord_5841930) baseStart_5841930 baseEnd_5841930 := by
    simpa [prefixWord, tailWord_5841930, baseEnd_5841930] using wordTrace_append hprefix tailTrace_5841930
  have hstable : (prefixWord ++ tailWord_5841930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5841930).length < 2 ^ (prefixWord ++ tailWord_5841930).sum := by decide
  have hdescent : baseEnd_5841930 < baseStart_5841930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5841930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842003 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4]
def baseStart_5842003 : Nat := 118140960795 + 5842003 * 2 ^ 59
def prefixEnd_5842003 : Nat := 4983230072969 + 3 ^ 40 * 5842003 * 2
def baseEnd_5842003 : Nat := 2999755524008211870095623

theorem tailTrace_5842003 : CollatzResearch.WordTrace tailWord_5842003 prefixEnd_5842003 2999755524008211870095623 := by
  unfold tailWord_5842003
  simp only [CollatzResearch.WordTrace]
  refine ⟨213075354254428340523794663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142050236169618893682529775 213075354254428340523794663)
  ·
    refine ⟨319613031381642510785691995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213075354254428340523794663 319613031381642510785691995)
    ·
      refine ⟨479419547072463766178537993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319613031381642510785691995 479419547072463766178537993)
      ·
        refine ⟨359564660304347824633903495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479419547072463766178537993 359564660304347824633903495)
        ·
          refine ⟨539346990456521736950855243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359564660304347824633903495 539346990456521736950855243)
          ·
            refine ⟨809020485684782605426282865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539346990456521736950855243 809020485684782605426282865)
            ·
              refine ⟨606765364263586954069712149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809020485684782605426282865 606765364263586954069712149)
              ·
                refine ⟨28442126449855638472017757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 606765364263586954069712149 28442126449855638472017757)
                ·
                  refine ⟨10665797418695864427006659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28442126449855638472017757 10665797418695864427006659)
                  ·
                    refine ⟨15998696128043796640509989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10665797418695864427006659 15998696128043796640509989)
                    ·
                      refine ⟨2999755524008211870095623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15998696128043796640509989 2999755524008211870095623)
                      ·
                        rfl

theorem cell23_5842003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_5842003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842003 prefixEnd_5842003 := by exact prefixLift 5842003
  have htrace : WordTrace (prefixWord ++ tailWord_5842003) baseStart_5842003 baseEnd_5842003 := by
    simpa [prefixWord, tailWord_5842003, baseEnd_5842003] using wordTrace_append hprefix tailTrace_5842003
  have hstable : (prefixWord ++ tailWord_5842003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842003).length < 2 ^ (prefixWord ++ tailWord_5842003).sum := by decide
  have hdescent : baseEnd_5842003 < baseStart_5842003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842020 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_5842020 : Nat := 118140960795 + 5842020 * 2 ^ 59
def prefixEnd_5842020 : Nat := 4983230072969 + 3 ^ 40 * 5842020 * 2
def baseEnd_5842020 : Nat := 2999764253179338303583045

theorem tailTrace_5842020 : CollatzResearch.WordTrace tailWord_5842020 prefixEnd_5842020 2999764253179338303583045 := by
  unfold tailWord_5842020
  simp only [CollatzResearch.WordTrace]
  refine ⟨106537987147683376213581757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142050649530244501618109009 106537987147683376213581757)
  ·
    refine ⟨39951745180381266080093159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106537987147683376213581757 39951745180381266080093159)
    ·
      refine ⟨59927617770571899120139739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39951745180381266080093159 59927617770571899120139739)
      ·
        refine ⟨89891426655857848680209609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59927617770571899120139739 89891426655857848680209609)
        ·
          refine ⟨67418569991893386510157207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89891426655857848680209609 67418569991893386510157207)
          ·
            refine ⟨101127854987840079765235811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67418569991893386510157207 101127854987840079765235811)
            ·
              refine ⟨151691782481760119647853717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101127854987840079765235811 151691782481760119647853717)
              ·
                refine ⟨7110552303832505608493143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151691782481760119647853717 7110552303832505608493143)
                ·
                  refine ⟨10665828455748758412739715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110552303832505608493143 10665828455748758412739715)
                  ·
                    refine ⟨15998742683623137619109573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10665828455748758412739715 15998742683623137619109573)
                    ·
                      refine ⟨2999764253179338303583045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15998742683623137619109573 2999764253179338303583045)
                      ·
                        rfl

theorem cell23_5842020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_5842020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842020 prefixEnd_5842020 := by exact prefixLift 5842020
  have htrace : WordTrace (prefixWord ++ tailWord_5842020) baseStart_5842020 baseEnd_5842020 := by
    simpa [prefixWord, tailWord_5842020, baseEnd_5842020] using wordTrace_append hprefix tailTrace_5842020
  have hstable : (prefixWord ++ tailWord_5842020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842020).length < 2 ^ (prefixWord ++ tailWord_5842020).sum := by decide
  have hdescent : baseEnd_5842020 < baseStart_5842020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842024 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5842024 : Nat := 118140960795 + 5842024 * 2 ^ 59
def prefixEnd_5842024 : Nat := 4983230072969 + 3 ^ 40 * 5842024 * 2
def baseEnd_5842024 : Nat := 2999766307101956287933027

theorem tailTrace_5842024 : CollatzResearch.WordTrace tailWord_5842024 prefixEnd_5842024 2999766307101956287933027 := by
  unfold tailWord_5842024
  simp only [CollatzResearch.WordTrace]
  refine ⟨106538060093676130555154563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142050746791568174073539417 106538060093676130555154563)
  ·
    refine ⟨159807090140514195832731845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106538060093676130555154563 159807090140514195832731845)
    ·
      refine ⟨29963829401346411718637221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159807090140514195832731845 29963829401346411718637221)
      ·
        refine ⟨5618218012752452197244479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29963829401346411718637221 5618218012752452197244479)
        ·
          refine ⟨8427327019128678295866719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618218012752452197244479 8427327019128678295866719)
          ·
            refine ⟨12640990528693017443800079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427327019128678295866719 12640990528693017443800079)
            ·
              refine ⟨18961485793039526165700119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12640990528693017443800079 18961485793039526165700119)
              ·
                refine ⟨28442228689559289248550179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18961485793039526165700119 28442228689559289248550179)
                ·
                  refine ⟨42663343034338933872825269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28442228689559289248550179 42663343034338933872825269)
                  ·
                    refine ⟨3999688409469275050577369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42663343034338933872825269 3999688409469275050577369)
                    ·
                      refine ⟨2999766307101956287933027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999688409469275050577369 2999766307101956287933027)
                      ·
                        rfl

theorem cell23_5842024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5842024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842024 prefixEnd_5842024 := by exact prefixLift 5842024
  have htrace : WordTrace (prefixWord ++ tailWord_5842024) baseStart_5842024 baseEnd_5842024 := by
    simpa [prefixWord, tailWord_5842024, baseEnd_5842024] using wordTrace_append hprefix tailTrace_5842024
  have hstable : (prefixWord ++ tailWord_5842024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842024).length < 2 ^ (prefixWord ++ tailWord_5842024).sum := by decide
  have hdescent : baseEnd_5842024 < baseStart_5842024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842030 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_5842030 : Nat := 118140960795 + 5842030 * 2 ^ 59
def prefixEnd_5842030 : Nat := 4983230072969 + 3 ^ 40 * 5842030 * 2
def baseEnd_5842030 : Nat := 999923129328627754819333

theorem tailTrace_5842030 : CollatzResearch.WordTrace tailWord_5842030 prefixEnd_5842030 999923129328627754819333 := by
  unfold tailWord_5842030
  simp only [CollatzResearch.WordTrace]
  refine ⟨26634542378166315516878443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142050892683553682756685029 26634542378166315516878443)
  ·
    refine ⟨39951813567249473275317665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26634542378166315516878443 39951813567249473275317665)
    ·
      refine ⟨29963860175437104956488249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39951813567249473275317665 29963860175437104956488249)
      ·
        refine ⟨22472895131577828717366187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29963860175437104956488249 22472895131577828717366187)
        ·
          refine ⟨33709342697366743076049281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22472895131577828717366187 33709342697366743076049281)
          ·
            refine ⟨25282007023025057307036961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33709342697366743076049281 25282007023025057307036961)
            ·
              refine ⟨18961505267268792980277721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25282007023025057307036961 18961505267268792980277721)
              ·
                refine ⟨14221128950451594735208291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18961505267268792980277721 14221128950451594735208291)
                ·
                  refine ⟨21331693425677392102812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14221128950451594735208291 21331693425677392102812437)
                  ·
                    refine ⟨999923129328627754819333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21331693425677392102812437 999923129328627754819333)
                    ·
                      rfl

theorem cell23_5842030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_5842030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842030 prefixEnd_5842030 := by exact prefixLift 5842030
  have htrace : WordTrace (prefixWord ++ tailWord_5842030) baseStart_5842030 baseEnd_5842030 := by
    simpa [prefixWord, tailWord_5842030, baseEnd_5842030] using wordTrace_append hprefix tailTrace_5842030
  have hstable : (prefixWord ++ tailWord_5842030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842030).length < 2 ^ (prefixWord ++ tailWord_5842030).sum := by decide
  have hdescent : baseEnd_5842030 < baseStart_5842030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842033 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_5842033 : Nat := 118140960795 + 5842033 * 2 ^ 59
def prefixEnd_5842033 : Nat := 4983230072969 + 3 ^ 40 * 5842033 * 2
def baseEnd_5842033 : Nat := 2999770928427846752720485

theorem tailTrace_5842033 : CollatzResearch.WordTrace tailWord_5842033 prefixEnd_5842033 2999770928427846752720485 := by
  unfold tailWord_5842033
  simp only [CollatzResearch.WordTrace]
  refine ⟨213076448444319655647386753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142050965629546437098257835 213076448444319655647386753)
  ·
    refine ⟨159807336333239741735540065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213076448444319655647386753 159807336333239741735540065)
    ·
      refine ⟨119855502249929806301655049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159807336333239741735540065 119855502249929806301655049)
      ·
        refine ⟨89891626687447354726241287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119855502249929806301655049 89891626687447354726241287)
        ·
          refine ⟨134837440031171032089361931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89891626687447354726241287 134837440031171032089361931)
          ·
            refine ⟨202256160046756548134042897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134837440031171032089361931 202256160046756548134042897)
            ·
              refine ⟨151692120035067411100532173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202256160046756548134042897 151692120035067411100532173)
              ·
                refine ⟨56884545013150279162699565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151692120035067411100532173 56884545013150279162699565)
                ·
                  refine ⟨21331704379931354686012337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56884545013150279162699565 21331704379931354686012337)
                  ·
                    refine ⟨15998778284948516014509253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21331704379931354686012337 15998778284948516014509253)
                    ·
                      refine ⟨2999770928427846752720485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15998778284948516014509253 2999770928427846752720485)
                      ·
                        rfl

theorem cell23_5842033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_5842033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842033 prefixEnd_5842033 := by exact prefixLift 5842033
  have htrace : WordTrace (prefixWord ++ tailWord_5842033) baseStart_5842033 baseEnd_5842033 := by
    simpa [prefixWord, tailWord_5842033, baseEnd_5842033] using wordTrace_append hprefix tailTrace_5842033
  have hstable : (prefixWord ++ tailWord_5842033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842033).length < 2 ^ (prefixWord ++ tailWord_5842033).sum := by decide
  have hdescent : baseEnd_5842033 < baseStart_5842033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842074 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5842074 : Nat := 118140960795 + 5842074 * 2 ^ 59
def prefixEnd_5842074 : Nat := 4983230072969 + 3 ^ 40 * 5842074 * 2
def baseEnd_5842074 : Nat := 2999791981134681092307797

theorem tailTrace_5842074 : CollatzResearch.WordTrace tailWord_5842074 prefixEnd_5842074 2999791981134681092307797 := by
  unfold tailWord_5842074
  simp only [CollatzResearch.WordTrace]
  refine ⟨53269485959292779912407319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142051962558114079766419517 53269485959292779912407319)
  ·
    refine ⟨79904228938939169868610979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53269485959292779912407319 79904228938939169868610979)
    ·
      refine ⟨119856343408408754802916469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79904228938939169868610979 119856343408408754802916469)
      ·
        refine ⟨11236532194538320762773419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119856343408408754802916469 11236532194538320762773419)
        ·
          refine ⟨16854798291807481144160129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236532194538320762773419 16854798291807481144160129)
          ·
            refine ⟨12641098718855610858120097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16854798291807481144160129 12641098718855610858120097)
            ·
              refine ⟨9480824039141708143590073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12641098718855610858120097 9480824039141708143590073)
              ·
                refine ⟨7110618029356281107692555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9480824039141708143590073 7110618029356281107692555)
                ·
                  refine ⟨10665927044034421661538833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110618029356281107692555 10665927044034421661538833)
                  ·
                    refine ⟨7999445283025816246154125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10665927044034421661538833 7999445283025816246154125)
                    ·
                      refine ⟨2999791981134681092307797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999445283025816246154125 2999791981134681092307797)
                      ·
                        rfl

theorem cell23_5842074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5842074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842074 prefixEnd_5842074 := by exact prefixLift 5842074
  have htrace : WordTrace (prefixWord ++ tailWord_5842074) baseStart_5842074 baseEnd_5842074 := by
    simpa [prefixWord, tailWord_5842074, baseEnd_5842074] using wordTrace_append hprefix tailTrace_5842074
  have hstable : (prefixWord ++ tailWord_5842074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842074).length < 2 ^ (prefixWord ++ tailWord_5842074).sum := by decide
  have hdescent : baseEnd_5842074 < baseStart_5842074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842125 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5842125 : Nat := 118140960795 + 5842125 * 2 ^ 59
def prefixEnd_5842125 : Nat := 4983230072969 + 3 ^ 40 * 5842125 * 2
def baseEnd_5842125 : Nat := 2999818168648060392770063

theorem tailTrace_5842125 : CollatzResearch.WordTrace tailWord_5842125 prefixEnd_5842125 2999818168648060392770063 := by
  unfold tailWord_5842125
  simp only [CollatzResearch.WordTrace]
  refine ⟨213079803959986355359735829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142053202639990903573157219 213079803959986355359735829)
  ·
    refine ⟨9988115810624360407487617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 213079803959986355359735829 9988115810624360407487617)
    ·
      refine ⟨7491086857968270305615713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9988115810624360407487617 7491086857968270305615713)
      ·
        refine ⟨5618315143476202729211785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491086857968270305615713 5618315143476202729211785)
        ·
          refine ⟨4213736357607152046908839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618315143476202729211785 4213736357607152046908839)
          ·
            refine ⟨6320604536410728070363259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213736357607152046908839 6320604536410728070363259)
            ·
              refine ⟨9480906804616092105544889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320604536410728070363259 9480906804616092105544889)
              ·
                refine ⟨7110680103462069079158667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9480906804616092105544889 7110680103462069079158667)
                ·
                  refine ⟨10666020155193103618738001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110680103462069079158667 10666020155193103618738001)
                  ·
                    refine ⟨7999515116394827714053501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10666020155193103618738001 7999515116394827714053501)
                    ·
                      refine ⟨2999818168648060392770063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999515116394827714053501 2999818168648060392770063)
                      ·
                        rfl

theorem cell23_5842125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5842125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842125 prefixEnd_5842125 := by exact prefixLift 5842125
  have htrace : WordTrace (prefixWord ++ tailWord_5842125) baseStart_5842125 baseEnd_5842125 := by
    simpa [prefixWord, tailWord_5842125, baseEnd_5842125] using wordTrace_append hprefix tailTrace_5842125
  have hstable : (prefixWord ++ tailWord_5842125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842125).length < 2 ^ (prefixWord ++ tailWord_5842125).sum := by decide
  have hdescent : baseEnd_5842125 < baseStart_5842125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842127 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 6, 2, 2]
def baseStart_5842127 : Nat := 118140960795 + 5842127 * 2 ^ 59
def prefixEnd_5842127 : Nat := 4983230072969 + 3 ^ 40 * 5842127 * 2
def baseEnd_5842127 : Nat := 2999819195609369384945053

theorem tailTrace_5842127 : CollatzResearch.WordTrace tailWord_5842127 prefixEnd_5842127 2999819195609369384945053 := by
  unfold tailWord_5842127
  simp only [CollatzResearch.WordTrace]
  refine ⟨213079876905979109701308635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142053251270652739800872423 213079876905979109701308635)
  ·
    refine ⟨319619815358968664551962953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213079876905979109701308635 319619815358968664551962953)
    ·
      refine ⟨239714861519226498413972215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319619815358968664551962953 239714861519226498413972215)
      ·
        refine ⟨359572292278839747620958323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239714861519226498413972215 359572292278839747620958323)
        ·
          refine ⟨539358438418259621431437485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359572292278839747620958323 539358438418259621431437485)
          ·
            refine ⟨202259414406847358036789057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 539358438418259621431437485 202259414406847358036789057)
            ·
              refine ⟨151694560805135518527591793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202259414406847358036789057 151694560805135518527591793)
              ·
                refine ⟨113770920603851638895693845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151694560805135518527591793 113770920603851638895693845)
                ·
                  refine ⟨5333011903305545573235649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113770920603851638895693845 5333011903305545573235649)
                  ·
                    refine ⟨3999758927479159179926737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333011903305545573235649 3999758927479159179926737)
                    ·
                      refine ⟨2999819195609369384945053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999758927479159179926737 2999819195609369384945053)
                      ·
                        rfl

theorem cell23_5842127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2, 2].length) (baseStart_5842127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842127 prefixEnd_5842127 := by exact prefixLift 5842127
  have htrace : WordTrace (prefixWord ++ tailWord_5842127) baseStart_5842127 baseEnd_5842127 := by
    simpa [prefixWord, tailWord_5842127, baseEnd_5842127] using wordTrace_append hprefix tailTrace_5842127
  have hstable : (prefixWord ++ tailWord_5842127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842127).length < 2 ^ (prefixWord ++ tailWord_5842127).sum := by decide
  have hdescent : baseEnd_5842127 < baseStart_5842127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842130 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5842130 : Nat := 118140960795 + 5842130 * 2 ^ 59
def prefixEnd_5842130 : Nat := 4983230072969 + 3 ^ 40 * 5842130 * 2
def baseEnd_5842130 : Nat := 2999820736051332873207539

theorem tailTrace_5842130 : CollatzResearch.WordTrace tailWord_5842130 prefixEnd_5842130 2999820736051332873207539 := by
  unfold tailWord_5842130
  simp only [CollatzResearch.WordTrace]
  refine ⟨53269996581242060303416961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142053324216645494142445229 53269996581242060303416961)
  ·
    refine ⟨39952497435931545227562721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53269996581242060303416961 39952497435931545227562721)
    ·
      refine ⟨29964373076948658920672041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39952497435931545227562721 29964373076948658920672041)
      ·
        refine ⟨22473279807711494190504031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29964373076948658920672041 22473279807711494190504031)
        ·
          refine ⟨33709919711567241285756047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22473279807711494190504031 33709919711567241285756047)
          ·
            refine ⟨50564879567350861928634071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33709919711567241285756047 50564879567350861928634071)
            ·
              refine ⟨75847319351026292892951107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50564879567350861928634071 75847319351026292892951107)
              ·
                refine ⟨113770979026539439339426661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75847319351026292892951107 113770979026539439339426661)
                ·
                  refine ⟨21332058567476144876142499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113770979026539439339426661 21332058567476144876142499)
                  ·
                    refine ⟨31998087851214217314213749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21332058567476144876142499 31998087851214217314213749)
                    ·
                      refine ⟨2999820736051332873207539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31998087851214217314213749 2999820736051332873207539)
                      ·
                        rfl

theorem cell23_5842130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5842130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842130 prefixEnd_5842130 := by exact prefixLift 5842130
  have htrace : WordTrace (prefixWord ++ tailWord_5842130) baseStart_5842130 baseEnd_5842130 := by
    simpa [prefixWord, tailWord_5842130, baseEnd_5842130] using wordTrace_append hprefix tailTrace_5842130
  have hstable : (prefixWord ++ tailWord_5842130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842130).length < 2 ^ (prefixWord ++ tailWord_5842130).sum := by decide
  have hdescent : baseEnd_5842130 < baseStart_5842130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842153 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_5842153 : Nat := 118140960795 + 5842153 * 2 ^ 59
def prefixEnd_5842153 : Nat := 4983230072969 + 3 ^ 40 * 5842153 * 2
def baseEnd_5842153 : Nat := 2999832546106386283219933

theorem tailTrace_5842153 : CollatzResearch.WordTrace tailWord_5842153 prefixEnd_5842153 2999832546106386283219933 := by
  unfold tailWord_5842153
  simp only [CollatzResearch.WordTrace]
  refine ⟨213080825203884916141755113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142053883469256610761170075 213080825203884916141755113)
  ·
    refine ⟨159810618902913687106316335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213080825203884916141755113 159810618902913687106316335)
    ·
      refine ⟨239715928354370530659474503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159810618902913687106316335 239715928354370530659474503)
      ·
        refine ⟨359573892531555795989211755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239715928354370530659474503 359573892531555795989211755)
        ·
          refine ⟨539360838797333693983817633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359573892531555795989211755 539360838797333693983817633)
          ·
            refine ⟨404520629098000270487863225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539360838797333693983817633 404520629098000270487863225)
            ·
              refine ⟨303390471823500202865897419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404520629098000270487863225 303390471823500202865897419)
              ·
                refine ⟨455085707735250304298846129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303390471823500202865897419 455085707735250304298846129)
                ·
                  refine ⟨341314280801437728224134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455085707735250304298846129 341314280801437728224134597)
                  ·
                    refine ⟨63996427650269574042025237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341314280801437728224134597 63996427650269574042025237)
                    ·
                      refine ⟨2999832546106386283219933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63996427650269574042025237 2999832546106386283219933)
                      ·
                        rfl

theorem cell23_5842153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_5842153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842153 prefixEnd_5842153 := by exact prefixLift 5842153
  have htrace : WordTrace (prefixWord ++ tailWord_5842153) baseStart_5842153 baseEnd_5842153 := by
    simpa [prefixWord, tailWord_5842153, baseEnd_5842153] using wordTrace_append hprefix tailTrace_5842153
  have hstable : (prefixWord ++ tailWord_5842153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842153).length < 2 ^ (prefixWord ++ tailWord_5842153).sum := by decide
  have hdescent : baseEnd_5842153 < baseStart_5842153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842177 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_5842177 : Nat := 118140960795 + 5842177 * 2 ^ 59
def prefixEnd_5842177 : Nat := 4983230072969 + 3 ^ 40 * 5842177 * 2
def baseEnd_5842177 : Nat := 2999844869642094189319823

theorem tailTrace_5842177 : CollatzResearch.WordTrace tailWord_5842177 prefixEnd_5842177 2999844869642094189319823 := by
  unfold tailWord_5842177
  simp only [CollatzResearch.WordTrace]
  refine ⟨213081700555797968240628785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142054467037198645493752523 213081700555797968240628785)
  ·
    refine ⟨159811275416848476180471589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213081700555797968240628785 159811275416848476180471589)
    ·
      refine ⟨29964614140659089283838423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159811275416848476180471589 29964614140659089283838423)
      ·
        refine ⟨44946921210988633925757635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29964614140659089283838423 44946921210988633925757635)
        ·
          refine ⟨67420381816482950888636453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44946921210988633925757635 67420381816482950888636453)
          ·
            refine ⟨12641321590590553291619335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67420381816482950888636453 12641321590590553291619335)
            ·
              refine ⟨18961982385885829937429003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12641321590590553291619335 18961982385885829937429003)
              ·
                refine ⟨28442973578828744906143505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18961982385885829937429003 28442973578828744906143505)
                ·
                  refine ⟨21332230184121558679607629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28442973578828744906143505 21332230184121558679607629)
                  ·
                    refine ⟨7999586319045584504852861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21332230184121558679607629 7999586319045584504852861)
                    ·
                      refine ⟨2999844869642094189319823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999586319045584504852861 2999844869642094189319823)
                      ·
                        rfl

theorem cell23_5842177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_5842177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842177 prefixEnd_5842177 := by exact prefixLift 5842177
  have htrace : WordTrace (prefixWord ++ tailWord_5842177) baseStart_5842177 baseEnd_5842177 := by
    simpa [prefixWord, tailWord_5842177, baseEnd_5842177] using wordTrace_append hprefix tailTrace_5842177
  have hstable : (prefixWord ++ tailWord_5842177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842177).length < 2 ^ (prefixWord ++ tailWord_5842177).sum := by decide
  have hdescent : baseEnd_5842177 < baseStart_5842177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842227 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 3, 4]
def baseStart_5842227 : Nat := 118140960795 + 5842227 * 2 ^ 59
def prefixEnd_5842227 : Nat := 4983230072969 + 3 ^ 40 * 5842227 * 2
def baseEnd_5842227 : Nat := 999956847891606331231531

theorem tailTrace_5842227 : CollatzResearch.WordTrace tailWord_5842227 prefixEnd_5842227 999956847891606331231531 := by
  unfold tailWord_5842227
  simp only [CollatzResearch.WordTrace]
  refine ⟨213083524205616826779948935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142055682803744551186632623 213083524205616826779948935)
  ·
    refine ⟨319625286308425240169923403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213083524205616826779948935 319625286308425240169923403)
    ·
      refine ⟨479437929462637860254885105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319625286308425240169923403 479437929462637860254885105)
      ·
        refine ⟨359578447096978395191163829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479437929462637860254885105 359578447096978395191163829)
        ·
          refine ⟨33710479415341724549171609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 359578447096978395191163829 33710479415341724549171609)
          ·
            refine ⟨25282859561506293411878707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33710479415341724549171609 25282859561506293411878707)
            ·
              refine ⟨37924289342259440117818061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25282859561506293411878707 37924289342259440117818061)
              ·
                refine ⟨14221608503347290044181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37924289342259440117818061 14221608503347290044181773)
                ·
                  refine ⟨5333103188755233766568165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14221608503347290044181773 5333103188755233766568165)
                  ·
                    refine ⟨999956847891606331231531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333103188755233766568165 999956847891606331231531)
                    ·
                      rfl

theorem cell23_5842227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 4].length) (baseStart_5842227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842227 prefixEnd_5842227 := by exact prefixLift 5842227
  have htrace : WordTrace (prefixWord ++ tailWord_5842227) baseStart_5842227 baseEnd_5842227 := by
    simpa [prefixWord, tailWord_5842227, baseEnd_5842227] using wordTrace_append hprefix tailTrace_5842227
  have hstable : (prefixWord ++ tailWord_5842227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842227).length < 2 ^ (prefixWord ++ tailWord_5842227).sum := by decide
  have hdescent : baseEnd_5842227 < baseStart_5842227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842261 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_5842261 : Nat := 118140960795 + 5842261 * 2 ^ 59
def prefixEnd_5842261 : Nat := 4983230072969 + 3 ^ 40 * 5842261 * 2
def baseEnd_5842261 : Nat := 999962667339023953556479

theorem tailTrace_5842261 : CollatzResearch.WordTrace tailWord_5842261 prefixEnd_5842261 999962667339023953556479 := by
  unfold tailWord_5842261
  simp only [CollatzResearch.WordTrace]
  refine ⟨213084764287493650586686637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142056509524995767057791091 213084764287493650586686637)
  ·
    refine ⟨79906786607810118970007489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213084764287493650586686637 79906786607810118970007489)
    ·
      refine ⟨59930089955857589227505617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79906786607810118970007489 59930089955857589227505617)
      ·
        refine ⟨44947567466893191920629213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59930089955857589227505617 44947567466893191920629213)
        ·
          refine ⟨16855337800084946970235955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44947567466893191920629213 16855337800084946970235955)
          ·
            refine ⟨25283006700127420455353933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16855337800084946970235955 25283006700127420455353933)
            ·
              refine ⟨9481127512547782670757725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25283006700127420455353933 9481127512547782670757725)
              ·
                refine ⟨3555422817205418501534147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9481127512547782670757725 3555422817205418501534147)
                ·
                  refine ⟨5333134225808127752301221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555422817205418501534147 5333134225808127752301221)
                  ·
                    refine ⟨999962667339023953556479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333134225808127752301221 999962667339023953556479)
                    ·
                      rfl

theorem cell23_5842261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_5842261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842261 prefixEnd_5842261 := by exact prefixLift 5842261
  have htrace : WordTrace (prefixWord ++ tailWord_5842261) baseStart_5842261 baseEnd_5842261 := by
    simpa [prefixWord, tailWord_5842261, baseEnd_5842261] using wordTrace_append hprefix tailTrace_5842261
  have hstable : (prefixWord ++ tailWord_5842261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842261).length < 2 ^ (prefixWord ++ tailWord_5842261).sum := by decide
  have hdescent : baseEnd_5842261 < baseStart_5842261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842311 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_5842311 : Nat := 118140960795 + 5842311 * 2 ^ 59
def prefixEnd_5842311 : Nat := 4983230072969 + 3 ^ 40 * 5842311 * 2
def baseEnd_5842311 : Nat := 2999913676049796665044207

theorem tailTrace_5842311 : CollatzResearch.WordTrace tailWord_5842311 prefixEnd_5842311 2999913676049796665044207 := by
  unfold tailWord_5842311
  simp only [CollatzResearch.WordTrace]
  refine ⟨213086587937312509126006787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142057725291541672750671191 213086587937312509126006787)
  ·
    refine ⟨319629881905968763689010181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213086587937312509126006787 319629881905968763689010181)
    ·
      refine ⟨59930602857369143191689409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319629881905968763689010181 59930602857369143191689409)
      ·
        refine ⟨44947952143026857393767057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59930602857369143191689409 44947952143026857393767057)
        ·
          refine ⟨33710964107270143045325293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44947952143026857393767057 33710964107270143045325293)
          ·
            refine ⟨12641611540226303641996985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33710964107270143045325293 12641611540226303641996985)
            ·
              refine ⟨9481208655169727731497739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12641611540226303641996985 9481208655169727731497739)
              ·
                refine ⟨14221812982754591597246609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9481208655169727731497739 14221812982754591597246609)
                ·
                  refine ⟨10666359737065943697934957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14221812982754591597246609 10666359737065943697934957)
                  ·
                    refine ⟨3999884901399728886725609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10666359737065943697934957 3999884901399728886725609)
                    ·
                      refine ⟨2999913676049796665044207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999884901399728886725609 2999913676049796665044207)
                      ·
                        rfl

theorem cell23_5842311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_5842311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842311 prefixEnd_5842311 := by exact prefixLift 5842311
  have htrace : WordTrace (prefixWord ++ tailWord_5842311) baseStart_5842311 baseEnd_5842311 := by
    simpa [prefixWord, tailWord_5842311, baseEnd_5842311] using wordTrace_append hprefix tailTrace_5842311
  have hstable : (prefixWord ++ tailWord_5842311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842311).length < 2 ^ (prefixWord ++ tailWord_5842311).sum := by decide
  have hdescent : baseEnd_5842311 < baseStart_5842311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842335 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 1, 1, 3]
def baseStart_5842335 : Nat := 118140960795 + 5842335 * 2 ^ 59
def prefixEnd_5842335 : Nat := 4983230072969 + 3 ^ 40 * 5842335 * 2
def baseEnd_5842335 : Nat := 2999925999585504571144097

theorem tailTrace_5842335 : CollatzResearch.WordTrace tailWord_5842335 prefixEnd_5842335 2999925999585504571144097 := by
  unfold tailWord_5842335
  simp only [CollatzResearch.WordTrace]
  refine ⟨213087463289225561224880459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142058308859483707483253639 213087463289225561224880459)
  ·
    refine ⟨319631194933838341837320689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213087463289225561224880459 319631194933838341837320689)
    ·
      refine ⟨239723396200378756377990517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319631194933838341837320689 239723396200378756377990517)
      ·
        refine ⟨22474068393785508410436611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239723396200378756377990517 22474068393785508410436611)
        ·
          refine ⟨33711102590678262615654917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22474068393785508410436611 33711102590678262615654917)
          ·
            refine ⟨6320831735752174240435297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33711102590678262615654917 6320831735752174240435297)
            ·
              refine ⟨4740623801814130680326473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320831735752174240435297 4740623801814130680326473)
              ·
                refine ⟨3555467851360598010244855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740623801814130680326473 3555467851360598010244855)
                ·
                  refine ⟨5333201777040897015367283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555467851360598010244855 5333201777040897015367283)
                  ·
                    refine ⟨7999802665561345523050925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5333201777040897015367283 7999802665561345523050925)
                    ·
                      refine ⟨2999925999585504571144097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999802665561345523050925 2999925999585504571144097)
                      ·
                        rfl

theorem cell23_5842335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_5842335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842335 prefixEnd_5842335 := by exact prefixLift 5842335
  have htrace : WordTrace (prefixWord ++ tailWord_5842335) baseStart_5842335 baseEnd_5842335 := by
    simpa [prefixWord, tailWord_5842335, baseEnd_5842335] using wordTrace_append hprefix tailTrace_5842335
  have hstable : (prefixWord ++ tailWord_5842335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842335).length < 2 ^ (prefixWord ++ tailWord_5842335).sum := by decide
  have hdescent : baseEnd_5842335 < baseStart_5842335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842378 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_5842378 : Nat := 118140960795 + 5842378 * 2 ^ 59
def prefixEnd_5842378 : Nat := 4983230072969 + 3 ^ 40 * 5842378 * 2
def baseEnd_5842378 : Nat := 2999948079253647902906399

theorem tailTrace_5842378 : CollatzResearch.WordTrace tailWord_5842378 prefixEnd_5842378 2999948079253647902906399 := by
  unfold tailWord_5842378
  simp only [CollatzResearch.WordTrace]
  refine ⟨53272257907017444892173947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142059354418713186379130525 53272257907017444892173947)
  ·
    refine ⟨79908386860526167338260921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53272257907017444892173947 79908386860526167338260921)
    ·
      refine ⟨59931290145394625503695691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79908386860526167338260921 59931290145394625503695691)
      ·
        refine ⟨89896935218091938255543537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59931290145394625503695691 89896935218091938255543537)
        ·
          refine ⟨67422701413568953691657653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89896935218091938255543537 67422701413568953691657653)
          ·
            refine ⟨6320878257522089408592905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67422701413568953691657653 6320878257522089408592905)
            ·
              refine ⟨4740658693141567056444679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320878257522089408592905 4740658693141567056444679)
              ·
                refine ⟨7110988039712350584667019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740658693141567056444679 7110988039712350584667019)
                ·
                  refine ⟨10666482059568525877000529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110988039712350584667019 10666482059568525877000529)
                  ·
                    refine ⟨7999861544676394407750397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10666482059568525877000529 7999861544676394407750397)
                    ·
                      refine ⟨2999948079253647902906399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999861544676394407750397 2999948079253647902906399)
                      ·
                        rfl

theorem cell23_5842378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_5842378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842378 prefixEnd_5842378 := by exact prefixLift 5842378
  have htrace : WordTrace (prefixWord ++ tailWord_5842378) baseStart_5842378 baseEnd_5842378 := by
    simpa [prefixWord, tailWord_5842378, baseEnd_5842378] using wordTrace_append hprefix tailTrace_5842378
  have hstable : (prefixWord ++ tailWord_5842378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842378).length < 2 ^ (prefixWord ++ tailWord_5842378).sum := by decide
  have hdescent : baseEnd_5842378 < baseStart_5842378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842408 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5842408 : Nat := 118140960795 + 5842408 * 2 ^ 59
def prefixEnd_5842408 : Nat := 4983230072969 + 3 ^ 40 * 5842408 * 2
def baseEnd_5842408 : Nat := 2999963483673282785531261

theorem tailTrace_5842408 : CollatzResearch.WordTrace tailWord_5842408 prefixEnd_5842408 2999963483673282785531261 := by
  unfold tailWord_5842408
  simp only [CollatzResearch.WordTrace]
  refine ⟨106545062908980547346143939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142060083878640729794858585 106545062908980547346143939)
  ·
    refine ⟨159817594363470821019215909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106545062908980547346143939 159817594363470821019215909)
    ·
      refine ⟨29965798943150778941102983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159817594363470821019215909 29965798943150778941102983)
      ·
        refine ⟨44948698414726168411654475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29965798943150778941102983 44948698414726168411654475)
        ·
          refine ⟨67423047622089252617481713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44948698414726168411654475 67423047622089252617481713)
          ·
            refine ⟨50567285716566939463111285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67423047622089252617481713 50567285716566939463111285)
            ·
              refine ⟨4740683035928150574666683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50567285716566939463111285 4740683035928150574666683)
              ·
                refine ⟨7111024553892225862000025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740683035928150574666683 7111024553892225862000025)
                ·
                  refine ⟨5333268415419169396500019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111024553892225862000025 5333268415419169396500019)
                  ·
                    refine ⟨7999902623128754094750029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5333268415419169396500019 7999902623128754094750029)
                    ·
                      refine ⟨2999963483673282785531261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7999902623128754094750029 2999963483673282785531261)
                      ·
                        rfl

theorem cell23_5842408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5842408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842408 prefixEnd_5842408 := by exact prefixLift 5842408
  have htrace : WordTrace (prefixWord ++ tailWord_5842408) baseStart_5842408 baseEnd_5842408 := by
    simpa [prefixWord, tailWord_5842408, baseEnd_5842408] using wordTrace_append hprefix tailTrace_5842408
  have hstable : (prefixWord ++ tailWord_5842408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842408).length < 2 ^ (prefixWord ++ tailWord_5842408).sum := by decide
  have hdescent : baseEnd_5842408 < baseStart_5842408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842418 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5842418 : Nat := 118140960795 + 5842418 * 2 ^ 59
def prefixEnd_5842418 : Nat := 4983230072969 + 3 ^ 40 * 5842418 * 2
def baseEnd_5842418 : Nat := 2999968618479827746406215

theorem tailTrace_5842418 : CollatzResearch.WordTrace tailWord_5842418 prefixEnd_5842418 2999968618479827746406215 := by
  unfold tailWord_5842418
  simp only [CollatzResearch.WordTrace]
  refine ⟨53272622636981216600037977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142060327031949910933434605 53272622636981216600037977)
  ·
    refine ⟨39954466977735912450028483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53272622636981216600037977 39954466977735912450028483)
    ·
      refine ⟨59931700466603868675042725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39954466977735912450028483 59931700466603868675042725)
      ·
        refine ⟨11237193837488225376570511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59931700466603868675042725 11237193837488225376570511)
        ·
          refine ⟨16855790756232338064855767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11237193837488225376570511 16855790756232338064855767)
          ·
            refine ⟨25283686134348507097283651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16855790756232338064855767 25283686134348507097283651)
            ·
              refine ⟨37925529201522760645925477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25283686134348507097283651 37925529201522760645925477)
              ·
                refine ⟨7111036725285517621111027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37925529201522760645925477 7111036725285517621111027)
                ·
                  refine ⟨10666555087928276431666541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7111036725285517621111027 10666555087928276431666541)
                  ·
                    refine ⟨3999958157973103661874953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10666555087928276431666541 3999958157973103661874953)
                    ·
                      refine ⟨2999968618479827746406215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999958157973103661874953 2999968618479827746406215)
                      ·
                        rfl

theorem cell23_5842418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5842418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842418 prefixEnd_5842418 := by exact prefixLift 5842418
  have htrace : WordTrace (prefixWord ++ tailWord_5842418) baseStart_5842418 baseEnd_5842418 := by
    simpa [prefixWord, tailWord_5842418, baseEnd_5842418] using wordTrace_append hprefix tailTrace_5842418
  have hstable : (prefixWord ++ tailWord_5842418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842418).length < 2 ^ (prefixWord ++ tailWord_5842418).sum := by decide
  have hdescent : baseEnd_5842418 < baseStart_5842418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842465 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5842465 : Nat := 118140960795 + 5842465 * 2 ^ 59
def prefixEnd_5842465 : Nat := 4983230072969 + 3 ^ 40 * 5842465 * 2
def baseEnd_5842465 : Nat := 2999992752070589062518499

theorem tailTrace_5842465 : CollatzResearch.WordTrace tailWord_5842465 prefixEnd_5842465 2999992752070589062518499 := by
  unfold tailWord_5842465
  simp only [CollatzResearch.WordTrace]
  refine ⟨213092204778754593427112849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142061469852503062284741899 213092204778754593427112849)
  ·
    refine ⟨159819153584065945070334637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213092204778754593427112849 159819153584065945070334637)
    ·
      refine ⟨59932182594024729401375489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159819153584065945070334637 59932182594024729401375489)
      ·
        refine ⟨44949136945518547051031617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59932182594024729401375489 44949136945518547051031617)
        ·
          refine ⟨33711852709138910288273713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44949136945518547051031617 33711852709138910288273713)
          ·
            refine ⟨25283889531854182716205285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33711852709138910288273713 25283889531854182716205285)
            ·
              refine ⟨4740729287222659259288491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25283889531854182716205285 4740729287222659259288491)
              ·
                refine ⟨7111093930833988888932737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740729287222659259288491 7111093930833988888932737)
                ·
                  refine ⟨5333320448125491666699553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111093930833988888932737 5333320448125491666699553)
                  ·
                    refine ⟨3999990336094118750024665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333320448125491666699553 3999990336094118750024665)
                    ·
                      refine ⟨2999992752070589062518499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3999990336094118750024665 2999992752070589062518499)
                      ·
                        rfl

theorem cell23_5842465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5842465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842465 prefixEnd_5842465 := by exact prefixLift 5842465
  have htrace : WordTrace (prefixWord ++ tailWord_5842465) baseStart_5842465 baseEnd_5842465 := by
    simpa [prefixWord, tailWord_5842465, baseEnd_5842465] using wordTrace_append hprefix tailTrace_5842465
  have hstable : (prefixWord ++ tailWord_5842465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842465).length < 2 ^ (prefixWord ++ tailWord_5842465).sum := by decide
  have hdescent : baseEnd_5842465 < baseStart_5842465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842507 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_5842507 : Nat := 118140960795 + 5842507 * 2 ^ 59
def prefixEnd_5842507 : Nat := 4983230072969 + 3 ^ 40 * 5842507 * 2
def baseEnd_5842507 : Nat := 3000014318258077898193305

theorem tailTrace_5842507 : CollatzResearch.WordTrace tailWord_5842507 prefixEnd_5842507 3000014318258077898193305 := by
  unfold tailWord_5842507
  simp only [CollatzResearch.WordTrace]
  refine ⟨213093736644602434600141775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142062491096401623066761183 213093736644602434600141775)
  ·
    refine ⟨319640604966903651900212663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213093736644602434600141775 319640604966903651900212663)
    ·
      refine ⟨479460907450355477850318995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319640604966903651900212663 479460907450355477850318995)
      ·
        refine ⟨719191361175533216775478493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479460907450355477850318995 719191361175533216775478493)
        ·
          refine ⟨269696760440824956290804435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 719191361175533216775478493 269696760440824956290804435)
          ·
            refine ⟨404545140661237434436206653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269696760440824956290804435 404545140661237434436206653)
            ·
              refine ⟨151704427747964037913577495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404545140661237434436206653 151704427747964037913577495)
              ·
                refine ⟨227556641621946056870366243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151704427747964037913577495 227556641621946056870366243)
                ·
                  refine ⟨341334962432919085305549365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227556641621946056870366243 341334962432919085305549365)
                  ·
                    refine ⟨32000152728086164247395253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341334962432919085305549365 32000152728086164247395253)
                    ·
                      refine ⟨3000014318258077898193305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32000152728086164247395253 3000014318258077898193305)
                      ·
                        rfl

theorem cell23_5842507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_5842507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842507 prefixEnd_5842507 := by exact prefixLift 5842507
  have htrace : WordTrace (prefixWord ++ tailWord_5842507) baseStart_5842507 baseEnd_5842507 := by
    simpa [prefixWord, tailWord_5842507, baseEnd_5842507] using wordTrace_append hprefix tailTrace_5842507
  have hstable : (prefixWord ++ tailWord_5842507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842507).length < 2 ^ (prefixWord ++ tailWord_5842507).sum := by decide
  have hdescent : baseEnd_5842507 < baseStart_5842507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842527 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 12]
def baseStart_5842527 : Nat := 118140960795 + 5842527 * 2 ^ 59
def prefixEnd_5842527 : Nat := 4983230072969 + 3 ^ 40 * 5842527 * 2
def baseEnd_5842527 : Nat := 333336065319018646660357

theorem tailTrace_5842527 : CollatzResearch.WordTrace tailWord_5842527 prefixEnd_5842527 333336065319018646660357 := by
  unfold tailWord_5842527
  simp only [CollatzResearch.WordTrace]
  refine ⟨213094466104529978015869835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142062977403019985343913223 213094466104529978015869835)
  ·
    refine ⟨319641699156794967023804753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213094466104529978015869835 319641699156794967023804753)
    ·
      refine ⟨239731274367596225267853565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 319641699156794967023804753 239731274367596225267853565)
      ·
        refine ⟨89899227887848584475445087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239731274367596225267853565 89899227887848584475445087)
        ·
          refine ⟨134848841831772876713167631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89899227887848584475445087 134848841831772876713167631)
          ·
            refine ⟨202273262747659315069751447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134848841831772876713167631 202273262747659315069751447)
            ·
              refine ⟨303409894121488972604627171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202273262747659315069751447 303409894121488972604627171)
              ·
                refine ⟨455114841182233458906940757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303409894121488972604627171 455114841182233458906940757)
                ·
                  refine ⟨333336065319018646660357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 455114841182233458906940757 333336065319018646660357)
                  ·
                    rfl

theorem cell23_5842527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 12].length) (baseStart_5842527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842527 prefixEnd_5842527 := by exact prefixLift 5842527
  have htrace : WordTrace (prefixWord ++ tailWord_5842527) baseStart_5842527 baseEnd_5842527 := by
    simpa [prefixWord, tailWord_5842527, baseEnd_5842527] using wordTrace_append hprefix tailTrace_5842527
  have hstable : (prefixWord ++ tailWord_5842527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842527).length < 2 ^ (prefixWord ++ tailWord_5842527).sum := by decide
  have hdescent : baseEnd_5842527 < baseStart_5842527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842531 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 3, 4]
def baseStart_5842531 : Nat := 118140960795 + 5842531 * 2 ^ 59
def prefixEnd_5842531 : Nat := 4983230072969 + 3 ^ 40 * 5842531 * 2
def baseEnd_5842531 : Nat := 1000008880597928601431065

theorem tailTrace_5842531 : CollatzResearch.WordTrace tailWord_5842531 prefixEnd_5842531 1000008880597928601431065 := by
  unfold tailWord_5842531
  simp only [CollatzResearch.WordTrace]
  refine ⟨213094611996515486699015447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142063074664343657799343631 213094611996515486699015447)
  ·
    refine ⟨319641917994773230048523171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213094611996515486699015447 319641917994773230048523171)
    ·
      refine ⟨479462876992159845072784757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319641917994773230048523171 479462876992159845072784757)
      ·
        refine ⟨44949644718014985475573571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 479462876992159845072784757 44949644718014985475573571)
        ·
          refine ⟨67424467077022478213360357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44949644718014985475573571 67424467077022478213360357)
          ·
            refine ⟨12642087576941714665005067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67424467077022478213360357 12642087576941714665005067)
            ·
              refine ⟨18963131365412571997507601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12642087576941714665005067 18963131365412571997507601)
              ·
                refine ⟨14222348524059428998130701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18963131365412571997507601 14222348524059428998130701)
                ·
                  refine ⟨5333380696522285874299013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14222348524059428998130701 5333380696522285874299013)
                  ·
                    refine ⟨1000008880597928601431065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333380696522285874299013 1000008880597928601431065)
                    ·
                      rfl

theorem cell23_5842531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 4].length) (baseStart_5842531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842531 prefixEnd_5842531 := by exact prefixLift 5842531
  have htrace : WordTrace (prefixWord ++ tailWord_5842531) baseStart_5842531 baseEnd_5842531 := by
    simpa [prefixWord, tailWord_5842531, baseEnd_5842531] using wordTrace_append hprefix tailTrace_5842531
  have hstable : (prefixWord ++ tailWord_5842531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842531).length < 2 ^ (prefixWord ++ tailWord_5842531).sum := by decide
  have hdescent : baseEnd_5842531 < baseStart_5842531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842538 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_5842538 : Nat := 118140960795 + 5842538 * 2 ^ 59
def prefixEnd_5842538 : Nat := 4983230072969 + 3 ^ 40 * 5842538 * 2
def baseEnd_5842538 : Nat := 3000030236158367276905663

theorem tailTrace_5842538 : CollatzResearch.WordTrace tailWord_5842538 prefixEnd_5842538 3000030236158367276905663 := by
  unfold tailWord_5842538
  simp only [CollatzResearch.WordTrace]
  refine ⟨53273716826872531723630067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142063244871660084596346845 53273716826872531723630067)
  ·
    refine ⟨79910575240308797585445101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53273716826872531723630067 79910575240308797585445101)
    ·
      refine ⟨29966465715115799094541913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79910575240308797585445101 29966465715115799094541913)
      ·
        refine ⟨22474849286336849320906435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29966465715115799094541913 22474849286336849320906435)
        ·
          refine ⟨33712273929505273981359653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22474849286336849320906435 33712273929505273981359653)
          ·
            refine ⟨6321051361782238871504935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33712273929505273981359653 6321051361782238871504935)
            ·
              refine ⟨9481577042673358307257403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321051361782238871504935 9481577042673358307257403)
              ·
                refine ⟨14222365564010037460886105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9481577042673358307257403 14222365564010037460886105)
                ·
                  refine ⟨10666774173007528095664579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14222365564010037460886105 10666774173007528095664579)
                  ·
                    refine ⟨16000161259511292143496869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10666774173007528095664579 16000161259511292143496869)
                    ·
                      refine ⟨3000030236158367276905663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16000161259511292143496869 3000030236158367276905663)
                      ·
                        rfl

theorem cell23_5842538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_5842538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842538 prefixEnd_5842538 := by exact prefixLift 5842538
  have htrace : WordTrace (prefixWord ++ tailWord_5842538) baseStart_5842538 baseEnd_5842538 := by
    simpa [prefixWord, tailWord_5842538, baseEnd_5842538] using wordTrace_append hprefix tailTrace_5842538
  have hstable : (prefixWord ++ tailWord_5842538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842538).length < 2 ^ (prefixWord ++ tailWord_5842538).sum := by decide
  have hdescent : baseEnd_5842538 < baseStart_5842538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842561 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 6]
def baseStart_5842561 : Nat := 118140960795 + 5842561 * 2 ^ 59
def prefixEnd_5842561 : Nat := 4983230072969 + 3 ^ 40 * 5842561 * 2
def baseEnd_5842561 : Nat := 333338005134824520768673

theorem tailTrace_5842561 : CollatzResearch.WordTrace tailWord_5842561 prefixEnd_5842561 333338005134824520768673 := by
  unfold tailWord_5842561
  simp only [CollatzResearch.WordTrace]
  refine ⟨213095706186406801822607537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142063804124271201215071691 213095706186406801822607537)
  ·
    refine ⟨159821779639805101366955653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213095706186406801822607537 159821779639805101366955653)
    ·
      refine ⟨29966583682463456506304185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159821779639805101366955653 29966583682463456506304185)
      ·
        refine ⟨22474937761847592379728139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29966583682463456506304185 22474937761847592379728139)
        ·
          refine ⟨33712406642771388569592209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22474937761847592379728139 33712406642771388569592209)
          ·
            refine ⟨25284304982078541427194157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33712406642771388569592209 25284304982078541427194157)
            ·
              refine ⟨9481614368279453035197809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25284304982078541427194157 9481614368279453035197809)
              ·
                refine ⟨7111210776209589776398357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9481614368279453035197809 7111210776209589776398357)
                ·
                  refine ⟨333338005134824520768673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7111210776209589776398357 333338005134824520768673)
                  ·
                    rfl

theorem cell23_5842561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_5842561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842561 prefixEnd_5842561 := by exact prefixLift 5842561
  have htrace : WordTrace (prefixWord ++ tailWord_5842561) baseStart_5842561 baseEnd_5842561 := by
    simpa [prefixWord, tailWord_5842561, baseEnd_5842561] using wordTrace_append hprefix tailTrace_5842561
  have hstable : (prefixWord ++ tailWord_5842561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842561).length < 2 ^ (prefixWord ++ tailWord_5842561).sum := by decide
  have hdescent : baseEnd_5842561 < baseStart_5842561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842611 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 4]
def baseStart_5842611 : Nat := 118140960795 + 5842611 * 2 ^ 59
def prefixEnd_5842611 : Nat := 4983230072969 + 3 ^ 40 * 5842611 * 2
def baseEnd_5842611 : Nat := 3000067720246145491292827

theorem tailTrace_5842611 : CollatzResearch.WordTrace tailWord_5842611 prefixEnd_5842611 3000067720246145491292827 := by
  unfold tailWord_5842611
  simp only [CollatzResearch.WordTrace]
  refine ⟨213097529836225660361927687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142065019890817106907951791 213097529836225660361927687)
  ·
    refine ⟨319646294754338490542891531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213097529836225660361927687 319646294754338490542891531)
    ·
      refine ⟨479469442131507735814337297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319646294754338490542891531 479469442131507735814337297)
      ·
        refine ⟨359602081598630801860752973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479469442131507735814337297 359602081598630801860752973)
        ·
          refine ⟨134850780599486550697782365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359602081598630801860752973 134850780599486550697782365)
          ·
            refine ⟨50569042724807456511668387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134850780599486550697782365 50569042724807456511668387)
            ·
              refine ⟨75853564087211184767502581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50569042724807456511668387 75853564087211184767502581)
              ·
                refine ⟨7111271633176048571953367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75853564087211184767502581 7111271633176048571953367)
                ·
                  refine ⟨10666907449764072857930051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7111271633176048571953367 10666907449764072857930051)
                  ·
                    refine ⟨16000361174646109286895077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10666907449764072857930051 16000361174646109286895077)
                    ·
                      refine ⟨3000067720246145491292827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16000361174646109286895077 3000067720246145491292827)
                      ·
                        rfl

theorem cell23_5842611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_5842611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842611 prefixEnd_5842611 := by exact prefixLift 5842611
  have htrace : WordTrace (prefixWord ++ tailWord_5842611) baseStart_5842611 baseEnd_5842611 := by
    simpa [prefixWord, tailWord_5842611, baseEnd_5842611] using wordTrace_append hprefix tailTrace_5842611
  have hstable : (prefixWord ++ tailWord_5842611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842611).length < 2 ^ (prefixWord ++ tailWord_5842611).sum := by decide
  have hdescent : baseEnd_5842611 < baseStart_5842611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842621 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_5842621 : Nat := 118140960795 + 5842621 * 2 ^ 59
def prefixEnd_5842621 : Nat := 4983230072969 + 3 ^ 40 * 5842621 * 2
def baseEnd_5842621 : Nat := 1000024285017563484055927

theorem tailTrace_5842621 : CollatzResearch.WordTrace tailWord_5842621 prefixEnd_5842621 1000024285017563484055927 := by
  unfold tailWord_5842621
  simp only [CollatzResearch.WordTrace]
  refine ⟨213097894566189432069791717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142065263044126288046527811 213097894566189432069791717)
  ·
    refine ⟨39955855231160518513085947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213097894566189432069791717 39955855231160518513085947)
    ·
      refine ⟨59933782846740777769628921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39955855231160518513085947 59933782846740777769628921)
      ·
        refine ⟨44950337135055583327221691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59933782846740777769628921 44950337135055583327221691)
        ·
          refine ⟨67425505702583374990832537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44950337135055583327221691 67425505702583374990832537)
          ·
            refine ⟨50569129276937531243124403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67425505702583374990832537 50569129276937531243124403)
            ·
              refine ⟨75853693915406296864686605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50569129276937531243124403 75853693915406296864686605)
              ·
                refine ⟨28445135218277361324257477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75853693915406296864686605 28445135218277361324257477)
                ·
                  refine ⟨5333462853427005248298277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28445135218277361324257477 5333462853427005248298277)
                  ·
                    refine ⟨1000024285017563484055927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333462853427005248298277 1000024285017563484055927)
                    ·
                      rfl

theorem cell23_5842621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_5842621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842621 prefixEnd_5842621 := by exact prefixLift 5842621
  have htrace : WordTrace (prefixWord ++ tailWord_5842621) baseStart_5842621 baseEnd_5842621 := by
    simpa [prefixWord, tailWord_5842621, baseEnd_5842621] using wordTrace_append hprefix tailTrace_5842621
  have hstable : (prefixWord ++ tailWord_5842621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842621).length < 2 ^ (prefixWord ++ tailWord_5842621).sum := by decide
  have hdescent : baseEnd_5842621 < baseStart_5842621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842624 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_5842624 : Nat := 118140960795 + 5842624 * 2 ^ 59
def prefixEnd_5842624 : Nat := 4983230072969 + 3 ^ 40 * 5842624 * 2
def baseEnd_5842624 : Nat := 3000074395494653940430267

theorem tailTrace_5842624 : CollatzResearch.WordTrace tailWord_5842624 prefixEnd_5842624 3000074395494653940430267 := by
  unfold tailWord_5842624
  simp only [CollatzResearch.WordTrace]
  refine ⟨106549001992589281791075463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142065335990119042388100617 106549001992589281791075463)
  ·
    refine ⟨159823502988883922686613195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106549001992589281791075463 159823502988883922686613195)
    ·
      refine ⟨239735254483325884029919793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159823502988883922686613195 239735254483325884029919793)
      ·
        refine ⟨179801440862494413022439845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239735254483325884029919793 179801440862494413022439845)
        ·
          refine ⟨33712770161717702441707471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179801440862494413022439845 33712770161717702441707471)
          ·
            refine ⟨50569155242576553662561207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33712770161717702441707471 50569155242576553662561207)
            ·
              refine ⟨75853732863864830493841811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50569155242576553662561207 75853732863864830493841811)
              ·
                refine ⟨113780599295797245740762717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75853732863864830493841811 113780599295797245740762717)
                ·
                  refine ⟨42667724735923967152786019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113780599295797245740762717 42667724735923967152786019)
                  ·
                    refine ⟨64001587103885950729179029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42667724735923967152786019 64001587103885950729179029)
                    ·
                      refine ⟨3000074395494653940430267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64001587103885950729179029 3000074395494653940430267)
                      ·
                        rfl

theorem cell23_5842624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_5842624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842624 prefixEnd_5842624 := by exact prefixLift 5842624
  have htrace : WordTrace (prefixWord ++ tailWord_5842624) baseStart_5842624 baseEnd_5842624 := by
    simpa [prefixWord, tailWord_5842624, baseEnd_5842624] using wordTrace_append hprefix tailTrace_5842624
  have hstable : (prefixWord ++ tailWord_5842624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842624).length < 2 ^ (prefixWord ++ tailWord_5842624).sum := by decide
  have hdescent : baseEnd_5842624 < baseStart_5842624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842631 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_5842631 : Nat := 118140960795 + 5842631 * 2 ^ 59
def prefixEnd_5842631 : Nat := 4983230072969 + 3 ^ 40 * 5842631 * 2
def baseEnd_5842631 : Nat := 3000077989859235413042735

theorem tailTrace_5842631 : CollatzResearch.WordTrace tailWord_5842631 prefixEnd_5842631 3000077989859235413042735 := by
  unfold tailWord_5842631
  simp only [CollatzResearch.WordTrace]
  refine ⟨213098259296153203777655747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142065506197435469185103831 213098259296153203777655747)
  ·
    refine ⟨319647388944229805666483621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213098259296153203777655747 319647388944229805666483621)
    ·
      refine ⟨59933885427043088562465679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319647388944229805666483621 59933885427043088562465679)
      ·
        refine ⟨89900828140564632843698519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59933885427043088562465679 89900828140564632843698519)
        ·
          refine ⟨134851242210846949265547779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89900828140564632843698519 134851242210846949265547779)
          ·
            refine ⟨202276863316270423898321669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134851242210846949265547779 202276863316270423898321669)
            ·
              refine ⟨37926911871800704480935313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202276863316270423898321669 37926911871800704480935313)
              ·
                refine ⟨28445183903850528360701485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37926911871800704480935313 28445183903850528360701485)
                ·
                  refine ⟨10666943963943948135263057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28445183903850528360701485 10666943963943948135263057)
                  ·
                    refine ⟨8000207972957961101447293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10666943963943948135263057 8000207972957961101447293)
                    ·
                      refine ⟨3000077989859235413042735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8000207972957961101447293 3000077989859235413042735)
                      ·
                        rfl

theorem cell23_5842631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_5842631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842631 prefixEnd_5842631 := by exact prefixLift 5842631
  have htrace : WordTrace (prefixWord ++ tailWord_5842631) baseStart_5842631 baseEnd_5842631 := by
    simpa [prefixWord, tailWord_5842631, baseEnd_5842631] using wordTrace_append hprefix tailTrace_5842631
  have hstable : (prefixWord ++ tailWord_5842631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842631).length < 2 ^ (prefixWord ++ tailWord_5842631).sum := by decide
  have hdescent : baseEnd_5842631 < baseStart_5842631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842638 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_5842638 : Nat := 118140960795 + 5842638 * 2 ^ 59
def prefixEnd_5842638 : Nat := 4983230072969 + 3 ^ 40 * 5842638 * 2
def baseEnd_5842638 : Nat := 1000027194741272295218401

theorem tailTrace_5842638 : CollatzResearch.WordTrace tailWord_5842638 prefixEnd_5842638 1000027194741272295218401 := by
  unfold tailWord_5842638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26637314325890980496645071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142065676404751895982107045 26637314325890980496645071)
  ·
    refine ⟨39955971488836470744967607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26637314325890980496645071 39955971488836470744967607)
    ·
      refine ⟨59933957233254706117451411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39955971488836470744967607 59933957233254706117451411)
      ·
        refine ⟨89900935849882059176177117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59933957233254706117451411 89900935849882059176177117)
        ·
          refine ⟨33712850943705772191066419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89900935849882059176177117 33712850943705772191066419)
          ·
            refine ⟨50569276415558658286599629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33712850943705772191066419 50569276415558658286599629)
            ·
              refine ⟨18963478655834496857474861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50569276415558658286599629 18963478655834496857474861)
              ·
                refine ⟨7111304495937936321553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18963478655834496857474861 7111304495937936321553073)
                ·
                  refine ⟨5333478371953452241164805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111304495937936321553073 5333478371953452241164805)
                  ·
                    refine ⟨1000027194741272295218401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333478371953452241164805 1000027194741272295218401)
                    ·
                      rfl

theorem cell23_5842638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_5842638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842638 prefixEnd_5842638 := by exact prefixLift 5842638
  have htrace : WordTrace (prefixWord ++ tailWord_5842638) baseStart_5842638 baseEnd_5842638 := by
    simpa [prefixWord, tailWord_5842638, baseEnd_5842638] using wordTrace_append hprefix tailTrace_5842638
  have hstable : (prefixWord ++ tailWord_5842638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842638).length < 2 ^ (prefixWord ++ tailWord_5842638).sum := by decide
  have hdescent : baseEnd_5842638 < baseStart_5842638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842695 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5842695 : Nat := 118140960795 + 5842695 * 2 ^ 59
def prefixEnd_5842695 : Nat := 4983230072969 + 3 ^ 40 * 5842695 * 2
def baseEnd_5842695 : Nat := 3000110852621123162642441

theorem tailTrace_5842695 : CollatzResearch.WordTrace tailWord_5842695 prefixEnd_5842695 3000110852621123162642441 := by
  unfold tailWord_5842695
  simp only [CollatzResearch.WordTrace]
  refine ⟨213100593567921342707985539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142067062378614228471990359 213100593567921342707985539)
  ·
    refine ⟨319650890351882014061978309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213100593567921342707985539 319650890351882014061978309)
    ·
      refine ⟨59934541940977877636620933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 319650890351882014061978309 59934541940977877636620933)
      ·
        refine ⟨11237726613933352056866425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59934541940977877636620933 11237726613933352056866425)
        ·
          refine ⟨8428294960450014042649819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11237726613933352056866425 8428294960450014042649819)
          ·
            refine ⟨12642442440675021063974729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428294960450014042649819 12642442440675021063974729)
            ·
              refine ⟨9481831830506265797981047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12642442440675021063974729 9481831830506265797981047)
              ·
                refine ⟨14222747745759398696971571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9481831830506265797981047 14222747745759398696971571)
                ·
                  refine ⟨21334121618639098045457357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14222747745759398696971571 21334121618639098045457357)
                  ·
                    refine ⟨8000295606989661767046509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21334121618639098045457357 8000295606989661767046509)
                    ·
                      refine ⟨3000110852621123162642441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8000295606989661767046509 3000110852621123162642441)
                      ·
                        rfl

theorem cell23_5842695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5842695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842695 prefixEnd_5842695 := by exact prefixLift 5842695
  have htrace : WordTrace (prefixWord ++ tailWord_5842695) baseStart_5842695 baseEnd_5842695 := by
    simpa [prefixWord, tailWord_5842695, baseEnd_5842695] using wordTrace_append hprefix tailTrace_5842695
  have hstable : (prefixWord ++ tailWord_5842695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842695).length < 2 ^ (prefixWord ++ tailWord_5842695).sum := by decide
  have hdescent : baseEnd_5842695 < baseStart_5842695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5842798 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5842798 : Nat := 118140960795 + 5842798 * 2 ^ 59
def prefixEnd_5842798 : Nat := 4983230072969 + 3 ^ 40 * 5842798 * 2
def baseEnd_5842798 : Nat := 3000163741128536259654467

theorem tailTrace_5842798 : CollatzResearch.WordTrace tailWord_5842798 prefixEnd_5842798 3000163741128536259654467 := by
  unfold tailWord_5842798
  simp only [CollatzResearch.WordTrace]
  refine ⟨26638043785818523912373131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142069566857698794199323365 26638043785818523912373131)
  ·
    refine ⟨39957065678727785868559697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26638043785818523912373131 39957065678727785868559697)
    ·
      refine ⟨29967799259045839401419773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39957065678727785868559697 29967799259045839401419773)
      ·
        refine ⟨11237924722142189775532415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29967799259045839401419773 11237924722142189775532415)
        ·
          refine ⟨16856887083213284663298623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11237924722142189775532415 16856887083213284663298623)
          ·
            refine ⟨25285330624819926994947935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16856887083213284663298623 25285330624819926994947935)
            ·
              refine ⟨37927995937229890492421903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25285330624819926994947935 37927995937229890492421903)
              ·
                refine ⟨56891993905844835738632855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37927995937229890492421903 56891993905844835738632855)
                ·
                  refine ⟨85337990858767253607949283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56891993905844835738632855 85337990858767253607949283)
                  ·
                    refine ⟨128006986288150880411923925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85337990858767253607949283 128006986288150880411923925)
                    ·
                      refine ⟨3000163741128536259654467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128006986288150880411923925 3000163741128536259654467)
                      ·
                        rfl

theorem cell23_5842798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5842798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5842798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5842798 prefixEnd_5842798 := by exact prefixLift 5842798
  have htrace : WordTrace (prefixWord ++ tailWord_5842798) baseStart_5842798 baseEnd_5842798 := by
    simpa [prefixWord, tailWord_5842798, baseEnd_5842798] using wordTrace_append hprefix tailTrace_5842798
  have hstable : (prefixWord ++ tailWord_5842798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5842798).length < 2 ^ (prefixWord ++ tailWord_5842798).sum := by decide
  have hdescent : baseEnd_5842798 < baseStart_5842798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5842798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
