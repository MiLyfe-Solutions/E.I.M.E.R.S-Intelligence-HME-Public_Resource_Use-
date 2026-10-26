import V185TrunkScan23Chunk1001

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5933629 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5933629 : Nat := 118140960795 + 5933629 * 2 ^ 59
def prefixEnd_5933629 : Nat := 4983230072969 + 3 ^ 40 * 5933629 * 2
def baseEnd_5933629 : Nat := 3046803702457070382949243

theorem tailTrace_5933629 : CollatzResearch.WordTrace tailWord_5933629 prefixEnd_5933629 3046803702457070382949243 := by
  unfold tailWord_5933629
  simp only [CollatzResearch.WordTrace]
  refine ⟨216417229020482990998755941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144278152680321993999170627 216417229020482990998755941)
  ·
    refine ⟨40578230441340560812266739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216417229020482990998755941 40578230441340560812266739)
    ·
      refine ⟨60867345662010841218400109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40578230441340560812266739 60867345662010841218400109)
      ·
        refine ⟨22825254623254065456900041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60867345662010841218400109 22825254623254065456900041)
        ·
          refine ⟨17118940967440549092675031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22825254623254065456900041 17118940967440549092675031)
          ·
            refine ⟨25678411451160823639012547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17118940967440549092675031 25678411451160823639012547)
            ·
              refine ⟨38517617176741235458518821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25678411451160823639012547 38517617176741235458518821)
              ·
                refine ⟨7222053220638981648472279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38517617176741235458518821 7222053220638981648472279)
                ·
                  refine ⟨10833079830958472472708419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222053220638981648472279 10833079830958472472708419)
                  ·
                    refine ⟨16249619746437708709062629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10833079830958472472708419 16249619746437708709062629)
                    ·
                      refine ⟨3046803702457070382949243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16249619746437708709062629 3046803702457070382949243)
                      ·
                        rfl

theorem cell23_5933629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5933629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933629 prefixEnd_5933629 := by exact prefixLift 5933629
  have htrace : WordTrace (prefixWord ++ tailWord_5933629) baseStart_5933629 baseEnd_5933629 := by
    simpa [prefixWord, tailWord_5933629, baseEnd_5933629] using wordTrace_append hprefix tailTrace_5933629
  have hstable : (prefixWord ++ tailWord_5933629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933629).length < 2 ^ (prefixWord ++ tailWord_5933629).sum := by decide
  have hdescent : baseEnd_5933629 < baseStart_5933629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933632 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_5933632 : Nat := 118140960795 + 5933632 * 2 ^ 59
def prefixEnd_5933632 : Nat := 4983230072969 + 3 ^ 40 * 5933632 * 2
def baseEnd_5933632 : Nat := 3046805242899033871211729

theorem tailTrace_5933632 : CollatzResearch.WordTrace tailWord_5933632 prefixEnd_5933632 3046805242899033871211729 := by
  unfold tailWord_5933632
  simp only [CollatzResearch.WordTrace]
  refine ⟨108208669219736061255557575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144278225626314748340743433 108208669219736061255557575)
  ·
    refine ⟨162313003829604091883336363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108208669219736061255557575 162313003829604091883336363)
    ·
      refine ⟨243469505744406137825004545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162313003829604091883336363 243469505744406137825004545)
      ·
        refine ⟨182602129308304603368753409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243469505744406137825004545 182602129308304603368753409)
        ·
          refine ⟨136951596981228452526565057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182602129308304603368753409 136951596981228452526565057)
          ·
            refine ⟨102713697735921339394923793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136951596981228452526565057 102713697735921339394923793)
            ·
              refine ⟨77035273301941004546192845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102713697735921339394923793 77035273301941004546192845)
              ·
                refine ⟨28888227488227876704822317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77035273301941004546192845 28888227488227876704822317)
                ·
                  refine ⟨10833085308085453764308369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28888227488227876704822317 10833085308085453764308369)
                  ·
                    refine ⟨8124813981064090323231277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10833085308085453764308369 8124813981064090323231277)
                    ·
                      refine ⟨3046805242899033871211729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8124813981064090323231277 3046805242899033871211729)
                      ·
                        rfl

theorem cell23_5933632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_5933632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933632 prefixEnd_5933632 := by exact prefixLift 5933632
  have htrace : WordTrace (prefixWord ++ tailWord_5933632) baseStart_5933632 baseEnd_5933632 := by
    simpa [prefixWord, tailWord_5933632, baseEnd_5933632] using wordTrace_append hprefix tailTrace_5933632
  have hstable : (prefixWord ++ tailWord_5933632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933632).length < 2 ^ (prefixWord ++ tailWord_5933632).sum := by decide
  have hdescent : baseEnd_5933632 < baseStart_5933632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933649 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_5933649 : Nat := 118140960795 + 5933649 * 2 ^ 59
def prefixEnd_5933649 : Nat := 4983230072969 + 3 ^ 40 * 5933649 * 2
def baseEnd_5933649 : Nat := 3046813972070160304699151

theorem tailTrace_5933649 : CollatzResearch.WordTrace tailWord_5933649 prefixEnd_5933649 3046813972070160304699151 := by
  unfold tailWord_5933649
  simp only [CollatzResearch.WordTrace]
  refine ⟨216417958480410534414484001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144278638986940356276322667 216417958480410534414484001)
  ·
    refine ⟨162313468860307900810863001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216417958480410534414484001 162313468860307900810863001)
    ·
      refine ⟨121735101645230925608147251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162313468860307900810863001 121735101645230925608147251)
      ·
        refine ⟨182602652467846388412220877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121735101645230925608147251 182602652467846388412220877)
        ·
          refine ⟨68475994675442395654582829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182602652467846388412220877 68475994675442395654582829)
          ·
            refine ⟨25678498003290898370468561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68475994675442395654582829 25678498003290898370468561)
            ·
              refine ⟨19258873502468173777851421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25678498003290898370468561 19258873502468173777851421)
              ·
                refine ⟨7222077563425565166694283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19258873502468173777851421 7222077563425565166694283)
                ·
                  refine ⟨10833116345138347750041425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222077563425565166694283 10833116345138347750041425)
                  ·
                    refine ⟨8124837258853760812531069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10833116345138347750041425 8124837258853760812531069)
                    ·
                      refine ⟨3046813972070160304699151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8124837258853760812531069 3046813972070160304699151)
                      ·
                        rfl

theorem cell23_5933649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_5933649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933649 prefixEnd_5933649 := by exact prefixLift 5933649
  have htrace : WordTrace (prefixWord ++ tailWord_5933649) baseStart_5933649 baseEnd_5933649 := by
    simpa [prefixWord, tailWord_5933649, baseEnd_5933649] using wordTrace_append hprefix tailTrace_5933649
  have hstable : (prefixWord ++ tailWord_5933649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933649).length < 2 ^ (prefixWord ++ tailWord_5933649).sum := by decide
  have hdescent : baseEnd_5933649 < baseStart_5933649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933652 : List Nat := [2, 4, 1, 1, 1, 5, 9]
def baseStart_5933652 : Nat := 118140960795 + 5933652 * 2 ^ 59
def prefixEnd_5933652 : Nat := 4983230072969 + 3 ^ 40 * 5933652 * 2
def baseEnd_5933652 : Nat := 37615006327310170283477

theorem tailTrace_5933652 : CollatzResearch.WordTrace tailWord_5933652 prefixEnd_5933652 37615006327310170283477 := by
  unfold tailWord_5933652
  simp only [CollatzResearch.WordTrace]
  refine ⟨108209033949699832963421605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144278711932933110617895473 108209033949699832963421605)
  ·
    refine ⟨20289193865568718680641551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108209033949699832963421605 20289193865568718680641551)
    ·
      refine ⟨30433790798353078020962327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289193865568718680641551 30433790798353078020962327)
      ·
        refine ⟨45650686197529617031443491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30433790798353078020962327 45650686197529617031443491)
        ·
          refine ⟨68476029296294425547165237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45650686197529617031443491 68476029296294425547165237)
          ·
            refine ⟨6419627746527602395046741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68476029296294425547165237 6419627746527602395046741)
            ·
              refine ⟨37615006327310170283477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6419627746527602395046741 37615006327310170283477)
              ·
                rfl

theorem cell23_5933652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 9].length) (baseStart_5933652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933652 prefixEnd_5933652 := by exact prefixLift 5933652
  have htrace : WordTrace (prefixWord ++ tailWord_5933652) baseStart_5933652 baseEnd_5933652 := by
    simpa [prefixWord, tailWord_5933652, baseEnd_5933652] using wordTrace_append hprefix tailTrace_5933652
  have hstable : (prefixWord ++ tailWord_5933652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933652).length < 2 ^ (prefixWord ++ tailWord_5933652).sum := by decide
  have hdescent : baseEnd_5933652 < baseStart_5933652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933675 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_5933675 : Nat := 118140960795 + 5933675 * 2 ^ 59
def prefixEnd_5933675 : Nat := 4983230072969 + 3 ^ 40 * 5933675 * 2
def baseEnd_5933675 : Nat := 3046827322567177202974031

theorem tailTrace_5933675 : CollatzResearch.WordTrace tailWord_5933675 prefixEnd_5933675 3046827322567177202974031 := by
  unfold tailWord_5933675
  simp only [CollatzResearch.WordTrace]
  refine ⟨216418906778316340854930479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144279271185544227236620319 216418906778316340854930479)
  ·
    refine ⟨324628360167474511282395719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216418906778316340854930479 324628360167474511282395719)
    ·
      refine ⟨486942540251211766923593579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324628360167474511282395719 486942540251211766923593579)
      ·
        refine ⟨730413810376817650385390369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486942540251211766923593579 730413810376817650385390369)
        ·
          refine ⟨547810357782613237789042777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730413810376817650385390369 547810357782613237789042777)
          ·
            refine ⟨410857768336959928341782083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547810357782613237789042777 410857768336959928341782083)
            ·
              refine ⟨616286652505439892512673125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410857768336959928341782083 616286652505439892512673125)
              ·
                refine ⟨115553747344769979846126211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616286652505439892512673125 115553747344769979846126211)
                ·
                  refine ⟨173330621017154969769189317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115553747344769979846126211 173330621017154969769189317)
                  ·
                    refine ⟨32499491440716556831722997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173330621017154969769189317 32499491440716556831722997)
                    ·
                      refine ⟨3046827322567177202974031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32499491440716556831722997 3046827322567177202974031)
                      ·
                        rfl

theorem cell23_5933675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_5933675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933675 prefixEnd_5933675 := by exact prefixLift 5933675
  have htrace : WordTrace (prefixWord ++ tailWord_5933675) baseStart_5933675 baseEnd_5933675 := by
    simpa [prefixWord, tailWord_5933675, baseEnd_5933675] using wordTrace_append hprefix tailTrace_5933675
  have hstable : (prefixWord ++ tailWord_5933675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933675).length < 2 ^ (prefixWord ++ tailWord_5933675).sum := by decide
  have hdescent : baseEnd_5933675 < baseStart_5933675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933695 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 8]
def baseStart_5933695 : Nat := 118140960795 + 5933695 * 2 ^ 59
def prefixEnd_5933695 : Nat := 4983230072969 + 3 ^ 40 * 5933695 * 2
def baseEnd_5933695 : Nat := 1015612530726755708241313

theorem tailTrace_5933695 : CollatzResearch.WordTrace tailWord_5933695 prefixEnd_5933695 1015612530726755708241313 := by
  unfold tailWord_5933695
  simp only [CollatzResearch.WordTrace]
  refine ⟨216419636238243884270658539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144279757492162589513772359 216419636238243884270658539)
  ·
    refine ⟨324629454357365826405987809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216419636238243884270658539 324629454357365826405987809)
    ·
      refine ⟨243472090768024369804490857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324629454357365826405987809 243472090768024369804490857)
      ·
        refine ⟨182604068076018277353368143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243472090768024369804490857 182604068076018277353368143)
        ·
          refine ⟨273906102114027416030052215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182604068076018277353368143 273906102114027416030052215)
          ·
            refine ⟨410859153171041124045078323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273906102114027416030052215 410859153171041124045078323)
            ·
              refine ⟨616288729756561686067617485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410859153171041124045078323 616288729756561686067617485)
              ·
                refine ⟨231108273658710632275356557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616288729756561686067617485 231108273658710632275356557)
                ·
                  refine ⟨86665602622016487103258709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231108273658710632275356557 86665602622016487103258709)
                  ·
                    refine ⟨1015612530726755708241313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86665602622016487103258709 1015612530726755708241313)
                    ·
                      rfl

theorem cell23_5933695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_5933695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933695 prefixEnd_5933695 := by exact prefixLift 5933695
  have htrace : WordTrace (prefixWord ++ tailWord_5933695) baseStart_5933695 baseEnd_5933695 := by
    simpa [prefixWord, tailWord_5933695, baseEnd_5933695] using wordTrace_append hprefix tailTrace_5933695
  have hstable : (prefixWord ++ tailWord_5933695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933695).length < 2 ^ (prefixWord ++ tailWord_5933695).sum := by decide
  have hdescent : baseEnd_5933695 < baseStart_5933695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933719 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_5933719 : Nat := 118140960795 + 5933719 * 2 ^ 59
def prefixEnd_5933719 : Nat := 4983230072969 + 3 ^ 40 * 5933719 * 2
def baseEnd_5933719 : Nat := 3046849915715975030823829

theorem tailTrace_5933719 : CollatzResearch.WordTrace tailWord_5933719 prefixEnd_5933719 3046849915715975030823829 := by
  unfold tailWord_5933719
  simp only [CollatzResearch.WordTrace]
  refine ⟨216420511590156936369532211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144280341060104624246354807 216420511590156936369532211)
  ·
    refine ⟨324630767385235404554298317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216420511590156936369532211 324630767385235404554298317)
    ·
      refine ⟨121736537769463276707861869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324630767385235404554298317 121736537769463276707861869)
      ·
        refine ⟨45651201663548728765448201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121736537769463276707861869 45651201663548728765448201)
        ·
          refine ⟨34238401247661546574086151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45651201663548728765448201 34238401247661546574086151)
          ·
            refine ⟨51357601871492319861129227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34238401247661546574086151 51357601871492319861129227)
            ·
              refine ⟨77036402807238479791693841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51357601871492319861129227 77036402807238479791693841)
              ·
                refine ⟨57777302105428859843770381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77036402807238479791693841 57777302105428859843770381)
                ·
                  refine ⟨21666488289535822441413893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57777302105428859843770381 21666488289535822441413893)
                  ·
                    refine ⟨4062466554287966707765105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21666488289535822441413893 4062466554287966707765105)
                    ·
                      refine ⟨3046849915715975030823829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062466554287966707765105 3046849915715975030823829)
                      ·
                        rfl

theorem cell23_5933719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_5933719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933719 prefixEnd_5933719 := by exact prefixLift 5933719
  have htrace : WordTrace (prefixWord ++ tailWord_5933719) baseStart_5933719 baseEnd_5933719 := by
    simpa [prefixWord, tailWord_5933719, baseEnd_5933719] using wordTrace_append hprefix tailTrace_5933719
  have hstable : (prefixWord ++ tailWord_5933719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933719).length < 2 ^ (prefixWord ++ tailWord_5933719).sum := by decide
  have hdescent : baseEnd_5933719 < baseStart_5933719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933729 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_5933729 : Nat := 118140960795 + 5933729 * 2 ^ 59
def prefixEnd_5933729 : Nat := 4983230072969 + 3 ^ 40 * 5933729 * 2
def baseEnd_5933729 : Nat := 1015618350174173330566261

theorem tailTrace_5933729 : CollatzResearch.WordTrace tailWord_5933729 prefixEnd_5933729 1015618350174173330566261 := by
  unfold tailWord_5933729
  simp only [CollatzResearch.WordTrace]
  refine ⟨216420876320120708077396241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144280584213413805384930827 216420876320120708077396241)
  ·
    refine ⟨162315657240090531058047181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216420876320120708077396241 162315657240090531058047181)
    ·
      refine ⟨60868371465033949146767693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162315657240090531058047181 60868371465033949146767693)
      ·
        refine ⟨22825639299387730930037885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60868371465033949146767693 22825639299387730930037885)
        ·
          refine ⟨8559614737270399098764207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22825639299387730930037885 8559614737270399098764207)
          ·
            refine ⟨12839422105905598648146311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8559614737270399098764207 12839422105905598648146311)
            ·
              refine ⟨19259133158858397972219467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12839422105905598648146311 19259133158858397972219467)
              ·
                refine ⟨28888699738287596958329201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19259133158858397972219467 28888699738287596958329201)
                ·
                  refine ⟨21666524803715697718746901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28888699738287596958329201 21666524803715697718746901)
                  ·
                    refine ⟨1015618350174173330566261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21666524803715697718746901 1015618350174173330566261)
                    ·
                      rfl

theorem cell23_5933729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_5933729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933729 prefixEnd_5933729 := by exact prefixLift 5933729
  have htrace : WordTrace (prefixWord ++ tailWord_5933729) baseStart_5933729 baseEnd_5933729 := by
    simpa [prefixWord, tailWord_5933729, baseEnd_5933729] using wordTrace_append hprefix tailTrace_5933729
  have hstable : (prefixWord ++ tailWord_5933729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933729).length < 2 ^ (prefixWord ++ tailWord_5933729).sum := by decide
  have hdescent : baseEnd_5933729 < baseStart_5933729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933759 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 5]
def baseStart_5933759 : Nat := 118140960795 + 5933759 * 2 ^ 59
def prefixEnd_5933759 : Nat := 4983230072969 + 3 ^ 40 * 5933759 * 2
def baseEnd_5933759 : Nat := 338541161660239430480405

theorem tailTrace_5933759 : CollatzResearch.WordTrace tailWord_5933759 prefixEnd_5933759 338541161660239430480405 := by
  unfold tailWord_5933759
  simp only [CollatzResearch.WordTrace]
  refine ⟨216421970510012023200988331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144281313673341348800658887 216421970510012023200988331)
  ·
    refine ⟨324632955765018034801482497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216421970510012023200988331 324632955765018034801482497)
    ·
      refine ⟨243474716823763526101111873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324632955765018034801482497 243474716823763526101111873)
      ·
        refine ⟨182606037617822644575833905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243474716823763526101111873 182606037617822644575833905)
        ·
          refine ⟨136954528213366983431875429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182606037617822644575833905 136954528213366983431875429)
          ·
            refine ⟨25678974040006309393476643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136954528213366983431875429 25678974040006309393476643)
            ·
              refine ⟨38518461060009464090214965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25678974040006309393476643 38518461060009464090214965)
              ·
                refine ⟨3611105724375887258457653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38518461060009464090214965 3611105724375887258457653)
                ·
                  refine ⟨338541161660239430480405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611105724375887258457653 338541161660239430480405)
                  ·
                    rfl

theorem cell23_5933759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 5].length) (baseStart_5933759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933759 prefixEnd_5933759 := by exact prefixLift 5933759
  have htrace : WordTrace (prefixWord ++ tailWord_5933759) baseStart_5933759 baseEnd_5933759 := by
    simpa [prefixWord, tailWord_5933759, baseEnd_5933759] using wordTrace_append hprefix tailTrace_5933759
  have hstable : (prefixWord ++ tailWord_5933759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933759).length < 2 ^ (prefixWord ++ tailWord_5933759).sum := by decide
  have hdescent : baseEnd_5933759 < baseStart_5933759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933770 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_5933770 : Nat := 118140960795 + 5933770 * 2 ^ 59
def prefixEnd_5933770 : Nat := 4983230072969 + 3 ^ 40 * 5933770 * 2
def baseEnd_5933770 : Nat := 3046876103229354331286095

theorem tailTrace_5933770 : CollatzResearch.WordTrace tailWord_5933770 prefixEnd_5933770 3046876103229354331286095 := by
  unfold tailWord_5933770
  simp only [CollatzResearch.WordTrace]
  refine ⟨54105592928243043019909691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144281581141981448053092509 54105592928243043019909691)
  ·
    refine ⟨81158389392364564529864537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54105592928243043019909691 81158389392364564529864537)
    ·
      refine ⟨60868792044273423397398403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81158389392364564529864537 60868792044273423397398403)
      ·
        refine ⟨91303188066410135096097605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60868792044273423397398403 91303188066410135096097605)
        ·
          refine ⟨17119347762451900330518301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91303188066410135096097605 17119347762451900330518301)
          ·
            refine ⟨6419755410919462623944363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17119347762451900330518301 6419755410919462623944363)
            ·
              refine ⟨9629633116379193935916545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419755410919462623944363 9629633116379193935916545)
              ·
                refine ⟨7222224837284395451937409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9629633116379193935916545 7222224837284395451937409)
                ·
                  refine ⟨5416668627963296588953057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7222224837284395451937409 5416668627963296588953057)
                  ·
                    refine ⟨4062501470972472441714793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5416668627963296588953057 4062501470972472441714793)
                    ·
                      refine ⟨3046876103229354331286095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062501470972472441714793 3046876103229354331286095)
                      ·
                        rfl

theorem cell23_5933770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_5933770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933770 prefixEnd_5933770 := by exact prefixLift 5933770
  have htrace : WordTrace (prefixWord ++ tailWord_5933770) baseStart_5933770 baseEnd_5933770 := by
    simpa [prefixWord, tailWord_5933770, baseEnd_5933770] using wordTrace_append hprefix tailTrace_5933770
  have hstable : (prefixWord ++ tailWord_5933770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933770).length < 2 ^ (prefixWord ++ tailWord_5933770).sum := by decide
  have hdescent : baseEnd_5933770 < baseStart_5933770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933802 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_5933802 : Nat := 118140960795 + 5933802 * 2 ^ 59
def prefixEnd_5933802 : Nat := 4983230072969 + 3 ^ 40 * 5933802 * 2
def baseEnd_5933802 : Nat := 1015630844870099402028649

theorem tailTrace_5933802 : CollatzResearch.WordTrace tailWord_5933802 prefixEnd_5933802 1015630844870099402028649 := by
  unfold tailWord_5933802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54105884712214060386200915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144282359232570827696535773 54105884712214060386200915)
  ·
    refine ⟨81158827068321090579301373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54105884712214060386200915 81158827068321090579301373)
    ·
      refine ⟨30434560150620408967238015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81158827068321090579301373 30434560150620408967238015)
      ·
        refine ⟨45651840225930613450857023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30434560150620408967238015 45651840225930613450857023)
        ·
          refine ⟨68477760338895920176285535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45651840225930613450857023 68477760338895920176285535)
          ·
            refine ⟨102716640508343880264428303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68477760338895920176285535 102716640508343880264428303)
            ·
              refine ⟨154074960762515820396642455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102716640508343880264428303 154074960762515820396642455)
              ·
                refine ⟨231112441143773730594963683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154074960762515820396642455 231112441143773730594963683)
                ·
                  refine ⟨346668661715660595892445525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231112441143773730594963683 346668661715660595892445525)
                  ·
                    refine ⟨1015630844870099402028649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 346668661715660595892445525 1015630844870099402028649)
                    ·
                      rfl

theorem cell23_5933802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_5933802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933802 prefixEnd_5933802 := by exact prefixLift 5933802
  have htrace : WordTrace (prefixWord ++ tailWord_5933802) baseStart_5933802 baseEnd_5933802 := by
    simpa [prefixWord, tailWord_5933802, baseEnd_5933802] using wordTrace_append hprefix tailTrace_5933802
  have hstable : (prefixWord ++ tailWord_5933802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933802).length < 2 ^ (prefixWord ++ tailWord_5933802).sum := by decide
  have hdescent : baseEnd_5933802 < baseStart_5933802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933809 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_5933809 : Nat := 118140960795 + 5933809 * 2 ^ 59
def prefixEnd_5933809 : Nat := 4983230072969 + 3 ^ 40 * 5933809 * 2
def baseEnd_5933809 : Nat := 3046896128974879678698415

theorem tailTrace_5933809 : CollatzResearch.WordTrace tailWord_5933809 prefixEnd_5933809 3046896128974879678698415 := by
  unfold tailWord_5933809
  simp only [CollatzResearch.WordTrace]
  refine ⟨216423794159830881740308481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144282529439887254493538987 216423794159830881740308481)
  ·
    refine ⟨162317845619873161305231361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216423794159830881740308481 162317845619873161305231361)
    ·
      refine ⟨121738384214904870978923521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162317845619873161305231361 121738384214904870978923521)
      ·
        refine ⟨91303788161178653234192641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121738384214904870978923521 91303788161178653234192641)
        ·
          refine ⟨68477841120883989925644481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91303788161178653234192641 68477841120883989925644481)
          ·
            refine ⟨51358380840662992444233361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68477841120883989925644481 51358380840662992444233361)
            ·
              refine ⟨38518785630497244333175021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51358380840662992444233361 38518785630497244333175021)
              ·
                refine ⟨14444544611436466624940633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38518785630497244333175021 14444544611436466624940633)
                ·
                  refine ⟨10833408458577349968705475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14444544611436466624940633 10833408458577349968705475)
                  ·
                    refine ⟨16250112687866024953058213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10833408458577349968705475 16250112687866024953058213)
                    ·
                      refine ⟨3046896128974879678698415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16250112687866024953058213 3046896128974879678698415)
                      ·
                        rfl

theorem cell23_5933809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_5933809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933809 prefixEnd_5933809 := by exact prefixLift 5933809
  have htrace : WordTrace (prefixWord ++ tailWord_5933809) baseStart_5933809 baseEnd_5933809 := by
    simpa [prefixWord, tailWord_5933809, baseEnd_5933809] using wordTrace_append hprefix tailTrace_5933809
  have hstable : (prefixWord ++ tailWord_5933809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933809).length < 2 ^ (prefixWord ++ tailWord_5933809).sum := by decide
  have hdescent : baseEnd_5933809 < baseStart_5933809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933826 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5933826 : Nat := 118140960795 + 5933826 * 2 ^ 59
def prefixEnd_5933826 : Nat := 4983230072969 + 3 ^ 40 * 5933826 * 2
def baseEnd_5933826 : Nat := 3046904858146006112185837

theorem tailTrace_5933826 : CollatzResearch.WordTrace tailWord_5933826 prefixEnd_5933826 3046904858146006112185837 := by
  unfold tailWord_5933826
  simp only [CollatzResearch.WordTrace]
  refine ⟨54106103550192323410919333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144282942800512862429118221 54106103550192323410919333)
  ·
    refine ⟨10144894415661060639547375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54106103550192323410919333 10144894415661060639547375)
    ·
      refine ⟨15217341623491590959321063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10144894415661060639547375 15217341623491590959321063)
      ·
        refine ⟨22826012435237386438981595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15217341623491590959321063 22826012435237386438981595)
        ·
          refine ⟨34239018652856079658472393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22826012435237386438981595 34239018652856079658472393)
          ·
            refine ⟨25679263989642059743854295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34239018652856079658472393 25679263989642059743854295)
            ·
              refine ⟨38518895984463089615781443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25679263989642059743854295 38518895984463089615781443)
              ·
                refine ⟨57778343976694634423672165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38518895984463089615781443 57778343976694634423672165)
                ·
                  refine ⟨10833439495630243954438531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57778343976694634423672165 10833439495630243954438531)
                  ·
                    refine ⟨16250159243445365931657797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10833439495630243954438531 16250159243445365931657797)
                    ·
                      refine ⟨3046904858146006112185837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16250159243445365931657797 3046904858146006112185837)
                      ·
                        rfl

theorem cell23_5933826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5933826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933826 prefixEnd_5933826 := by exact prefixLift 5933826
  have htrace : WordTrace (prefixWord ++ tailWord_5933826) baseStart_5933826 baseEnd_5933826 := by
    simpa [prefixWord, tailWord_5933826, baseEnd_5933826] using wordTrace_append hprefix tailTrace_5933826
  have hstable : (prefixWord ++ tailWord_5933826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933826).length < 2 ^ (prefixWord ++ tailWord_5933826).sum := by decide
  have hdescent : baseEnd_5933826 < baseStart_5933826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933872 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_5933872 : Nat := 118140960795 + 5933872 * 2 ^ 59
def prefixEnd_5933872 : Nat := 4983230072969 + 3 ^ 40 * 5933872 * 2
def baseEnd_5933872 : Nat := 3046928478256112932210625

theorem tailTrace_5933872 : CollatzResearch.WordTrace tailWord_5933872 prefixEnd_5933872 3046928478256112932210625 := by
  unfold tailWord_5933872
  simp only [CollatzResearch.WordTrace]
  refine ⟨108213045979301321749925935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144284061305735095666567913 108213045979301321749925935)
  ·
    refine ⟨162319568968951982624888903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108213045979301321749925935 162319568968951982624888903)
    ·
      refine ⟨243479353453427973937333355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162319568968951982624888903 243479353453427973937333355)
      ·
        refine ⟨365219030180141960906000033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243479353453427973937333355 365219030180141960906000033)
        ·
          refine ⟨273914272635106470679500025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365219030180141960906000033 273914272635106470679500025)
          ·
            refine ⟨205435704476329853009625019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273914272635106470679500025 205435704476329853009625019)
            ·
              refine ⟨308153556714494779514437529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205435704476329853009625019 308153556714494779514437529)
              ·
                refine ⟨231115167535871084635828147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308153556714494779514437529 231115167535871084635828147)
                ·
                  refine ⟨346672751303806626953742221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231115167535871084635828147 346672751303806626953742221)
                  ·
                    refine ⟨130002281738927485107653333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346672751303806626953742221 130002281738927485107653333)
                    ·
                      refine ⟨3046928478256112932210625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130002281738927485107653333 3046928478256112932210625)
                      ·
                        rfl

theorem cell23_5933872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_5933872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933872 prefixEnd_5933872 := by exact prefixLift 5933872
  have htrace : WordTrace (prefixWord ++ tailWord_5933872) baseStart_5933872 baseEnd_5933872 := by
    simpa [prefixWord, tailWord_5933872, baseEnd_5933872] using wordTrace_append hprefix tailTrace_5933872
  have hstable : (prefixWord ++ tailWord_5933872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933872).length < 2 ^ (prefixWord ++ tailWord_5933872).sum := by decide
  have hdescent : baseEnd_5933872 < baseStart_5933872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933933 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_5933933 : Nat := 118140960795 + 5933933 * 2 ^ 59
def prefixEnd_5933933 : Nat := 4983230072969 + 3 ^ 40 * 5933933 * 2
def baseEnd_5933933 : Nat := 3046959800576037193547845

theorem tailTrace_5933933 : CollatzResearch.WordTrace tailWord_5933933 prefixEnd_5933933 3046959800576037193547845 := by
  unfold tailWord_5933933
  simp only [CollatzResearch.WordTrace]
  refine ⟨216428316811381650917822453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144285544540921100611881635 216428316811381650917822453)
  ·
    refine ⟨20290154701067029773545855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216428316811381650917822453 20290154701067029773545855)
    ·
      refine ⟨30435232051600544660318783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20290154701067029773545855 30435232051600544660318783)
      ·
        refine ⟨45652848077400816990478175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30435232051600544660318783 45652848077400816990478175)
        ·
          refine ⟨68479272116101225485717263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45652848077400816990478175 68479272116101225485717263)
          ·
            refine ⟨102718908174151838228575895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68479272116101225485717263 102718908174151838228575895)
            ·
              refine ⟨154078362261227757342863843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102718908174151838228575895 154078362261227757342863843)
              ·
                refine ⟨231117543391841636014295765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154078362261227757342863843 231117543391841636014295765)
                ·
                  refine ⟨5416817423246288344085057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 231117543391841636014295765 5416817423246288344085057)
                  ·
                    refine ⟨4062613067434716258063793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5416817423246288344085057 4062613067434716258063793)
                    ·
                      refine ⟨3046959800576037193547845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062613067434716258063793 3046959800576037193547845)
                      ·
                        rfl

theorem cell23_5933933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_5933933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933933 prefixEnd_5933933 := by exact prefixLift 5933933
  have htrace : WordTrace (prefixWord ++ tailWord_5933933) baseStart_5933933 baseEnd_5933933 := by
    simpa [prefixWord, tailWord_5933933, baseEnd_5933933] using wordTrace_append hprefix tailTrace_5933933
  have hstable : (prefixWord ++ tailWord_5933933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933933).length < 2 ^ (prefixWord ++ tailWord_5933933).sum := by decide
  have hdescent : baseEnd_5933933 < baseStart_5933933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933960 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 2, 4]
def baseStart_5933960 : Nat := 118140960795 + 5933960 * 2 ^ 59
def prefixEnd_5933960 : Nat := 4983230072969 + 3 ^ 40 * 5933960 * 2
def baseEnd_5933960 : Nat := 1015657888184569529303407

theorem tailTrace_5933960 : CollatzResearch.WordTrace tailWord_5933960 prefixEnd_5933960 1015657888184569529303407 := by
  unfold tailWord_5933960
  simp only [CollatzResearch.WordTrace]
  refine ⟨108214650791141917264527667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144286201054855889686036889 108214650791141917264527667)
  ·
    refine ⟨162321976186712875896791501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108214650791141917264527667 162321976186712875896791501)
    ·
      refine ⟨60870741070017328461296813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162321976186712875896791501 60870741070017328461296813)
      ·
        refine ⟨22826527901256498172986305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60870741070017328461296813 22826527901256498172986305)
        ·
          refine ⟨17119895925942373629739729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22826527901256498172986305 17119895925942373629739729)
          ·
            refine ⟨12839921944456780222304797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17119895925942373629739729 12839921944456780222304797)
            ·
              refine ⟨4814970729171292583364299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12839921944456780222304797 4814970729171292583364299)
              ·
                refine ⟨7222456093756938875046449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814970729171292583364299 7222456093756938875046449)
                ·
                  refine ⟨5416842070317704156284837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7222456093756938875046449 5416842070317704156284837)
                  ·
                    refine ⟨1015657888184569529303407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416842070317704156284837 1015657888184569529303407)
                    ·
                      rfl

theorem cell23_5933960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_5933960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933960 prefixEnd_5933960 := by exact prefixLift 5933960
  have htrace : WordTrace (prefixWord ++ tailWord_5933960) baseStart_5933960 baseEnd_5933960 := by
    simpa [prefixWord, tailWord_5933960, baseEnd_5933960] using wordTrace_append hprefix tailTrace_5933960
  have hstable : (prefixWord ++ tailWord_5933960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933960).length < 2 ^ (prefixWord ++ tailWord_5933960).sum := by decide
  have hdescent : baseEnd_5933960 < baseStart_5933960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933983 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 3]
def baseStart_5933983 : Nat := 118140960795 + 5933983 * 2 ^ 59
def prefixEnd_5933983 : Nat := 4983230072969 + 3 ^ 40 * 5933983 * 2
def baseEnd_5933983 : Nat := 3046985474608761997922615

theorem tailTrace_5933983 : CollatzResearch.WordTrace tailWord_5933983 prefixEnd_5933983 3046985474608761997922615 := by
  unfold tailWord_5933983
  simp only [CollatzResearch.WordTrace]
  refine ⟨216430140461200509457142603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144286760307467006304761735 216430140461200509457142603)
  ·
    refine ⟨324645210691800764185713905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216430140461200509457142603 324645210691800764185713905)
    ·
      refine ⟨243483908018850573139285429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324645210691800764185713905 243483908018850573139285429)
      ·
        refine ⟨22826616376767241231808009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243483908018850573139285429 22826616376767241231808009)
        ·
          refine ⟨17119962282575430923856007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22826616376767241231808009 17119962282575430923856007)
          ·
            refine ⟨25679943423863146385784011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17119962282575430923856007 25679943423863146385784011)
            ·
              refine ⟨38519915135794719578676017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25679943423863146385784011 38519915135794719578676017)
              ·
                refine ⟨28889936351846039684007013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38519915135794719578676017 28889936351846039684007013)
                ·
                  refine ⟨5416863065971132440751315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28889936351846039684007013 5416863065971132440751315)
                  ·
                    refine ⟨8125294598956698661126973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5416863065971132440751315 8125294598956698661126973)
                    ·
                      refine ⟨3046985474608761997922615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8125294598956698661126973 3046985474608761997922615)
                      ·
                        rfl

theorem cell23_5933983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_5933983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933983 prefixEnd_5933983 := by exact prefixLift 5933983
  have htrace : WordTrace (prefixWord ++ tailWord_5933983) baseStart_5933983 baseEnd_5933983 := by
    simpa [prefixWord, tailWord_5933983, baseEnd_5933983] using wordTrace_append hprefix tailTrace_5933983
  have hstable : (prefixWord ++ tailWord_5933983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933983).length < 2 ^ (prefixWord ++ tailWord_5933983).sum := by decide
  have hdescent : baseEnd_5933983 < baseStart_5933983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933989 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_5933989 : Nat := 118140960795 + 5933989 * 2 ^ 59
def prefixEnd_5933989 : Nat := 4983230072969 + 3 ^ 40 * 5933989 * 2
def baseEnd_5933989 : Nat := 3046988555492688974447587

theorem tailTrace_5933989 : CollatzResearch.WordTrace tailWord_5933989 prefixEnd_5933989 3046988555492688974447587 := by
  unfold tailWord_5933989
  simp only [CollatzResearch.WordTrace]
  refine ⟨216430359299178772481861021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144286906199452514987907347 216430359299178772481861021)
  ·
    refine ⟨81161384737192039680697883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216430359299178772481861021 81161384737192039680697883)
    ·
      refine ⟨121742077105788059521046825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81161384737192039680697883 121742077105788059521046825)
      ·
        refine ⟨91306557829341044640785119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121742077105788059521046825 91306557829341044640785119)
        ·
          refine ⟨136959836744011566961177679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91306557829341044640785119 136959836744011566961177679)
          ·
            refine ⟨205439755116017350441766519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136959836744011566961177679 205439755116017350441766519)
            ·
              refine ⟨308159632674026025662649779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205439755116017350441766519 308159632674026025662649779)
              ·
                refine ⟨462239449011039038493974669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308159632674026025662649779 462239449011039038493974669)
                ·
                  refine ⟨173339793379139639435240501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462239449011039038493974669 173339793379139639435240501)
                  ·
                    refine ⟨16250605629294341197053797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173339793379139639435240501 16250605629294341197053797)
                    ·
                      refine ⟨3046988555492688974447587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16250605629294341197053797 3046988555492688974447587)
                      ·
                        rfl

theorem cell23_5933989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_5933989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933989 prefixEnd_5933989 := by exact prefixLift 5933989
  have htrace : WordTrace (prefixWord ++ tailWord_5933989) baseStart_5933989 baseEnd_5933989 := by
    simpa [prefixWord, tailWord_5933989, baseEnd_5933989] using wordTrace_append hprefix tailTrace_5933989
  have hstable : (prefixWord ++ tailWord_5933989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933989).length < 2 ^ (prefixWord ++ tailWord_5933989).sum := by decide
  have hdescent : baseEnd_5933989 < baseStart_5933989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933993 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 1, 3, 2]
def baseStart_5933993 : Nat := 118140960795 + 5933993 * 2 ^ 59
def prefixEnd_5933993 : Nat := 4983230072969 + 3 ^ 40 * 5933993 * 2
def baseEnd_5933993 : Nat := 3046990609415306958797569

theorem tailTrace_5933993 : CollatzResearch.WordTrace tailWord_5933993 prefixEnd_5933993 3046990609415306958797569 := by
  unfold tailWord_5933993
  simp only [CollatzResearch.WordTrace]
  refine ⟨216430505191164281165006633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144287003460776187443337755 216430505191164281165006633)
  ·
    refine ⟨162322878893373210873754975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216430505191164281165006633 162322878893373210873754975)
    ·
      refine ⟨243484318340059816310632463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162322878893373210873754975 243484318340059816310632463)
      ·
        refine ⟨365226477510089724465948695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243484318340059816310632463 365226477510089724465948695)
        ·
          refine ⟨547839716265134586698923043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365226477510089724465948695 547839716265134586698923043)
          ·
            refine ⟨821759574397701880048384565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547839716265134586698923043 821759574397701880048384565)
            ·
              refine ⟨77039960099784551254536053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 821759574397701880048384565 77039960099784551254536053)
              ·
                refine ⟨7222496259354801680112755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77039960099784551254536053 7222496259354801680112755)
                ·
                  refine ⟨10833744389032202520169133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222496259354801680112755 10833744389032202520169133)
                  ·
                    refine ⟨4062654145887075945063425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10833744389032202520169133 4062654145887075945063425)
                    ·
                      refine ⟨3046990609415306958797569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062654145887075945063425 3046990609415306958797569)
                      ·
                        rfl

theorem cell23_5933993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3, 2].length) (baseStart_5933993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933993 prefixEnd_5933993 := by exact prefixLift 5933993
  have htrace : WordTrace (prefixWord ++ tailWord_5933993) baseStart_5933993 baseEnd_5933993 := by
    simpa [prefixWord, tailWord_5933993, baseEnd_5933993] using wordTrace_append hprefix tailTrace_5933993
  have hstable : (prefixWord ++ tailWord_5933993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933993).length < 2 ^ (prefixWord ++ tailWord_5933993).sum := by decide
  have hdescent : baseEnd_5933993 < baseStart_5933993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933999 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 2, 6]
def baseStart_5933999 : Nat := 118140960795 + 5933999 * 2 ^ 59
def prefixEnd_5933999 : Nat := 4983230072969 + 3 ^ 40 * 5933999 * 2
def baseEnd_5933999 : Nat := 1015664563433077978440847

theorem tailTrace_5933999 : CollatzResearch.WordTrace tailWord_5933999 prefixEnd_5933999 1015664563433077978440847 := by
  unfold tailWord_5933999
  simp only [CollatzResearch.WordTrace]
  refine ⟨216430724029142544189725051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144287149352761696126483367 216430724029142544189725051)
  ·
    refine ⟨324646086043713816284587577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216430724029142544189725051 324646086043713816284587577)
    ·
      refine ⟨243484564532785362213440683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324646086043713816284587577 243484564532785362213440683)
      ·
        refine ⟨365226846799178043320161025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243484564532785362213440683 365226846799178043320161025)
        ·
          refine ⟨273920135099383532490120769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365226846799178043320161025 273920135099383532490120769)
          ·
            refine ⟨205440101324537649367590577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273920135099383532490120769 205440101324537649367590577)
            ·
              refine ⟨154080075993403237025692933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205440101324537649367590577 154080075993403237025692933)
              ·
                refine ⟨28890014248763106942317425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154080075993403237025692933 28890014248763106942317425)
                ·
                  refine ⟨21667510686572330206738069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28890014248763106942317425 21667510686572330206738069)
                  ·
                    refine ⟨1015664563433077978440847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21667510686572330206738069 1015664563433077978440847)
                    ·
                      rfl

theorem cell23_5933999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_5933999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933999 prefixEnd_5933999 := by exact prefixLift 5933999
  have htrace : WordTrace (prefixWord ++ tailWord_5933999) baseStart_5933999 baseEnd_5933999 := by
    simpa [prefixWord, tailWord_5933999, baseEnd_5933999] using wordTrace_append hprefix tailTrace_5933999
  have hstable : (prefixWord ++ tailWord_5933999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933999).length < 2 ^ (prefixWord ++ tailWord_5933999).sum := by decide
  have hdescent : baseEnd_5933999 < baseStart_5933999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934039 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_5934039 : Nat := 118140960795 + 5934039 * 2 ^ 59
def prefixEnd_5934039 : Nat := 4983230072969 + 3 ^ 40 * 5934039 * 2
def baseEnd_5934039 : Nat := 3047014229525413778822357

theorem tailTrace_5934039 : CollatzResearch.WordTrace tailWord_5934039 prefixEnd_5934039 3047014229525413778822357 := by
  unfold tailWord_5934039
  simp only [CollatzResearch.WordTrace]
  refine ⟨216432182948997631021181171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144288121965998420680787447 216432182948997631021181171)
  ·
    refine ⟨324648274423496446531771757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216432182948997631021181171 324648274423496446531771757)
    ·
      refine ⟨121743102908811167449414409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324648274423496446531771757 121743102908811167449414409)
      ·
        refine ⟨91307327181608375587060807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121743102908811167449414409 91307327181608375587060807)
        ·
          refine ⟨136960990772412563380591211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91307327181608375587060807 136960990772412563380591211)
          ·
            refine ⟨205441486158618845070886817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136960990772412563380591211 205441486158618845070886817)
            ·
              refine ⟨154081114618964133803165113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205441486158618845070886817 154081114618964133803165113)
              ·
                refine ⟨115560835964223100352373835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154081114618964133803165113 115560835964223100352373835)
                ·
                  refine ⟨173341253946334650528560753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115560835964223100352373835 173341253946334650528560753)
                  ·
                    refine ⟨130005940459750987896420565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173341253946334650528560753 130005940459750987896420565)
                    ·
                      refine ⟨3047014229525413778822357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130005940459750987896420565 3047014229525413778822357)
                      ·
                        rfl

theorem cell23_5934039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_5934039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934039 prefixEnd_5934039 := by exact prefixLift 5934039
  have htrace : WordTrace (prefixWord ++ tailWord_5934039) baseStart_5934039 baseEnd_5934039 := by
    simpa [prefixWord, tailWord_5934039, baseEnd_5934039] using wordTrace_append hprefix tailTrace_5934039
  have hstable : (prefixWord ++ tailWord_5934039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934039).length < 2 ^ (prefixWord ++ tailWord_5934039).sum := by decide
  have hdescent : baseEnd_5934039 < baseStart_5934039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934059 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 7]
def baseStart_5934059 : Nat := 118140960795 + 5934059 * 2 ^ 59
def prefixEnd_5934059 : Nat := 4983230072969 + 3 ^ 40 * 5934059 * 2
def baseEnd_5934059 : Nat := 1015674833046167900190755

theorem tailTrace_5934059 : CollatzResearch.WordTrace tailWord_5934059 prefixEnd_5934059 1015674833046167900190755 := by
  unfold tailWord_5934059
  simp only [CollatzResearch.WordTrace]
  refine ⟨216432912408925174436909231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144288608272616782957939487 216432912408925174436909231)
  ·
    refine ⟨324649368613387761655363847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216432912408925174436909231 324649368613387761655363847)
    ·
      refine ⟨486974052920081642483045771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324649368613387761655363847 486974052920081642483045771)
      ·
        refine ⟨730461079380122463724568657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486974052920081642483045771 730461079380122463724568657)
        ·
          refine ⟨547845809535091847793426493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730461079380122463724568657 547845809535091847793426493)
          ·
            refine ⟨205442178575659442922534935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547845809535091847793426493 205442178575659442922534935)
            ·
              refine ⟨308163267863489164383802403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205442178575659442922534935 308163267863489164383802403)
              ·
                refine ⟨462244901795233746575703605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308163267863489164383802403 462244901795233746575703605)
                ·
                  refine ⟨43335459543303163741472213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 462244901795233746575703605 43335459543303163741472213)
                  ·
                    refine ⟨1015674833046167900190755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43335459543303163741472213 1015674833046167900190755)
                    ·
                      rfl

theorem cell23_5934059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_5934059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934059 prefixEnd_5934059 := by exact prefixLift 5934059
  have htrace : WordTrace (prefixWord ++ tailWord_5934059) baseStart_5934059 baseEnd_5934059 := by
    simpa [prefixWord, tailWord_5934059, baseEnd_5934059] using wordTrace_append hprefix tailTrace_5934059
  have hstable : (prefixWord ++ tailWord_5934059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934059).length < 2 ^ (prefixWord ++ tailWord_5934059).sum := by decide
  have hdescent : baseEnd_5934059 < baseStart_5934059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934063 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 5]
def baseStart_5934063 : Nat := 118140960795 + 5934063 * 2 ^ 59
def prefixEnd_5934063 : Nat := 4983230072969 + 3 ^ 40 * 5934063 * 2
def baseEnd_5934063 : Nat := 338558505895680187213583

theorem tailTrace_5934063 : CollatzResearch.WordTrace tailWord_5934063 prefixEnd_5934063 338558505895680187213583 := by
  unfold tailWord_5934063
  simp only [CollatzResearch.WordTrace]
  refine ⟨216433058300910683120054843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144288705533940455413369895 216433058300910683120054843)
  ·
    refine ⟨324649587451366024680082265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216433058300910683120054843 324649587451366024680082265)
    ·
      refine ⟨243487190588524518510061699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324649587451366024680082265 243487190588524518510061699)
      ·
        refine ⟨365230785882786777765092549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243487190588524518510061699 365230785882786777765092549)
        ·
          refine ⟨68480772353022520830954853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365230785882786777765092549 68480772353022520830954853)
          ·
            refine ⟨12840144816191722655804035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68480772353022520830954853 12840144816191722655804035)
            ·
              refine ⟨19260217224287583983706053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12840144816191722655804035 19260217224287583983706053)
              ·
                refine ⟨3611290729553921996944885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19260217224287583983706053 3611290729553921996944885)
                ·
                  refine ⟨338558505895680187213583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611290729553921996944885 338558505895680187213583)
                  ·
                    rfl

theorem cell23_5934063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 5].length) (baseStart_5934063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934063 prefixEnd_5934063 := by exact prefixLift 5934063
  have htrace : WordTrace (prefixWord ++ tailWord_5934063) baseStart_5934063 baseEnd_5934063 := by
    simpa [prefixWord, tailWord_5934063, baseEnd_5934063] using wordTrace_append hprefix tailTrace_5934063
  have hstable : (prefixWord ++ tailWord_5934063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934063).length < 2 ^ (prefixWord ++ tailWord_5934063).sum := by decide
  have hdescent : baseEnd_5934063 < baseStart_5934063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934123 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 3, 4]
def baseStart_5934123 : Nat := 118140960795 + 5934123 * 2 ^ 59
def prefixEnd_5934123 : Nat := 4983230072969 + 3 ^ 40 * 5934123 * 2
def baseEnd_5934123 : Nat := 1015685787300130483390657

theorem tailTrace_5934123 : CollatzResearch.WordTrace tailWord_5934123 prefixEnd_5934123 1015685787300130483390657 := by
  unfold tailWord_5934123
  simp only [CollatzResearch.WordTrace]
  refine ⟨216435246680693313367239023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144290164453795542244826015 216435246680693313367239023)
  ·
    refine ⟨324652870021039970050858535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216435246680693313367239023 324652870021039970050858535)
    ·
      refine ⟨486979305031559955076287803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324652870021039970050858535 486979305031559955076287803)
      ·
        refine ⟨730468957547339932614431705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486979305031559955076287803 730468957547339932614431705)
        ·
          refine ⟨547851718160504949460823779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730468957547339932614431705 547851718160504949460823779)
          ·
            refine ⟨821777577240757424191235669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547851718160504949460823779 821777577240757424191235669)
            ·
              refine ⟨9630205983290126064741043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 821777577240757424191235669 9630205983290126064741043)
              ·
                refine ⟨14445308974935189097111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9630205983290126064741043 14445308974935189097111565)
                ·
                  refine ⟨5416990865600695911416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14445308974935189097111565 5416990865600695911416837)
                  ·
                    refine ⟨1015685787300130483390657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416990865600695911416837 1015685787300130483390657)
                    ·
                      rfl

theorem cell23_5934123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 4].length) (baseStart_5934123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934123 prefixEnd_5934123 := by exact prefixLift 5934123
  have htrace : WordTrace (prefixWord ++ tailWord_5934123) baseStart_5934123 baseEnd_5934123 := by
    simpa [prefixWord, tailWord_5934123, baseEnd_5934123] using wordTrace_append hprefix tailTrace_5934123
  have hstable : (prefixWord ++ tailWord_5934123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934123).length < 2 ^ (prefixWord ++ tailWord_5934123).sum := by decide
  have hdescent : baseEnd_5934123 < baseStart_5934123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934163 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 3]
def baseStart_5934163 : Nat := 118140960795 + 5934163 * 2 ^ 59
def prefixEnd_5934163 : Nat := 4983230072969 + 3 ^ 40 * 5934163 * 2
def baseEnd_5934163 : Nat := 3047077901126571293671787

theorem tailTrace_5934163 : CollatzResearch.WordTrace tailWord_5934163 prefixEnd_5934163 3047077901126571293671787 := by
  unfold tailWord_5934163
  simp only [CollatzResearch.WordTrace]
  refine ⟨216436705600548400198695143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144291137067032266799130095 216436705600548400198695143)
  ·
    refine ⟨324655058400822600298042715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216436705600548400198695143 324655058400822600298042715)
    ·
      refine ⟨486982587601233900447064073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324655058400822600298042715 486982587601233900447064073)
      ·
        refine ⟨365236940700925425335298055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486982587601233900447064073 365236940700925425335298055)
        ·
          refine ⟨547855411051388138002947083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365236940700925425335298055 547855411051388138002947083)
          ·
            refine ⟨821783116577082207004420625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547855411051388138002947083 821783116577082207004420625)
            ·
              refine ⟨616337337432811655253315469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821783116577082207004420625 616337337432811655253315469)
              ·
                refine ⟨231126501537304370719993301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616337337432811655253315469 231126501537304370719993301)
                ·
                  refine ⟨5417027379780571188749843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 231126501537304370719993301 5417027379780571188749843)
                  ·
                    refine ⟨8125541069670856783124765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5417027379780571188749843 8125541069670856783124765)
                    ·
                      refine ⟨3047077901126571293671787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8125541069670856783124765 3047077901126571293671787)
                      ·
                        rfl

theorem cell23_5934163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_5934163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934163 prefixEnd_5934163 := by exact prefixLift 5934163
  have htrace : WordTrace (prefixWord ++ tailWord_5934163) baseStart_5934163 baseEnd_5934163 := by
    simpa [prefixWord, tailWord_5934163, baseEnd_5934163] using wordTrace_append hprefix tailTrace_5934163
  have hstable : (prefixWord ++ tailWord_5934163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934163).length < 2 ^ (prefixWord ++ tailWord_5934163).sum := by decide
  have hdescent : baseEnd_5934163 < baseStart_5934163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934174 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5934174 : Nat := 118140960795 + 5934174 * 2 ^ 59
def prefixEnd_5934174 : Nat := 4983230072969 + 3 ^ 40 * 5934174 * 2
def baseEnd_5934174 : Nat := 1015694516471256916878079

theorem tailTrace_5934174 : CollatzResearch.WordTrace tailWord_5934174 prefixEnd_5934174 1015694516471256916878079 := by
  unfold tailWord_5934174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27054638350438568634668197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144291404535672366051563717 27054638350438568634668197)
  ·
    refine ⟨5072744690707231619000287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27054638350438568634668197 5072744690707231619000287)
    ·
      refine ⟨7609117036060847428500431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072744690707231619000287 7609117036060847428500431)
      ·
        refine ⟨11413675554091271142750647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609117036060847428500431 11413675554091271142750647)
        ·
          refine ⟨17120513331136906714125971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413675554091271142750647 17120513331136906714125971)
          ·
            refine ⟨25680769996705360071188957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17120513331136906714125971 25680769996705360071188957)
            ·
              refine ⟨9630288748764510026695859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25680769996705360071188957 9630288748764510026695859)
              ·
                refine ⟨14445433123146765040043789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9630288748764510026695859 14445433123146765040043789)
                ·
                  refine ⟨5417037421180036890016421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14445433123146765040043789 5417037421180036890016421)
                  ·
                    refine ⟨1015694516471256916878079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5417037421180036890016421 1015694516471256916878079)
                    ·
                      rfl

theorem cell23_5934174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5934174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934174 prefixEnd_5934174 := by exact prefixLift 5934174
  have htrace : WordTrace (prefixWord ++ tailWord_5934174) baseStart_5934174 baseEnd_5934174 := by
    simpa [prefixWord, tailWord_5934174, baseEnd_5934174] using wordTrace_append hprefix tailTrace_5934174
  have hstable : (prefixWord ++ tailWord_5934174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934174).length < 2 ^ (prefixWord ++ tailWord_5934174).sum := by decide
  have hdescent : baseEnd_5934174 < baseStart_5934174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934203 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 6, 2]
def baseStart_5934203 : Nat := 118140960795 + 5934203 * 2 ^ 59
def prefixEnd_5934203 : Nat := 4983230072969 + 3 ^ 40 * 5934203 * 2
def baseEnd_5934203 : Nat := 3047098440352751137171603

theorem tailTrace_5934203 : CollatzResearch.WordTrace tailWord_5934203 prefixEnd_5934203 3047098440352751137171603 := by
  unfold tailWord_5934203
  simp only [CollatzResearch.WordTrace]
  refine ⟨216438164520403487030151263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144292109680268991353434175 216438164520403487030151263)
  ·
    refine ⟨324657246780605230545226895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216438164520403487030151263 324657246780605230545226895)
    ·
      refine ⟨486985870170907845817840343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324657246780605230545226895 486985870170907845817840343)
      ·
        refine ⟨730478805256361768726760515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486985870170907845817840343 730478805256361768726760515)
        ·
          refine ⟨1095718207884542653090140773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730478805256361768726760515 1095718207884542653090140773)
          ·
            refine ⟨205447163978351747454401395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1095718207884542653090140773 205447163978351747454401395)
            ·
              refine ⟨308170745967527621181602093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205447163978351747454401395 308170745967527621181602093)
              ·
                refine ⟨115564029737822857943100785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308170745967527621181602093 115564029737822857943100785)
                ·
                  refine ⟨86673022303367143457325589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115564029737822857943100785 86673022303367143457325589)
                  ·
                    refine ⟨4062797920470334849562137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86673022303367143457325589 4062797920470334849562137)
                    ·
                      refine ⟨3047098440352751137171603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062797920470334849562137 3047098440352751137171603)
                      ·
                        rfl

theorem cell23_5934203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6, 2].length) (baseStart_5934203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934203 prefixEnd_5934203 := by exact prefixLift 5934203
  have htrace : WordTrace (prefixWord ++ tailWord_5934203) baseStart_5934203 baseEnd_5934203 := by
    simpa [prefixWord, tailWord_5934203, baseEnd_5934203] using wordTrace_append hprefix tailTrace_5934203
  have hstable : (prefixWord ++ tailWord_5934203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934203).length < 2 ^ (prefixWord ++ tailWord_5934203).sum := by decide
  have hdescent : baseEnd_5934203 < baseStart_5934203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934231 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 1, 1, 3]
def baseStart_5934231 : Nat := 118140960795 + 5934231 * 2 ^ 59
def prefixEnd_5934231 : Nat := 4983230072969 + 3 ^ 40 * 5934231 * 2
def baseEnd_5934231 : Nat := 3047112817811077027621475

theorem tailTrace_5934231 : CollatzResearch.WordTrace tailWord_5934231 prefixEnd_5934231 3047112817811077027621475 := by
  unfold tailWord_5934231
  simp only [CollatzResearch.WordTrace]
  refine ⟨216439185764302047812170547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144292790509534698541447031 216439185764302047812170547)
  ·
    refine ⟨324658778646453071718255821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216439185764302047812170547 324658778646453071718255821)
    ·
      refine ⟨121747041992419901894345933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324658778646453071718255821 121747041992419901894345933)
      ·
        refine ⟨45655140747157463210379725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121747041992419901894345933 45655140747157463210379725)
        ·
          refine ⟨17120677780184048703892397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45655140747157463210379725 17120677780184048703892397)
          ·
            refine ⟨6420254167569018263959649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17120677780184048703892397 6420254167569018263959649)
            ·
              refine ⟨4815190625676763697969737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420254167569018263959649 4815190625676763697969737)
              ·
                refine ⟨3611392969257572773477303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4815190625676763697969737 3611392969257572773477303)
                ·
                  refine ⟨5417089453886359160215955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611392969257572773477303 5417089453886359160215955)
                  ·
                    refine ⟨8125634180829538740323933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5417089453886359160215955 8125634180829538740323933)
                    ·
                      refine ⟨3047112817811077027621475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8125634180829538740323933 3047112817811077027621475)
                      ·
                        rfl

theorem cell23_5934231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_5934231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934231 prefixEnd_5934231 := by exact prefixLift 5934231
  have htrace : WordTrace (prefixWord ++ tailWord_5934231) baseStart_5934231 baseEnd_5934231 := by
    simpa [prefixWord, tailWord_5934231, baseEnd_5934231] using wordTrace_append hprefix tailTrace_5934231
  have hstable : (prefixWord ++ tailWord_5934231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934231).length < 2 ^ (prefixWord ++ tailWord_5934231).sum := by decide
  have hdescent : baseEnd_5934231 < baseStart_5934231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934237 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_5934237 : Nat := 118140960795 + 5934237 * 2 ^ 59
def prefixEnd_5934237 : Nat := 4983230072969 + 3 ^ 40 * 5934237 * 2
def baseEnd_5934237 : Nat := 3047115898695004004146447

theorem tailTrace_5934237 : CollatzResearch.WordTrace tailWord_5934237 prefixEnd_5934237 3047115898695004004146447 := by
  unfold tailWord_5934237
  simp only [CollatzResearch.WordTrace]
  refine ⟨216439404602280310836888965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144292936401520207224592643 216439404602280310836888965)
  ·
    refine ⟨40582388362927558281916681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216439404602280310836888965 40582388362927558281916681)
    ·
      refine ⟨30436791272195668711437511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40582388362927558281916681 30436791272195668711437511)
      ·
        refine ⟨45655186908293503067156267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30436791272195668711437511 45655186908293503067156267)
        ·
          refine ⟨68482780362440254600734401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45655186908293503067156267 68482780362440254600734401)
          ·
            refine ⟨51362085271830190950550801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68482780362440254600734401 51362085271830190950550801)
            ·
              refine ⟨38521563953872643212913101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51362085271830190950550801 38521563953872643212913101)
              ·
                refine ⟨14445586482702241204842413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38521563953872643212913101 14445586482702241204842413)
                ·
                  refine ⟨5417094931013340451815905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14445586482702241204842413 5417094931013340451815905)
                  ·
                    refine ⟨4062821198260005338861929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5417094931013340451815905 4062821198260005338861929)
                    ·
                      refine ⟨3047115898695004004146447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062821198260005338861929 3047115898695004004146447)
                      ·
                        rfl

theorem cell23_5934237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_5934237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934237 prefixEnd_5934237 := by exact prefixLift 5934237
  have htrace : WordTrace (prefixWord ++ tailWord_5934237) baseStart_5934237 baseEnd_5934237 := by
    simpa [prefixWord, tailWord_5934237, baseEnd_5934237] using wordTrace_append hprefix tailTrace_5934237
  have hstable : (prefixWord ++ tailWord_5934237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934237).length < 2 ^ (prefixWord ++ tailWord_5934237).sum := by decide
  have hdescent : baseEnd_5934237 < baseStart_5934237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934247 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 2, 4]
def baseStart_5934247 : Nat := 118140960795 + 5934247 * 2 ^ 59
def prefixEnd_5934247 : Nat := 4983230072969 + 3 ^ 40 * 5934247 * 2
def baseEnd_5934247 : Nat := 1015707011167182988340467

theorem tailTrace_5934247 : CollatzResearch.WordTrace tailWord_5934247 prefixEnd_5934247 1015707011167182988340467 := by
  unfold tailWord_5934247
  simp only [CollatzResearch.WordTrace]
  refine ⟨216439769332244082544752995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144293179554829388363168663 216439769332244082544752995)
  ·
    refine ⟨324659653998366123817129493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216439769332244082544752995 324659653998366123817129493)
    ·
      refine ⟨15218421281173412053927945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 324659653998366123817129493 15218421281173412053927945)
      ·
        refine ⟨11413815960880059040445959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15218421281173412053927945 11413815960880059040445959)
        ·
          refine ⟨17120723941320088560668939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413815960880059040445959 17120723941320088560668939)
          ·
            refine ⟨25681085911980132841003409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17120723941320088560668939 25681085911980132841003409)
            ·
              refine ⟨19260814433985099630752557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25681085911980132841003409 19260814433985099630752557)
              ·
                refine ⟨7222805412744412361532209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19260814433985099630752557 7222805412744412361532209)
                ·
                  refine ⟨5417104059558309271149157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7222805412744412361532209 5417104059558309271149157)
                  ·
                    refine ⟨1015707011167182988340467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5417104059558309271149157 1015707011167182988340467)
                    ·
                      rfl

theorem cell23_5934247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_5934247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934247 prefixEnd_5934247 := by exact prefixLift 5934247
  have htrace : WordTrace (prefixWord ++ tailWord_5934247) baseStart_5934247 baseEnd_5934247 := by
    simpa [prefixWord, tailWord_5934247, baseEnd_5934247] using wordTrace_append hprefix tailTrace_5934247
  have hstable : (prefixWord ++ tailWord_5934247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934247).length < 2 ^ (prefixWord ++ tailWord_5934247).sum := by decide
  have hdescent : baseEnd_5934247 < baseStart_5934247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934303 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 2, 6]
def baseStart_5934303 : Nat := 118140960795 + 5934303 * 2 ^ 59
def prefixEnd_5934303 : Nat := 4983230072969 + 3 ^ 40 * 5934303 * 2
def baseEnd_5934303 : Nat := 1015716596139400248640381

theorem tailTrace_5934303 : CollatzResearch.WordTrace tailWord_5934303 prefixEnd_5934303 1015716596139400248640381 := by
  unfold tailWord_5934303
  simp only [CollatzResearch.WordTrace]
  refine ⟨216441811820041204108791563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144294541213360802739194375 216441811820041204108791563)
  ·
    refine ⟨324662717730061806163187345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216441811820041204108791563 324662717730061806163187345)
    ·
      refine ⟨243497038297546354622390509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324662717730061806163187345 243497038297546354622390509)
      ·
        refine ⟨91311389361579882983396441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243497038297546354622390509 91311389361579882983396441)
        ·
          refine ⟨68483542021184912237547331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91311389361579882983396441 68483542021184912237547331)
          ·
            refine ⟨102725313031777368356320997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68483542021184912237547331 102725313031777368356320997)
            ·
              refine ⟨19260996193458256566810187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102725313031777368356320997 19260996193458256566810187)
              ·
                refine ⟨28891494290187384850215281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19260996193458256566810187 28891494290187384850215281)
                ·
                  refine ⟨21668620717640538637661461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28891494290187384850215281 21668620717640538637661461)
                  ·
                    refine ⟨1015716596139400248640381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21668620717640538637661461 1015716596139400248640381)
                    ·
                      rfl

theorem cell23_5934303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_5934303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934303 prefixEnd_5934303 := by exact prefixLift 5934303
  have htrace : WordTrace (prefixWord ++ tailWord_5934303) baseStart_5934303 baseEnd_5934303 := by
    simpa [prefixWord, tailWord_5934303, baseEnd_5934303] using wordTrace_append hprefix tailTrace_5934303
  have hstable : (prefixWord ++ tailWord_5934303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934303).length < 2 ^ (prefixWord ++ tailWord_5934303).sum := by decide
  have hdescent : baseEnd_5934303 < baseStart_5934303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934304 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3]
def baseStart_5934304 : Nat := 118140960795 + 5934304 * 2 ^ 59
def prefixEnd_5934304 : Nat := 4983230072969 + 3 ^ 40 * 5934304 * 2
def baseEnd_5934304 : Nat := 3047150301898855242008639

theorem tailTrace_5934304 : CollatzResearch.WordTrace tailWord_5934304 prefixEnd_5934304 3047150301898855242008639 := by
  unfold tailWord_5934304
  simp only [CollatzResearch.WordTrace]
  refine ⟨108220924146518790639788983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144294565528691720853051977 108220924146518790639788983)
  ·
    refine ⟨162331386219778185959683475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108220924146518790639788983 162331386219778185959683475)
    ·
      refine ⟨243497079329667278939525213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162331386219778185959683475 243497079329667278939525213)
      ·
        refine ⟨91311404748625229602321955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243497079329667278939525213 91311404748625229602321955)
        ·
          refine ⟨136967107122937844403482933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91311404748625229602321955 136967107122937844403482933)
          ·
            refine ⟨12840666292775422912826525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136967107122937844403482933 12840666292775422912826525)
            ·
              refine ⟨4815249859790783592309947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12840666292775422912826525 4815249859790783592309947)
              ·
                refine ⟨7222874789686175388464921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815249859790783592309947 7222874789686175388464921)
                ·
                  refine ⟨5417156092264631541348691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7222874789686175388464921 5417156092264631541348691)
                  ·
                    refine ⟨8125734138396947312023037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5417156092264631541348691 8125734138396947312023037)
                    ·
                      refine ⟨3047150301898855242008639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8125734138396947312023037 3047150301898855242008639)
                      ·
                        rfl

theorem cell23_5934304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_5934304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934304 prefixEnd_5934304 := by exact prefixLift 5934304
  have htrace : WordTrace (prefixWord ++ tailWord_5934304) baseStart_5934304 baseEnd_5934304 := by
    simpa [prefixWord, tailWord_5934304, baseEnd_5934304] using wordTrace_append hprefix tailTrace_5934304
  have hstable : (prefixWord ++ tailWord_5934304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934304).length < 2 ^ (prefixWord ++ tailWord_5934304).sum := by decide
  have hdescent : baseEnd_5934304 < baseStart_5934304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934314 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_5934314 : Nat := 118140960795 + 5934314 * 2 ^ 59
def prefixEnd_5934314 : Nat := 4983230072969 + 3 ^ 40 * 5934314 * 2
def baseEnd_5934314 : Nat := 3047155436705400202883593

theorem tailTrace_5934314 : CollatzResearch.WordTrace tailWord_5934314 prefixEnd_5934314 3047155436705400202883593 := by
  unfold tailWord_5934314
  simp only [CollatzResearch.WordTrace]
  refine ⟨54110553255750338246860499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144294808682000901991627997 54110553255750338246860499)
  ·
    refine ⟨81165829883625507370290749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54110553255750338246860499 81165829883625507370290749)
    ·
      refine ⟨30437186206359565263859031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81165829883625507370290749 30437186206359565263859031)
      ·
        refine ⟨45655779309539347895788547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30437186206359565263859031 45655779309539347895788547)
        ·
          refine ⟨68483668964309021843682821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45655779309539347895788547 68483668964309021843682821)
          ·
            refine ⟨12840687930807941595690529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68483668964309021843682821 12840687930807941595690529)
            ·
              refine ⟨9630515948105956196767897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12840687930807941595690529 9630515948105956196767897)
              ·
                refine ⟨7222886961079467147575923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9630515948105956196767897 7222886961079467147575923)
                ·
                  refine ⟨10834330441619200721363885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222886961079467147575923 10834330441619200721363885)
                  ·
                    refine ⟨4062873915607200270511457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10834330441619200721363885 4062873915607200270511457)
                    ·
                      refine ⟨3047155436705400202883593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062873915607200270511457 3047155436705400202883593)
                      ·
                        rfl

theorem cell23_5934314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_5934314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934314 prefixEnd_5934314 := by exact prefixLift 5934314
  have htrace : WordTrace (prefixWord ++ tailWord_5934314) baseStart_5934314 baseEnd_5934314 := by
    simpa [prefixWord, tailWord_5934314, baseEnd_5934314] using wordTrace_append hprefix tailTrace_5934314
  have hstable : (prefixWord ++ tailWord_5934314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934314).length < 2 ^ (prefixWord ++ tailWord_5934314).sum := by decide
  have hdescent : baseEnd_5934314 < baseStart_5934314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934350 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_5934350 : Nat := 118140960795 + 5934350 * 2 ^ 59
def prefixEnd_5934350 : Nat := 4983230072969 + 3 ^ 40 * 5934350 * 2
def baseEnd_5934350 : Nat := 338574880223218006892603

theorem tailTrace_5934350 : CollatzResearch.WordTrace tailWord_5934350 prefixEnd_5934350 338574880223218006892603 := by
  unfold tailWord_5934350
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055440756358866391969063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144295684033913954090501669 27055440756358866391969063)
  ·
    refine ⟨40583161134538299587953595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27055440756358866391969063 40583161134538299587953595)
    ·
      refine ⟨60874741701807449381930393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40583161134538299587953595 60874741701807449381930393)
      ·
        refine ⟨45656056276355587036447795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60874741701807449381930393 45656056276355587036447795)
        ·
          refine ⟨68484084414533380554671693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45656056276355587036447795 68484084414533380554671693)
          ·
            refine ⟨25681531655450017708001885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68484084414533380554671693 25681531655450017708001885)
            ·
              refine ⟨9630574370793756640500707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25681531655450017708001885 9630574370793756640500707)
              ·
                refine ⟨14445861556190634960751061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9630574370793756640500707 14445861556190634960751061)
                ·
                  refine ⟨338574880223218006892603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14445861556190634960751061 338574880223218006892603)
                  ·
                    rfl

theorem cell23_5934350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_5934350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934350 prefixEnd_5934350 := by exact prefixLift 5934350
  have htrace : WordTrace (prefixWord ++ tailWord_5934350) baseStart_5934350 baseEnd_5934350 := by
    simpa [prefixWord, tailWord_5934350, baseEnd_5934350] using wordTrace_append hprefix tailTrace_5934350
  have hstable : (prefixWord ++ tailWord_5934350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934350).length < 2 ^ (prefixWord ++ tailWord_5934350).sum := by decide
  have hdescent : baseEnd_5934350 < baseStart_5934350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934363 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 6, 5]
def baseStart_5934363 : Nat := 118140960795 + 5934363 * 2 ^ 59
def prefixEnd_5934363 : Nat := 4983230072969 + 3 ^ 40 * 5934363 * 2
def baseEnd_5934363 : Nat := 1015726865752490170390289

theorem tailTrace_5934363 : CollatzResearch.WordTrace tailWord_5934363 prefixEnd_5934363 1015726865752490170390289 := by
  unfold tailWord_5934363
  simp only [CollatzResearch.WordTrace]
  refine ⟨216444000199823834355975743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144296000133215889570650495 216444000199823834355975743)
  ·
    refine ⟨324666000299735751533963615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216444000199823834355975743 324666000299735751533963615)
    ·
      refine ⟨486999000449603627300945423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324666000299735751533963615 486999000449603627300945423)
      ·
        refine ⟨730498500674405440951418135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486999000449603627300945423 730498500674405440951418135)
        ·
          refine ⟨1095747751011608161427127203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730498500674405440951418135 1095747751011608161427127203)
          ·
            refine ⟨1643621626517412242140690805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095747751011608161427127203 1643621626517412242140690805)
            ·
              refine ⟨154089527486007397700689763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1643621626517412242140690805 154089527486007397700689763)
              ·
                refine ⟨231134291229011096551034645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154089527486007397700689763 231134291229011096551034645)
                ·
                  refine ⟨10834419901359895150829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231134291229011096551034645 10834419901359895150829749)
                  ·
                    refine ⟨1015726865752490170390289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10834419901359895150829749 1015726865752490170390289)
                    ·
                      rfl

theorem cell23_5934363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 5].length) (baseStart_5934363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934363 prefixEnd_5934363 := by exact prefixLift 5934363
  have htrace : WordTrace (prefixWord ++ tailWord_5934363) baseStart_5934363 baseEnd_5934363 := by
    simpa [prefixWord, tailWord_5934363, baseEnd_5934363] using wordTrace_append hprefix tailTrace_5934363
  have hstable : (prefixWord ++ tailWord_5934363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934363).length < 2 ^ (prefixWord ++ tailWord_5934363).sum := by decide
  have hdescent : baseEnd_5934363 < baseStart_5934363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934400 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_5934400 : Nat := 118140960795 + 5934400 * 2 ^ 59
def prefixEnd_5934400 : Nat := 4983230072969 + 3 ^ 40 * 5934400 * 2
def baseEnd_5934400 : Nat := 3047199596041686866408197

theorem tailTrace_5934400 : CollatzResearch.WordTrace tailWord_5934400 prefixEnd_5934400 3047199596041686866408197 := by
  unfold tailWord_5934400
  simp only [CollatzResearch.WordTrace]
  refine ⟨108222674850344894837536327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144296899800459859783381769 108222674850344894837536327)
  ·
    refine ⟨162334012275517342256304491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108222674850344894837536327 162334012275517342256304491)
    ·
      refine ⟨243501018413276013384456737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162334012275517342256304491 243501018413276013384456737)
      ·
        refine ⟨182625763809957010038342553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243501018413276013384456737 182625763809957010038342553)
        ·
          refine ⟨136969322857467757528756915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182625763809957010038342553 136969322857467757528756915)
          ·
            refine ⟨205453984286201636293135373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136969322857467757528756915 205453984286201636293135373)
            ·
              refine ⟨77045244107325613609925765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205453984286201636293135373 77045244107325613609925765)
              ·
                refine ⟨14445983270123552551861081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77045244107325613609925765 14445983270123552551861081)
                ·
                  refine ⟨10834487452592664413895811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14445983270123552551861081 10834487452592664413895811)
                  ·
                    refine ⟨16251731178888996620843717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10834487452592664413895811 16251731178888996620843717)
                    ·
                      refine ⟨3047199596041686866408197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16251731178888996620843717 3047199596041686866408197)
                      ·
                        rfl

theorem cell23_5934400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_5934400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934400 prefixEnd_5934400 := by exact prefixLift 5934400
  have htrace : WordTrace (prefixWord ++ tailWord_5934400) baseStart_5934400 baseEnd_5934400 := by
    simpa [prefixWord, tailWord_5934400, baseEnd_5934400] using wordTrace_append hprefix tailTrace_5934400
  have hstable : (prefixWord ++ tailWord_5934400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934400).length < 2 ^ (prefixWord ++ tailWord_5934400).sum := by decide
  have hdescent : baseEnd_5934400 < baseStart_5934400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934401 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 5]
def baseStart_5934401 : Nat := 118140960795 + 5934401 * 2 ^ 59
def prefixEnd_5934401 : Nat := 4983230072969 + 3 ^ 40 * 5934401 * 2
def baseEnd_5934401 : Nat := 338577789946926818055077

theorem tailTrace_5934401 : CollatzResearch.WordTrace tailWord_5934401 prefixEnd_5934401 338577789946926818055077 := by
  unfold tailWord_5934401
  simp only [CollatzResearch.WordTrace]
  refine ⟨216445386173686166845859057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144296924115790777897239371 216445386173686166845859057)
  ·
    refine ⟨162334039630264625134394293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216445386173686166845859057 162334039630264625134394293)
    ·
      refine ⟨15218816215337308606349465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162334039630264625134394293 15218816215337308606349465)
      ·
        refine ⟨11414112161502981454762099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15218816215337308606349465 11414112161502981454762099)
        ·
          refine ⟨17121168242254472182143149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11414112161502981454762099 17121168242254472182143149)
          ·
            refine ⟨6420438090845427068303681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17121168242254472182143149 6420438090845427068303681)
            ·
              refine ⟨4815328568134070301227761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420438090845427068303681 4815328568134070301227761)
              ·
                refine ⟨3611496426100552725920821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4815328568134070301227761 3611496426100552725920821)
                ·
                  refine ⟨338577789946926818055077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611496426100552725920821 338577789946926818055077)
                  ·
                    rfl

theorem cell23_5934401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 5].length) (baseStart_5934401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934401 prefixEnd_5934401 := by exact prefixLift 5934401
  have htrace : WordTrace (prefixWord ++ tailWord_5934401) baseStart_5934401 baseEnd_5934401 := by
    simpa [prefixWord, tailWord_5934401, baseEnd_5934401] using wordTrace_append hprefix tailTrace_5934401
  have hstable : (prefixWord ++ tailWord_5934401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934401).length < 2 ^ (prefixWord ++ tailWord_5934401).sum := by decide
  have hdescent : baseEnd_5934401 < baseStart_5934401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934403 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_5934403 : Nat := 118140960795 + 5934403 * 2 ^ 59
def prefixEnd_5934403 : Nat := 4983230072969 + 3 ^ 40 * 5934403 * 2
def baseEnd_5934403 : Nat := 3047201136483650354670683

theorem tailTrace_5934403 : CollatzResearch.WordTrace tailWord_5934403 prefixEnd_5934403 3047201136483650354670683 := by
  unfold tailWord_5934403
  simp only [CollatzResearch.WordTrace]
  refine ⟨216445459119678921187431863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144296972746452614124954575 216445459119678921187431863)
  ·
    refine ⟨324668188679518381781147795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216445459119678921187431863 324668188679518381781147795)
    ·
      refine ⟨487002283019277572671721693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324668188679518381781147795 487002283019277572671721693)
      ·
        refine ⟨182625856132229089751895635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487002283019277572671721693 182625856132229089751895635)
        ·
          refine ⟨273938784198343634627843453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182625856132229089751895635 273938784198343634627843453)
          ·
            refine ⟨102727044074378862985441295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273938784198343634627843453 102727044074378862985441295)
            ·
              refine ⟨154090566111568294478161943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102727044074378862985441295 154090566111568294478161943)
              ·
                refine ⟨231135849167352441717242915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154090566111568294478161943 231135849167352441717242915)
                ·
                  refine ⟨346703773751028662575864373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231135849167352441717242915 346703773751028662575864373)
                  ·
                    refine ⟨32503478789158937116487285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 346703773751028662575864373 32503478789158937116487285)
                    ·
                      refine ⟨3047201136483650354670683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32503478789158937116487285 3047201136483650354670683)
                      ·
                        rfl

theorem cell23_5934403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_5934403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934403 prefixEnd_5934403 := by exact prefixLift 5934403
  have htrace : WordTrace (prefixWord ++ tailWord_5934403) baseStart_5934403 baseEnd_5934403 := by
    simpa [prefixWord, tailWord_5934403, baseEnd_5934403] using wordTrace_append hprefix tailTrace_5934403
  have hstable : (prefixWord ++ tailWord_5934403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934403).length < 2 ^ (prefixWord ++ tailWord_5934403).sum := by decide
  have hdescent : baseEnd_5934403 < baseStart_5934403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934404 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5934404 : Nat := 118140960795 + 5934404 * 2 ^ 59
def prefixEnd_5934404 : Nat := 4983230072969 + 3 ^ 40 * 5934404 * 2
def baseEnd_5934404 : Nat := 3047201649964304850758179

theorem tailTrace_5934404 : CollatzResearch.WordTrace tailWord_5934404 prefixEnd_5934404 3047201649964304850758179 := by
  unfold tailWord_5934404
  simp only [CollatzResearch.WordTrace]
  refine ⟨108222747796337649179109133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144296997061783532238812177 108222747796337649179109133)
  ·
    refine ⟨40583530423626618442165925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108222747796337649179109133 40583530423626618442165925)
    ·
      refine ⟨7609411954429990957906111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40583530423626618442165925 7609411954429990957906111)
      ·
        refine ⟨11414117931644986436859167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609411954429990957906111 11414117931644986436859167)
        ·
          refine ⟨17121176897467479655288751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11414117931644986436859167 17121176897467479655288751)
          ·
            refine ⟨25681765346201219482933127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17121176897467479655288751 25681765346201219482933127)
            ·
              refine ⟨38522648019301829224399691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25681765346201219482933127 38522648019301829224399691)
              ·
                refine ⟨57783972028952743836599537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38522648019301829224399691 57783972028952743836599537)
                ·
                  refine ⟨43337979021714557877449653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57783972028952743836599537 43337979021714557877449653)
                  ·
                    refine ⟨4062935533285739801010905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43337979021714557877449653 4062935533285739801010905)
                    ·
                      refine ⟨3047201649964304850758179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062935533285739801010905 3047201649964304850758179)
                      ·
                        rfl

theorem cell23_5934404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5934404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934404 prefixEnd_5934404 := by exact prefixLift 5934404
  have htrace : WordTrace (prefixWord ++ tailWord_5934404) baseStart_5934404 baseEnd_5934404 := by
    simpa [prefixWord, tailWord_5934404, baseEnd_5934404] using wordTrace_append hprefix tailTrace_5934404
  have hstable : (prefixWord ++ tailWord_5934404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934404).length < 2 ^ (prefixWord ++ tailWord_5934404).sum := by decide
  have hdescent : baseEnd_5934404 < baseStart_5934404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934410 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_5934410 : Nat := 118140960795 + 5934410 * 2 ^ 59
def prefixEnd_5934410 : Nat := 4983230072969 + 3 ^ 40 * 5934410 * 2
def baseEnd_5934410 : Nat := 1015734910282743942427717

theorem tailTrace_5934410 : CollatzResearch.WordTrace tailWord_5934410 prefixEnd_5934410 1015734910282743942427717 := by
  unfold tailWord_5934410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111428607663390345734171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144297142953769040921957789 54111428607663390345734171)
  ·
    refine ⟨81167142911495085518601257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54111428607663390345734171 81167142911495085518601257)
    ·
      refine ⟨60875357183621314138950943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81167142911495085518601257 60875357183621314138950943)
      ·
        refine ⟨91313035775431971208426415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60875357183621314138950943 91313035775431971208426415)
        ·
          refine ⟨136969553663147956812639623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91313035775431971208426415 136969553663147956812639623)
          ·
            refine ⟨205454330494721935218959435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136969553663147956812639623 205454330494721935218959435)
            ·
              refine ⟨308181495742082902828439153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205454330494721935218959435 308181495742082902828439153)
              ·
                refine ⟨231136121806562177121329365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308181495742082902828439153 231136121806562177121329365)
                ·
                  refine ⟨5417252854841301026281157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 231136121806562177121329365 5417252854841301026281157)
                  ·
                    refine ⟨1015734910282743942427717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5417252854841301026281157 1015734910282743942427717)
                    ·
                      rfl

theorem cell23_5934410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_5934410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934410 prefixEnd_5934410 := by exact prefixLift 5934410
  have htrace : WordTrace (prefixWord ++ tailWord_5934410) baseStart_5934410 baseEnd_5934410 := by
    simpa [prefixWord, tailWord_5934410, baseEnd_5934410] using wordTrace_append hprefix tailTrace_5934410
  have hstable : (prefixWord ++ tailWord_5934410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934410).length < 2 ^ (prefixWord ++ tailWord_5934410).sum := by decide
  have hdescent : baseEnd_5934410 < baseStart_5934410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934417 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_5934417 : Nat := 118140960795 + 5934417 * 2 ^ 59
def prefixEnd_5934417 : Nat := 4983230072969 + 3 ^ 40 * 5934417 * 2
def baseEnd_5934417 : Nat := 3047208325212813299895619

theorem tailTrace_5934417 : CollatzResearch.WordTrace tailWord_5934417 prefixEnd_5934417 3047208325212813299895619 := by
  unfold tailWord_5934417
  simp only [CollatzResearch.WordTrace]
  refine ⟨216445969741628201578441505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144297313161085467718961003 216445969741628201578441505)
  ·
    refine ⟨162334477306221151183831129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216445969741628201578441505 162334477306221151183831129)
    ·
      refine ⟨121750857979665863387873347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162334477306221151183831129 121750857979665863387873347)
      ·
        refine ⟨182626286969498795081810021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121750857979665863387873347 182626286969498795081810021)
        ·
          refine ⟨34242428806781024077839379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182626286969498795081810021 34242428806781024077839379)
          ·
            refine ⟨51363643210171536116759069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34242428806781024077839379 51363643210171536116759069)
            ·
              refine ⟨19261366203814326043784651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51363643210171536116759069 19261366203814326043784651)
              ·
                refine ⟨28892049305721489065676977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19261366203814326043784651 28892049305721489065676977)
                ·
                  refine ⟨21669036979291116799257733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28892049305721489065676977 21669036979291116799257733)
                  ·
                    refine ⟨4062944433617084399860825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21669036979291116799257733 4062944433617084399860825)
                    ·
                      refine ⟨3047208325212813299895619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062944433617084399860825 3047208325212813299895619)
                      ·
                        rfl

theorem cell23_5934417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_5934417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934417 prefixEnd_5934417 := by exact prefixLift 5934417
  have htrace : WordTrace (prefixWord ++ tailWord_5934417) baseStart_5934417 baseEnd_5934417 := by
    simpa [prefixWord, tailWord_5934417, baseEnd_5934417] using wordTrace_append hprefix tailTrace_5934417
  have hstable : (prefixWord ++ tailWord_5934417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934417).length < 2 ^ (prefixWord ++ tailWord_5934417).sum := by decide
  have hdescent : baseEnd_5934417 < baseStart_5934417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934443 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_5934443 : Nat := 118140960795 + 5934443 * 2 ^ 59
def prefixEnd_5934443 : Nat := 4983230072969 + 3 ^ 40 * 5934443 * 2
def baseEnd_5934443 : Nat := 3047221675709830198170499

theorem tailTrace_5934443 : CollatzResearch.WordTrace tailWord_5934443 prefixEnd_5934443 3047221675709830198170499 := by
  unfold tailWord_5934443
  simp only [CollatzResearch.WordTrace]
  refine ⟨216446918039534008018887983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144297945359689338679258655 216446918039534008018887983)
  ·
    refine ⟨324670377059301012028331975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216446918039534008018887983 324670377059301012028331975)
    ·
      refine ⟨487005565588951518042497963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324670377059301012028331975 487005565588951518042497963)
      ·
        refine ⟨730508348383427277063746945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487005565588951518042497963 730508348383427277063746945)
        ·
          refine ⟨547881261287570457797810209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730508348383427277063746945 547881261287570457797810209)
          ·
            refine ⟨410910945965677843348357657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547881261287570457797810209 410910945965677843348357657)
            ·
              refine ⟨308183209474258382511268243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410910945965677843348357657 308183209474258382511268243)
              ·
                refine ⟨462274814211387573766902365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308183209474258382511268243 462274814211387573766902365)
                ·
                  refine ⟨173353055329270340162588387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462274814211387573766902365 173353055329270340162588387)
                  ·
                    refine ⟨260029582993905510243882581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173353055329270340162588387 260029582993905510243882581)
                    ·
                      refine ⟨3047221675709830198170499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260029582993905510243882581 3047221675709830198170499)
                      ·
                        rfl

theorem cell23_5934443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_5934443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934443 prefixEnd_5934443 := by exact prefixLift 5934443
  have htrace : WordTrace (prefixWord ++ tailWord_5934443) baseStart_5934443 baseEnd_5934443 := by
    simpa [prefixWord, tailWord_5934443, baseEnd_5934443] using wordTrace_append hprefix tailTrace_5934443
  have hstable : (prefixWord ++ tailWord_5934443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934443).length < 2 ^ (prefixWord ++ tailWord_5934443).sum := by decide
  have hdescent : baseEnd_5934443 < baseStart_5934443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934444 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_5934444 : Nat := 118140960795 + 5934444 * 2 ^ 59
def prefixEnd_5934444 : Nat := 4983230072969 + 3 ^ 40 * 5934444 * 2
def baseEnd_5934444 : Nat := 1015740729730161564752665

theorem tailTrace_5934444 : CollatzResearch.WordTrace tailWord_5934444 prefixEnd_5934444 1015740729730161564752665 := by
  unfold tailWord_5934444
  simp only [CollatzResearch.WordTrace]
  refine ⟨108223477256265192594837193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144297969675020256793116257 108223477256265192594837193)
  ·
    refine ⟨81167607942198894446127895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108223477256265192594837193 81167607942198894446127895)
    ·
      refine ⟨121751411913298341669191843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81167607942198894446127895 121751411913298341669191843)
      ·
        refine ⟨182627117869947512503787765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121751411913298341669191843 182627117869947512503787765)
        ·
          refine ⟨17121292300307579297230103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182627117869947512503787765 17121292300307579297230103)
          ·
            refine ⟨25681938450461368945845155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17121292300307579297230103 25681938450461368945845155)
            ·
              refine ⟨38522907675692053418767733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25681938450461368945845155 38522907675692053418767733)
              ·
                refine ⟨3611522594596130008009475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38522907675692053418767733 3611522594596130008009475)
                ·
                  refine ⟨5417283891894195012014213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611522594596130008009475 5417283891894195012014213)
                  ·
                    refine ⟨1015740729730161564752665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5417283891894195012014213 1015740729730161564752665)
                    ·
                      rfl

theorem cell23_5934444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_5934444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934444 prefixEnd_5934444 := by exact prefixLift 5934444
  have htrace : WordTrace (prefixWord ++ tailWord_5934444) baseStart_5934444 baseEnd_5934444 := by
    simpa [prefixWord, tailWord_5934444, baseEnd_5934444] using wordTrace_append hprefix tailTrace_5934444
  have hstable : (prefixWord ++ tailWord_5934444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934444).length < 2 ^ (prefixWord ++ tailWord_5934444).sum := by decide
  have hdescent : baseEnd_5934444 < baseStart_5934444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934500 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5934500 : Nat := 118140960795 + 5934500 * 2 ^ 59
def prefixEnd_5934500 : Nat := 4983230072969 + 3 ^ 40 * 5934500 * 2
def baseEnd_5934500 : Nat := 1015750314702378825052579

theorem tailTrace_5934500 : CollatzResearch.WordTrace tailWord_5934500 prefixEnd_5934500 1015750314702378825052579 := by
  unfold tailWord_5934500
  simp only [CollatzResearch.WordTrace]
  refine ⟨108224498500163753376856477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144299331333551671169141969 108224498500163753376856477)
  ·
    refine ⟨40584186937561407516321179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108224498500163753376856477 40584186937561407516321179)
    ·
      refine ⟨60876280406342111274481769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40584186937561407516321179 60876280406342111274481769)
      ·
        refine ⟨45657210304756583455861327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60876280406342111274481769 45657210304756583455861327)
        ·
          refine ⟨68485815457134875183791991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45657210304756583455861327 68485815457134875183791991)
          ·
            refine ⟨102728723185702312775687987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68485815457134875183791991 102728723185702312775687987)
            ·
              refine ⟨154093084778553469163531981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102728723185702312775687987 154093084778553469163531981)
              ·
                refine ⟨57784906791957550936324493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154093084778553469163531981 57784906791957550936324493)
                ·
                  refine ⟨21669340046984081601121685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57784906791957550936324493 21669340046984081601121685)
                  ·
                    refine ⟨1015750314702378825052579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21669340046984081601121685 1015750314702378825052579)
                    ·
                      rfl

theorem cell23_5934500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5934500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934500 prefixEnd_5934500 := by exact prefixLift 5934500
  have htrace : WordTrace (prefixWord ++ tailWord_5934500) baseStart_5934500 baseEnd_5934500 := by
    simpa [prefixWord, tailWord_5934500, baseEnd_5934500] using wordTrace_append hprefix tailTrace_5934500
  have hstable : (prefixWord ++ tailWord_5934500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934500).length < 2 ^ (prefixWord ++ tailWord_5934500).sum := by decide
  have hdescent : baseEnd_5934500 < baseStart_5934500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934520 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_5934520 : Nat := 118140960795 + 5934520 * 2 ^ 59
def prefixEnd_5934520 : Nat := 4983230072969 + 3 ^ 40 * 5934520 * 2
def baseEnd_5934520 : Nat := 3047261213720226396907645

theorem tailTrace_5934520 : CollatzResearch.WordTrace tailWord_5934520 prefixEnd_5934520 3047261213720226396907645 := by
  unfold tailWord_5934520
  simp only [CollatzResearch.WordTrace]
  refine ⟨108224863230127525084720507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144299817640170033446294009 108224863230127525084720507)
  ·
    refine ⟨162337294845191287627080761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108224863230127525084720507 162337294845191287627080761)
    ·
      refine ⟨121752971133893465720310571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162337294845191287627080761 121752971133893465720310571)
      ·
        refine ⟨182629456700840198580465857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121752971133893465720310571 182629456700840198580465857)
        ·
          refine ⟨136972092525630148935349393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182629456700840198580465857 136972092525630148935349393)
          ·
            refine ⟨102729069394222611701512045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136972092525630148935349393 102729069394222611701512045)
            ·
              refine ⟨38523401022833479388067017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102729069394222611701512045 38523401022833479388067017)
              ·
                refine ⟨28892550767125109541050263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38523401022833479388067017 28892550767125109541050263)
                ·
                  refine ⟨43338826150687664311575395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28892550767125109541050263 43338826150687664311575395)
                  ·
                    refine ⟨65008239226031496467363093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43338826150687664311575395 65008239226031496467363093)
                    ·
                      refine ⟨3047261213720226396907645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65008239226031496467363093 3047261213720226396907645)
                      ·
                        rfl

theorem cell23_5934520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_5934520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934520 prefixEnd_5934520 := by exact prefixLift 5934520
  have htrace : WordTrace (prefixWord ++ tailWord_5934520) baseStart_5934520 baseEnd_5934520 := by
    simpa [prefixWord, tailWord_5934520, baseEnd_5934520] using wordTrace_append hprefix tailTrace_5934520
  have hstable : (prefixWord ++ tailWord_5934520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934520).length < 2 ^ (prefixWord ++ tailWord_5934520).sum := by decide
  have hdescent : baseEnd_5934520 < baseStart_5934520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934561 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_5934561 : Nat := 118140960795 + 5934561 * 2 ^ 59
def prefixEnd_5934561 : Nat := 4983230072969 + 3 ^ 40 * 5934561 * 2
def baseEnd_5934561 : Nat := 3047282266427060736494957

theorem tailTrace_5934561 : CollatzResearch.WordTrace tailWord_5934561 prefixEnd_5934561 3047282266427060736494957 := by
  unfold tailWord_5934561
  simp only [CollatzResearch.WordTrace]
  refine ⟨216451221853106514171683537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144300814568737676114455691 216451221853106514171683537)
  ·
    refine ⟨162338416389829885628762653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216451221853106514171683537 162338416389829885628762653)
    ·
      refine ⟨60876906146186207110785995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162338416389829885628762653 60876906146186207110785995)
      ·
        refine ⟨91315359219279310666178993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60876906146186207110785995 91315359219279310666178993)
        ·
          refine ⟨68486519414459482999634245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91315359219279310666178993 68486519414459482999634245)
          ·
            refine ⟨12841222390211153062431421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68486519414459482999634245 12841222390211153062431421)
            ·
              refine ⟨4815458396329182398411783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12841222390211153062431421 4815458396329182398411783)
              ·
                refine ⟨7223187594493773597617675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815458396329182398411783 7223187594493773597617675)
                ·
                  refine ⟨10834781391740660396426513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7223187594493773597617675 10834781391740660396426513)
                  ·
                    refine ⟨8126086043805495297319885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10834781391740660396426513 8126086043805495297319885)
                    ·
                      refine ⟨3047282266427060736494957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8126086043805495297319885 3047282266427060736494957)
                      ·
                        rfl

theorem cell23_5934561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_5934561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934561 prefixEnd_5934561 := by exact prefixLift 5934561
  have htrace : WordTrace (prefixWord ++ tailWord_5934561) baseStart_5934561 baseEnd_5934561 := by
    simpa [prefixWord, tailWord_5934561, baseEnd_5934561] using wordTrace_append hprefix tailTrace_5934561
  have hstable : (prefixWord ++ tailWord_5934561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934561).length < 2 ^ (prefixWord ++ tailWord_5934561).sum := by decide
  have hdescent : baseEnd_5934561 < baseStart_5934561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934584 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_5934584 : Nat := 118140960795 + 5934584 * 2 ^ 59
def prefixEnd_5934584 : Nat := 4983230072969 + 3 ^ 40 * 5934584 * 2
def baseEnd_5934584 : Nat := 3047294076482114146507351

theorem tailTrace_5934584 : CollatzResearch.WordTrace tailWord_5934584 prefixEnd_5934584 3047294076482114146507351 := by
  unfold tailWord_5934584
  simp only [CollatzResearch.WordTrace]
  refine ⟨108226030366011594549885403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144301373821348792733180537 108226030366011594549885403)
  ·
    refine ⟨162339045549017391824828105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108226030366011594549885403 162339045549017391824828105)
    ·
      refine ⟨121754284161763043868621079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162339045549017391824828105 121754284161763043868621079)
      ·
        refine ⟨182631426242644565802931619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121754284161763043868621079 182631426242644565802931619)
        ·
          refine ⟨273947139363966848704397429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182631426242644565802931619 273947139363966848704397429)
          ·
            refine ⟨25682544315371892066037259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273947139363966848704397429 25682544315371892066037259)
            ·
              refine ⟨38523816473057838099055889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25682544315371892066037259 38523816473057838099055889)
              ·
                refine ⟨28892862354793378574291917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38523816473057838099055889 28892862354793378574291917)
                ·
                  refine ⟨10834823383047516965359469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28892862354793378574291917 10834823383047516965359469)
                  ·
                    refine ⟨4063058768642818862009801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10834823383047516965359469 4063058768642818862009801)
                    ·
                      refine ⟨3047294076482114146507351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063058768642818862009801 3047294076482114146507351)
                      ·
                        rfl

theorem cell23_5934584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_5934584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934584 prefixEnd_5934584 := by exact prefixLift 5934584
  have htrace : WordTrace (prefixWord ++ tailWord_5934584) baseStart_5934584 baseEnd_5934584 := by
    simpa [prefixWord, tailWord_5934584, baseEnd_5934584] using wordTrace_append hprefix tailTrace_5934584
  have hstable : (prefixWord ++ tailWord_5934584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934584).length < 2 ^ (prefixWord ++ tailWord_5934584).sum := by decide
  have hdescent : baseEnd_5934584 < baseStart_5934584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934612 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5934612 : Nat := 118140960795 + 5934612 * 2 ^ 59
def prefixEnd_5934612 : Nat := 4983230072969 + 3 ^ 40 * 5934612 * 2
def baseEnd_5934612 : Nat := 3047308453940440036957223

theorem tailTrace_5934612 : CollatzResearch.WordTrace tailWord_5934612 prefixEnd_5934612 3047308453940440036957223 := by
  unfold tailWord_5934612
  simp only [CollatzResearch.WordTrace]
  refine ⟨108226540987960874940895045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144302054650614499921193393 108226540987960874940895045)
  ·
    refine ⟨20292476435242664051417821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108226540987960874940895045 20292476435242664051417821)
    ·
      refine ⟨7609678663215999019281683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20292476435242664051417821 7609678663215999019281683)
      ·
        refine ⟨11414517994823998528922525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609678663215999019281683 11414517994823998528922525)
        ·
          refine ⟨4280444248058999448345947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11414517994823998528922525 4280444248058999448345947)
          ·
            refine ⟨6420666372088499172518921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280444248058999448345947 6420666372088499172518921)
            ·
              refine ⟨4815499779066374379389191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420666372088499172518921 4815499779066374379389191)
              ·
                refine ⟨7223249668599561569083787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815499779066374379389191 7223249668599561569083787)
                ·
                  refine ⟨10834874502899342353625681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7223249668599561569083787 10834874502899342353625681)
                  ·
                    refine ⟨8126155877174506765219261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10834874502899342353625681 8126155877174506765219261)
                    ·
                      refine ⟨3047308453940440036957223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8126155877174506765219261 3047308453940440036957223)
                      ·
                        rfl

theorem cell23_5934612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5934612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934612 prefixEnd_5934612 := by exact prefixLift 5934612
  have htrace : WordTrace (prefixWord ++ tailWord_5934612) baseStart_5934612 baseEnd_5934612 := by
    simpa [prefixWord, tailWord_5934612, baseEnd_5934612] using wordTrace_append hprefix tailTrace_5934612
  have hstable : (prefixWord ++ tailWord_5934612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934612).length < 2 ^ (prefixWord ++ tailWord_5934612).sum := by decide
  have hdescent : baseEnd_5934612 < baseStart_5934612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934667 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 2, 5]
def baseStart_5934667 : Nat := 118140960795 + 5934667 * 2 ^ 59
def prefixEnd_5934667 : Nat := 4983230072969 + 3 ^ 40 * 5934667 * 2
def baseEnd_5934667 : Nat := 1015778898458812440589823

theorem tailTrace_5934667 : CollatzResearch.WordTrace tailWord_5934667 prefixEnd_5934667 1015778898458812440589823 := by
  unfold tailWord_5934667
  simp only [CollatzResearch.WordTrace]
  refine ⟨216455087990722494275042255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144303391993814996183361503 216455087990722494275042255)
  ·
    refine ⟨324682631986083741412563383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216455087990722494275042255 324682631986083741412563383)
    ·
      refine ⟨487023947979125612118845075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324682631986083741412563383 487023947979125612118845075)
      ·
        refine ⟨730535921968688418178267613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487023947979125612118845075 730535921968688418178267613)
        ·
          refine ⟨273950970738258156816850355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730535921968688418178267613 273950970738258156816850355)
          ·
            refine ⟨410926456107387235225275533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273950970738258156816850355 410926456107387235225275533)
            ·
              refine ⟨154097421040270213209478325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410926456107387235225275533 154097421040270213209478325)
              ·
                refine ⟨14446633222525332488388593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154097421040270213209478325 14446633222525332488388593)
                ·
                  refine ⟨10834974916893999366291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14446633222525332488388593 10834974916893999366291445)
                  ·
                    refine ⟨1015778898458812440589823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10834974916893999366291445 1015778898458812440589823)
                    ·
                      rfl

theorem cell23_5934667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 5].length) (baseStart_5934667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934667 prefixEnd_5934667 := by exact prefixLift 5934667
  have htrace : WordTrace (prefixWord ++ tailWord_5934667) baseStart_5934667 baseEnd_5934667 := by
    simpa [prefixWord, tailWord_5934667, baseEnd_5934667] using wordTrace_append hprefix tailTrace_5934667
  have hstable : (prefixWord ++ tailWord_5934667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934667).length < 2 ^ (prefixWord ++ tailWord_5934667).sum := by decide
  have hdescent : baseEnd_5934667 < baseStart_5934667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934677 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5934677 : Nat := 118140960795 + 5934677 * 2 ^ 59
def prefixEnd_5934677 : Nat := 4983230072969 + 3 ^ 40 * 5934677 * 2
def baseEnd_5934677 : Nat := 3047341830182982282644423

theorem tailTrace_5934677 : CollatzResearch.WordTrace tailWord_5934677 prefixEnd_5934677 3047341830182982282644423 := by
  unfold tailWord_5934677
  simp only [CollatzResearch.WordTrace]
  refine ⟨216455452720686265982906285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144303635147124177321937523 216455452720686265982906285)
  ·
    refine ⟨81170794770257349743589857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216455452720686265982906285 81170794770257349743589857)
    ·
      refine ⟨60878096077693012307692393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81170794770257349743589857 60878096077693012307692393)
      ·
        refine ⟨45658572058269759230769295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60878096077693012307692393 45658572058269759230769295)
        ·
          refine ⟨68487858087404638846153943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45658572058269759230769295 68487858087404638846153943)
          ·
            refine ⟨102731787131106958269230915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68487858087404638846153943 102731787131106958269230915)
            ·
              refine ⟨154097680696660437403846373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102731787131106958269230915 154097680696660437403846373)
              ·
                refine ⟨28893315130623832013221195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154097680696660437403846373 28893315130623832013221195)
                ·
                  refine ⟨43339972695935748019831793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28893315130623832013221195 43339972695935748019831793)
                  ·
                    refine ⟨32504979521951811014873845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43339972695935748019831793 32504979521951811014873845)
                    ·
                      refine ⟨3047341830182982282644423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32504979521951811014873845 3047341830182982282644423)
                      ·
                        rfl

theorem cell23_5934677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5934677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934677 prefixEnd_5934677 := by exact prefixLift 5934677
  have htrace : WordTrace (prefixWord ++ tailWord_5934677) baseStart_5934677 baseEnd_5934677 := by
    simpa [prefixWord, tailWord_5934677, baseEnd_5934677] using wordTrace_append hprefix tailTrace_5934677
  have hstable : (prefixWord ++ tailWord_5934677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934677).length < 2 ^ (prefixWord ++ tailWord_5934677).sum := by decide
  have hdescent : baseEnd_5934677 < baseStart_5934677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934684 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5934684 : Nat := 118140960795 + 5934684 * 2 ^ 59
def prefixEnd_5934684 : Nat := 4983230072969 + 3 ^ 40 * 5934684 * 2
def baseEnd_5934684 : Nat := 1015781808182521251752297

theorem tailTrace_5934684 : CollatzResearch.WordTrace tailWord_5934684 prefixEnd_5934684 1015781808182521251752297 := by
  unfold tailWord_5934684
  simp only [CollatzResearch.WordTrace]
  refine ⟨108227854015830453089205553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144303805354440604118940737 108227854015830453089205553)
  ·
    refine ⟨81170890511872839816904165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108227854015830453089205553 81170890511872839816904165)
    ·
      refine ⟨15219541970976157465669531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81170890511872839816904165 15219541970976157465669531)
      ·
        refine ⟨22829312956464236198504297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15219541970976157465669531 22829312956464236198504297)
        ·
          refine ⟨17121984717348177148878223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22829312956464236198504297 17121984717348177148878223)
          ·
            refine ⟨25682977076022265723317335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17121984717348177148878223 25682977076022265723317335)
            ·
              refine ⟨38524465614033398584976003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25682977076022265723317335 38524465614033398584976003)
              ·
                refine ⟨57786698421050097877464005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38524465614033398584976003 57786698421050097877464005)
                ·
                  refine ⟨10835005953946893352024501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57786698421050097877464005 10835005953946893352024501)
                  ·
                    refine ⟨1015781808182521251752297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10835005953946893352024501 1015781808182521251752297)
                    ·
                      rfl

theorem cell23_5934684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5934684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934684 prefixEnd_5934684 := by exact prefixLift 5934684
  have htrace : WordTrace (prefixWord ++ tailWord_5934684) baseStart_5934684 baseEnd_5934684 := by
    simpa [prefixWord, tailWord_5934684, baseEnd_5934684] using wordTrace_append hprefix tailTrace_5934684
  have hstable : (prefixWord ++ tailWord_5934684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934684).length < 2 ^ (prefixWord ++ tailWord_5934684).sum := by decide
  have hdescent : baseEnd_5934684 < baseStart_5934684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934721 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5934721 : Nat := 118140960795 + 5934721 * 2 ^ 59
def prefixEnd_5934721 : Nat := 4983230072969 + 3 ^ 40 * 5934721 * 2
def baseEnd_5934721 : Nat := 3047364423331780110494221

theorem tailTrace_5934721 : CollatzResearch.WordTrace tailWord_5934721 prefixEnd_5934721 3047364423331780110494221 := by
  unfold tailWord_5934721
  simp only [CollatzResearch.WordTrace]
  refine ⟨216457057532526861497508017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144304705021684574331672011 216457057532526861497508017)
  ·
    refine ⟨162342793149395146123131013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216457057532526861497508017 162342793149395146123131013)
    ·
      refine ⟨30439273715511589898087065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162342793149395146123131013 30439273715511589898087065)
      ·
        refine ⟨22829455286633692423565299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30439273715511589898087065 22829455286633692423565299)
        ·
          refine ⟨34244182929950538635347949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22829455286633692423565299 34244182929950538635347949)
          ·
            refine ⟨12841568598731451988255481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34244182929950538635347949 12841568598731451988255481)
            ·
              refine ⟨9631176449048588991191611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12841568598731451988255481 9631176449048588991191611)
              ·
                refine ⟨14446764673572883486787417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9631176449048588991191611 14446764673572883486787417)
                ·
                  refine ⟨10835073505179662615090563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14446764673572883486787417 10835073505179662615090563)
                  ·
                    refine ⟨16252610257769493922635845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10835073505179662615090563 16252610257769493922635845)
                    ·
                      refine ⟨3047364423331780110494221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16252610257769493922635845 3047364423331780110494221)
                      ·
                        rfl

theorem cell23_5934721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5934721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934721 prefixEnd_5934721 := by exact prefixLift 5934721
  have htrace : WordTrace (prefixWord ++ tailWord_5934721) baseStart_5934721 baseEnd_5934721 := by
    simpa [prefixWord, tailWord_5934721, baseEnd_5934721] using wordTrace_append hprefix tailTrace_5934721
  have hstable : (prefixWord ++ tailWord_5934721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934721).length < 2 ^ (prefixWord ++ tailWord_5934721).sum := by decide
  have hdescent : baseEnd_5934721 < baseStart_5934721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934731 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 1, 4]
def baseStart_5934731 : Nat := 118140960795 + 5934731 * 2 ^ 59
def prefixEnd_5934731 : Nat := 4983230072969 + 3 ^ 40 * 5934731 * 2
def baseEnd_5934731 : Nat := 1015789852712775023789725

theorem tailTrace_5934731 : CollatzResearch.WordTrace tailWord_5934731 prefixEnd_5934731 1015789852712775023789725 := by
  unfold tailWord_5934731
  simp only [CollatzResearch.WordTrace]
  refine ⟨216457422262490633205372047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144304948174993755470248031 216457422262490633205372047)
  ·
    refine ⟨324686133393735949808058071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216457422262490633205372047 324686133393735949808058071)
    ·
      refine ⟨487029200090603924712087107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324686133393735949808058071 487029200090603924712087107)
      ·
        refine ⟨730543800135905887068130661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487029200090603924712087107 730543800135905887068130661)
        ·
          refine ⟨136976962525482353825274499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 730543800135905887068130661 136976962525482353825274499)
          ·
            refine ⟨205465443788223530737911749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136976962525482353825274499 205465443788223530737911749)
            ·
              refine ⟨38524770710291912013358453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205465443788223530737911749 38524770710291912013358453)
              ·
                refine ⟨3611697254089866751252355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38524770710291912013358453 3611697254089866751252355)
                ·
                  refine ⟨5417545881134800126878533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611697254089866751252355 5417545881134800126878533)
                  ·
                    refine ⟨1015789852712775023789725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5417545881134800126878533 1015789852712775023789725)
                    ·
                      rfl

theorem cell23_5934731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 4].length) (baseStart_5934731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934731 prefixEnd_5934731 := by exact prefixLift 5934731
  have htrace : WordTrace (prefixWord ++ tailWord_5934731) baseStart_5934731 baseEnd_5934731 := by
    simpa [prefixWord, tailWord_5934731, baseEnd_5934731] using wordTrace_append hprefix tailTrace_5934731
  have hstable : (prefixWord ++ tailWord_5934731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934731).length < 2 ^ (prefixWord ++ tailWord_5934731).sum := by decide
  have hdescent : baseEnd_5934731 < baseStart_5934731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934744 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 6]
def baseStart_5934744 : Nat := 118140960795 + 5934744 * 2 ^ 59
def prefixEnd_5934744 : Nat := 4983230072969 + 3 ^ 40 * 5934744 * 2
def baseEnd_5934744 : Nat := 338597359265203724500735

theorem tailTrace_5934744 : CollatzResearch.WordTrace tailWord_5934744 prefixEnd_5934744 338597359265203724500735 := by
  unfold tailWord_5934744
  simp only [CollatzResearch.WordTrace]
  refine ⟨108228948205721768212797643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144305264274295690950396857 108228948205721768212797643)
  ·
    refine ⟨162343422308582652319196465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108228948205721768212797643 162343422308582652319196465)
    ·
      refine ⟨121757566731436989239397349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162343422308582652319196465 121757566731436989239397349)
      ·
        refine ⟨22829543762144435482387003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121757566731436989239397349 22829543762144435482387003)
        ·
          refine ⟨34244315643216653223580505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22829543762144435482387003 34244315643216653223580505)
          ·
            refine ⟨25683236732412489917685379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34244315643216653223580505 25683236732412489917685379)
            ·
              refine ⟨38524855098618734876528069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25683236732412489917685379 38524855098618734876528069)
              ·
                refine ⟨7223410330991012789349013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38524855098618734876528069 7223410330991012789349013)
                ·
                  refine ⟨338597359265203724500735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7223410330991012789349013 338597359265203724500735)
                  ·
                    rfl

theorem cell23_5934744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_5934744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934744 prefixEnd_5934744 := by exact prefixLift 5934744
  have htrace : WordTrace (prefixWord ++ tailWord_5934744) baseStart_5934744 baseEnd_5934744 := by
    simpa [prefixWord, tailWord_5934744, baseEnd_5934744] using wordTrace_append hprefix tailTrace_5934744
  have hstable : (prefixWord ++ tailWord_5934744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934744).length < 2 ^ (prefixWord ++ tailWord_5934744).sum := by decide
  have hdescent : baseEnd_5934744 < baseStart_5934744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934767 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_5934767 : Nat := 118140960795 + 5934767 * 2 ^ 59
def prefixEnd_5934767 : Nat := 4983230072969 + 3 ^ 40 * 5934767 * 2
def baseEnd_5934767 : Nat := 3047388043441886930519009

theorem tailTrace_5934767 : CollatzResearch.WordTrace tailWord_5934767 prefixEnd_5934767 3047388043441886930519009 := by
  unfold tailWord_5934767
  simp only [CollatzResearch.WordTrace]
  refine ⟨216458735290360211353682555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144305823526906807569121703 216458735290360211353682555)
  ·
    refine ⟨324688102935540317030523833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216458735290360211353682555 324688102935540317030523833)
    ·
      refine ⟨243516077201655237772892875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324688102935540317030523833 243516077201655237772892875)
      ·
        refine ⟨365274115802482856659339313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243516077201655237772892875 365274115802482856659339313)
        ·
          refine ⟨273955586851862142494504485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365274115802482856659339313 273955586851862142494504485)
          ·
            refine ⟨51366672534724151717719591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273955586851862142494504485 51366672534724151717719591)
            ·
              refine ⟨77050008802086227576579387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51366672534724151717719591 77050008802086227576579387)
              ·
                refine ⟨115575013203129341364869081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77050008802086227576579387 115575013203129341364869081)
                ·
                  refine ⟨86681259902347006023651811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115575013203129341364869081 86681259902347006023651811)
                  ·
                    refine ⟨130021889853520509035477717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86681259902347006023651811 130021889853520509035477717)
                    ·
                      refine ⟨3047388043441886930519009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130021889853520509035477717 3047388043441886930519009)
                      ·
                        rfl

theorem cell23_5934767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_5934767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934767 prefixEnd_5934767 := by exact prefixLift 5934767
  have htrace : WordTrace (prefixWord ++ tailWord_5934767) baseStart_5934767 baseEnd_5934767 := by
    simpa [prefixWord, tailWord_5934767, baseEnd_5934767] using wordTrace_append hprefix tailTrace_5934767
  have hstable : (prefixWord ++ tailWord_5934767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934767).length < 2 ^ (prefixWord ++ tailWord_5934767).sum := by decide
  have hdescent : baseEnd_5934767 < baseStart_5934767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934771 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 3]
def baseStart_5934771 : Nat := 118140960795 + 5934771 * 2 ^ 59
def prefixEnd_5934771 : Nat := 4983230072969 + 3 ^ 40 * 5934771 * 2
def baseEnd_5934771 : Nat := 3047390097364504914868991

theorem tailTrace_5934771 : CollatzResearch.WordTrace tailWord_5934771 prefixEnd_5934771 3047390097364504914868991 := by
  unfold tailWord_5934771
  simp only [CollatzResearch.WordTrace]
  refine ⟨216458881182345720036828167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144305920788230480024552111 216458881182345720036828167)
  ·
    refine ⟨324688321773518580055242251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216458881182345720036828167 324688321773518580055242251)
    ·
      refine ⟨487032482660277870082863377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324688321773518580055242251 487032482660277870082863377)
      ·
        refine ⟨365274361995208402562147533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487032482660277870082863377 365274361995208402562147533)
        ·
          refine ⟨136977885748203150960805325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365274361995208402562147533 136977885748203150960805325)
          ·
            refine ⟨51366707155576181610301997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136977885748203150960805325 51366707155576181610301997)
            ·
              refine ⟨19262515183341068103863249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51366707155576181610301997 19262515183341068103863249)
              ·
                refine ⟨14446886387505801077897437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19262515183341068103863249 14446886387505801077897437)
                ·
                  refine ⟨5417582395314675404211539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14446886387505801077897437 5417582395314675404211539)
                  ·
                    refine ⟨8126373592972013106317309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5417582395314675404211539 8126373592972013106317309)
                    ·
                      refine ⟨3047390097364504914868991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8126373592972013106317309 3047390097364504914868991)
                      ·
                        rfl

theorem cell23_5934771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_5934771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934771 prefixEnd_5934771 := by exact prefixLift 5934771
  have htrace : WordTrace (prefixWord ++ tailWord_5934771) baseStart_5934771 baseEnd_5934771 := by
    simpa [prefixWord, tailWord_5934771, baseEnd_5934771] using wordTrace_append hprefix tailTrace_5934771
  have hstable : (prefixWord ++ tailWord_5934771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934771).length < 2 ^ (prefixWord ++ tailWord_5934771).sum := by decide
  have hdescent : baseEnd_5934771 < baseStart_5934771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934781 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_5934781 : Nat := 118140960795 + 5934781 * 2 ^ 59
def prefixEnd_5934781 : Nat := 4983230072969 + 3 ^ 40 * 5934781 * 2
def baseEnd_5934781 : Nat := 3047395232171049875743945

theorem tailTrace_5934781 : CollatzResearch.WordTrace tailWord_5934781 prefixEnd_5934781 3047395232171049875743945 := by
  unfold tailWord_5934781
  simp only [CollatzResearch.WordTrace]
  refine ⟨216459245912309491744692197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144306163941539661163128131 216459245912309491744692197)
  ·
    refine ⟨40586108608558029702129787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216459245912309491744692197 40586108608558029702129787)
    ·
      refine ⟨60879162912837044553194681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40586108608558029702129787 60879162912837044553194681)
      ·
        refine ⟨45659372184627783414896011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60879162912837044553194681 45659372184627783414896011)
        ·
          refine ⟨68489058276941675122344017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45659372184627783414896011 68489058276941675122344017)
          ·
            refine ⟨51366793707706256341758013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68489058276941675122344017 51366793707706256341758013)
            ·
              refine ⟨19262547640389846128159255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51366793707706256341758013 19262547640389846128159255)
              ·
                refine ⟨28893821460584769192238883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19262547640389846128159255 28893821460584769192238883)
                ·
                  refine ⟨43340732190877153788358325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28893821460584769192238883 43340732190877153788358325)
                  ·
                    refine ⟨4063193642894733167658593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43340732190877153788358325 4063193642894733167658593)
                    ·
                      refine ⟨3047395232171049875743945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063193642894733167658593 3047395232171049875743945)
                      ·
                        rfl

theorem cell23_5934781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_5934781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934781 prefixEnd_5934781 := by exact prefixLift 5934781
  have htrace : WordTrace (prefixWord ++ tailWord_5934781) baseStart_5934781 baseEnd_5934781 := by
    simpa [prefixWord, tailWord_5934781, baseEnd_5934781] using wordTrace_append hprefix tailTrace_5934781
  have hstable : (prefixWord ++ tailWord_5934781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934781).length < 2 ^ (prefixWord ++ tailWord_5934781).sum := by decide
  have hdescent : baseEnd_5934781 < baseStart_5934781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934828 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_5934828 : Nat := 118140960795 + 5934828 * 2 ^ 59
def prefixEnd_5934828 : Nat := 4983230072969 + 3 ^ 40 * 5934828 * 2
def baseEnd_5934828 : Nat := 3047419365761811191856229

theorem tailTrace_5934828 : CollatzResearch.WordTrace tailWord_5934828 prefixEnd_5934828 3047419365761811191856229 := by
  unfold tailWord_5934828
  simp only [CollatzResearch.WordTrace]
  refine ⟨108230480071569609385826569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144307306762092812514435425 108230480071569609385826569)
  ·
    refine ⟨81172860053677207039369927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108230480071569609385826569 81172860053677207039369927)
    ·
      refine ⟨121759290080515810559054891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81172860053677207039369927 121759290080515810559054891)
      ·
        refine ⟨182638935120773715838582337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121759290080515810559054891 182638935120773715838582337)
        ·
          refine ⟨136979201340580286878936753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182638935120773715838582337 136979201340580286878936753)
          ·
            refine ⟨102734401005435215159202565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136979201340580286878936753 102734401005435215159202565)
            ·
              refine ⟨19262700188519102842350481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102734401005435215159202565 19262700188519102842350481)
              ·
                refine ⟨14447025141389327131762861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19262700188519102842350481 14447025141389327131762861)
                ·
                  refine ⟨5417634428020997674411073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14447025141389327131762861 5417634428020997674411073)
                  ·
                    refine ⟨4063225821015748255808305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5417634428020997674411073 4063225821015748255808305)
                    ·
                      refine ⟨3047419365761811191856229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063225821015748255808305 3047419365761811191856229)
                      ·
                        rfl

theorem cell23_5934828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_5934828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934828 prefixEnd_5934828 := by exact prefixLift 5934828
  have htrace : WordTrace (prefixWord ++ tailWord_5934828) baseStart_5934828 baseEnd_5934828 := by
    simpa [prefixWord, tailWord_5934828, baseEnd_5934828] using wordTrace_append hprefix tailTrace_5934828
  have hstable : (prefixWord ++ tailWord_5934828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934828).length < 2 ^ (prefixWord ++ tailWord_5934828).sum := by decide
  have hdescent : baseEnd_5934828 < baseStart_5934828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934834 : List Nat := [3, 2, 1, 3, 1, 1, 3, 9]
def baseStart_5934834 : Nat := 118140960795 + 5934834 * 2 ^ 59
def prefixEnd_5934834 : Nat := 4983230072969 + 3 ^ 40 * 5934834 * 2
def baseEnd_5934834 : Nat := 112867498023916228458563

theorem tailTrace_5934834 : CollatzResearch.WordTrace tailWord_5934834 prefixEnd_5934834 112867498023916228458563 := by
  unfold tailWord_5934834
  simp only [CollatzResearch.WordTrace]
  refine ⟨54115294745279370449092889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144307452654078321197581037 54115294745279370449092889)
  ·
    refine ⟨40586471058959527836819667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54115294745279370449092889 40586471058959527836819667)
    ·
      refine ⟨60879706588439291755229501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40586471058959527836819667 60879706588439291755229501)
      ·
        refine ⟨22829889970664734408211063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60879706588439291755229501 22829889970664734408211063)
        ·
          refine ⟨34244834955997101612316595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22829889970664734408211063 34244834955997101612316595)
          ·
            refine ⟨51367252433995652418474893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34244834955997101612316595 51367252433995652418474893)
            ·
              refine ⟨19262719662748369656928085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51367252433995652418474893 19262719662748369656928085)
              ·
                refine ⟨112867498023916228458563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19262719662748369656928085 112867498023916228458563)
                ·
                  rfl

theorem cell23_5934834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_5934834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934834 prefixEnd_5934834 := by exact prefixLift 5934834
  have htrace : WordTrace (prefixWord ++ tailWord_5934834) baseStart_5934834 baseEnd_5934834 := by
    simpa [prefixWord, tailWord_5934834, baseEnd_5934834] using wordTrace_append hprefix tailTrace_5934834
  have hstable : (prefixWord ++ tailWord_5934834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934834).length < 2 ^ (prefixWord ++ tailWord_5934834).sum := by decide
  have hdescent : baseEnd_5934834 < baseStart_5934834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934845 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_5934845 : Nat := 118140960795 + 5934845 * 2 ^ 59
def prefixEnd_5934845 : Nat := 4983230072969 + 3 ^ 40 * 5934845 * 2
def baseEnd_5934845 : Nat := 3047428094932937625343651

theorem tailTrace_5934845 : CollatzResearch.WordTrace tailWord_5934845 prefixEnd_5934845 3047428094932937625343651 := by
  unfold tailWord_5934845
  simp only [CollatzResearch.WordTrace]
  refine ⟨216461580184077630675021989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144307720122718420450014659 216461580184077630675021989)
  ·
    refine ⟨40586546284514555751566623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216461580184077630675021989 40586546284514555751566623)
    ·
      refine ⟨60879819426771833627349935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40586546284514555751566623 60879819426771833627349935)
      ·
        refine ⟨91319729140157750441024903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60879819426771833627349935 91319729140157750441024903)
        ·
          refine ⟨136979593710236625661537355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91319729140157750441024903 136979593710236625661537355)
          ·
            refine ⟨205469390565354938492306033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136979593710236625661537355 205469390565354938492306033)
            ·
              refine ⟨154102042924016203869229525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205469390565354938492306033 154102042924016203869229525)
              ·
                refine ⟨3611766631031629778185067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154102042924016203869229525 3611766631031629778185067)
                ·
                  refine ⟨5417649946547444667277601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611766631031629778185067 5417649946547444667277601)
                  ·
                    refine ⟨4063237459910583500458201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5417649946547444667277601 4063237459910583500458201)
                    ·
                      refine ⟨3047428094932937625343651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063237459910583500458201 3047428094932937625343651)
                      ·
                        rfl

theorem cell23_5934845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_5934845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934845 prefixEnd_5934845 := by exact prefixLift 5934845
  have htrace : WordTrace (prefixWord ++ tailWord_5934845) baseStart_5934845 baseEnd_5934845 := by
    simpa [prefixWord, tailWord_5934845, baseEnd_5934845] using wordTrace_append hprefix tailTrace_5934845
  have hstable : (prefixWord ++ tailWord_5934845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934845).length < 2 ^ (prefixWord ++ tailWord_5934845).sum := by decide
  have hdescent : baseEnd_5934845 < baseStart_5934845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934935 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_5934935 : Nat := 118140960795 + 5934935 * 2 ^ 59
def prefixEnd_5934935 : Nat := 4983230072969 + 3 ^ 40 * 5934935 * 2
def baseEnd_5934935 : Nat := 3047474308191842273218237

theorem tailTrace_5934935 : CollatzResearch.WordTrace tailWord_5934935 prefixEnd_5934935 3047474308191842273218237 := by
  unfold tailWord_5934935
  simp only [CollatzResearch.WordTrace]
  refine ⟨216464862753751576045798259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144309908502501050697198839 216464862753751576045798259)
  ·
    refine ⟨324697294130627364068697389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216464862753751576045798259 324697294130627364068697389)
    ·
      refine ⟨121761485298985261525761521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324697294130627364068697389 121761485298985261525761521)
      ·
        refine ⟨91321113974238946144321141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121761485298985261525761521 91321113974238946144321141)
        ·
          refine ⟨8561354435084901201030107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91321113974238946144321141 8561354435084901201030107)
          ·
            refine ⟨12842031652627351801545161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8561354435084901201030107 12842031652627351801545161)
            ·
              refine ⟨9631523739470513851158871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12842031652627351801545161 9631523739470513851158871)
              ·
                refine ⟨14447285609205770776738307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9631523739470513851158871 14447285609205770776738307)
                ·
                  refine ⟨21670928413808656165107461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14447285609205770776738307 21670928413808656165107461)
                  ·
                    refine ⟨4063299077589123030957649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21670928413808656165107461 4063299077589123030957649)
                    ·
                      refine ⟨3047474308191842273218237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063299077589123030957649 3047474308191842273218237)
                      ·
                        rfl

theorem cell23_5934935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_5934935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934935 prefixEnd_5934935 := by exact prefixLift 5934935
  have htrace : WordTrace (prefixWord ++ tailWord_5934935) baseStart_5934935 baseEnd_5934935 := by
    simpa [prefixWord, tailWord_5934935, baseEnd_5934935] using wordTrace_append hprefix tailTrace_5934935
  have hstable : (prefixWord ++ tailWord_5934935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934935).length < 2 ^ (prefixWord ++ tailWord_5934935).sum := by decide
  have hdescent : baseEnd_5934935 < baseStart_5934935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5934951 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_5934951 : Nat := 118140960795 + 5934951 * 2 ^ 59
def prefixEnd_5934951 : Nat := 4983230072969 + 3 ^ 40 * 5934951 * 2
def baseEnd_5934951 : Nat := 3047482523882314210618163

theorem tailTrace_5934951 : CollatzResearch.WordTrace tailWord_5934951 prefixEnd_5934951 3047482523882314210618163 := by
  unfold tailWord_5934951
  simp only [CollatzResearch.WordTrace]
  refine ⟨216465446321693610778380707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144310297547795740518920471 216465446321693610778380707)
  ·
    refine ⟨324698169482540416167571061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216465446321693610778380707 324698169482540416167571061)
    ·
      refine ⟨30440453388988164015709787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324698169482540416167571061 30440453388988164015709787)
      ·
        refine ⟨45660680083482246023564681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30440453388988164015709787 45660680083482246023564681)
        ·
          refine ⟨34245510062611684517673511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45660680083482246023564681 34245510062611684517673511)
          ·
            refine ⟨51368265093917526776510267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34245510062611684517673511 51368265093917526776510267)
            ·
              refine ⟨77052397640876290164765401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51368265093917526776510267 77052397640876290164765401)
              ·
                refine ⟨57789298230657217623574051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77052397640876290164765401 57789298230657217623574051)
                ·
                  refine ⟨86683947345985826435361077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57789298230657217623574051 86683947345985826435361077)
                  ·
                    refine ⟨8126620063686171228315101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86683947345985826435361077 8126620063686171228315101)
                    ·
                      refine ⟨3047482523882314210618163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8126620063686171228315101 3047482523882314210618163)
                      ·
                        rfl

theorem cell23_5934951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_5934951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5934951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5934951 prefixEnd_5934951 := by exact prefixLift 5934951
  have htrace : WordTrace (prefixWord ++ tailWord_5934951) baseStart_5934951 baseEnd_5934951 := by
    simpa [prefixWord, tailWord_5934951, baseEnd_5934951] using wordTrace_append hprefix tailTrace_5934951
  have hstable : (prefixWord ++ tailWord_5934951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5934951).length < 2 ^ (prefixWord ++ tailWord_5934951).sum := by decide
  have hdescent : baseEnd_5934951 < baseStart_5934951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5934951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935031 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 6]
def baseStart_5935031 : Nat := 118140960795 + 5935031 * 2 ^ 59
def prefixEnd_5935031 : Nat := 4983230072969 + 3 ^ 40 * 5935031 * 2
def baseEnd_5935031 : Nat := 338613733592741544179755

theorem tailTrace_5935031 : CollatzResearch.WordTrace tailWord_5935031 prefixEnd_5935031 338613733592741544179755 := by
  unfold tailWord_5935031
  simp only [CollatzResearch.WordTrace]
  refine ⟨216468364161403784441292947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144312242774269189627528631 216468364161403784441292947)
  ·
    refine ⟨324702546242105676661939421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216468364161403784441292947 324702546242105676661939421)
    ·
      refine ⟨121763454840789628748227283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324702546242105676661939421 121763454840789628748227283)
      ·
        refine ⟨182645182261184443122340925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121763454840789628748227283 182645182261184443122340925)
        ·
          refine ⟨68491943347944166170877847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182645182261184443122340925 68491943347944166170877847)
          ·
            refine ⟨102737915021916249256316771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68491943347944166170877847 102737915021916249256316771)
            ·
              refine ⟨154106872532874373884475157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102737915021916249256316771 154106872532874373884475157)
              ·
                refine ⟨7223759649978486275834773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154106872532874373884475157 7223759649978486275834773)
                ·
                  refine ⟨338613733592741544179755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7223759649978486275834773 338613733592741544179755)
                  ·
                    rfl

theorem cell23_5935031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 6].length) (baseStart_5935031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935031 prefixEnd_5935031 := by exact prefixLift 5935031
  have htrace : WordTrace (prefixWord ++ tailWord_5935031) baseStart_5935031 baseEnd_5935031 := by
    simpa [prefixWord, tailWord_5935031, baseEnd_5935031] using wordTrace_append hprefix tailTrace_5935031
  have hstable : (prefixWord ++ tailWord_5935031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935031).length < 2 ^ (prefixWord ++ tailWord_5935031).sum := by decide
  have hdescent : baseEnd_5935031 < baseStart_5935031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935048 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 6]
def baseStart_5935048 : Nat := 118140960795 + 5935048 * 2 ^ 59
def prefixEnd_5935048 : Nat := 4983230072969 + 3 ^ 40 * 5935048 * 2
def baseEnd_5935048 : Nat := 338614703500644481233913

theorem tailTrace_5935048 : CollatzResearch.WordTrace tailWord_5935048 prefixEnd_5935048 338614703500644481233913 := by
  unfold tailWord_5935048
  simp only [CollatzResearch.WordTrace]
  refine ⟨108234492101171098172330899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144312656134894797563107865 108234492101171098172330899)
  ·
    refine ⟨162351738151756647258496349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108234492101171098172330899 162351738151756647258496349)
    ·
      refine ⟨60881901806908742721936131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162351738151756647258496349 60881901806908742721936131)
      ·
        refine ⟨91322852710363114082904197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60881901806908742721936131 91322852710363114082904197)
        ·
          refine ⟨17123034883193083890544537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91322852710363114082904197 17123034883193083890544537)
          ·
            refine ⟨12842276162394812917908403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17123034883193083890544537 12842276162394812917908403)
            ·
              refine ⟨19263414243592219376862605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12842276162394812917908403 19263414243592219376862605)
              ·
                refine ⟨7223780341347082266323477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19263414243592219376862605 7223780341347082266323477)
                ·
                  refine ⟨338614703500644481233913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7223780341347082266323477 338614703500644481233913)
                  ·
                    rfl

theorem cell23_5935048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_5935048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935048 prefixEnd_5935048 := by exact prefixLift 5935048
  have htrace : WordTrace (prefixWord ++ tailWord_5935048) baseStart_5935048 baseEnd_5935048 := by
    simpa [prefixWord, tailWord_5935048, baseEnd_5935048] using wordTrace_append hprefix tailTrace_5935048
  have hstable : (prefixWord ++ tailWord_5935048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935048).length < 2 ^ (prefixWord ++ tailWord_5935048).sum := by decide
  have hdescent : baseEnd_5935048 < baseStart_5935048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935098 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_5935098 : Nat := 118140960795 + 5935098 * 2 ^ 59
def prefixEnd_5935098 : Nat := 4983230072969 + 3 ^ 40 * 5935098 * 2
def baseEnd_5935098 : Nat := 3047558005538525135479987

theorem tailTrace_5935098 : CollatzResearch.WordTrace tailWord_5935098 prefixEnd_5935098 3047558005538525135479987 := by
  unfold tailWord_5935098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54117701963040263720995487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144313871901440703255987965 54117701963040263720995487)
  ·
    refine ⟨81176552944560395581493231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54117701963040263720995487 81176552944560395581493231)
    ·
      refine ⟨121764829416840593372239847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81176552944560395581493231 121764829416840593372239847)
      ·
        refine ⟨182647244125260890058359771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121764829416840593372239847 182647244125260890058359771)
        ·
          refine ⟨273970866187891335087539657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182647244125260890058359771 273970866187891335087539657)
          ·
            refine ⟨205478149640918501315654743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273970866187891335087539657 205478149640918501315654743)
            ·
              refine ⟨308217224461377751973482115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205478149640918501315654743 308217224461377751973482115)
              ·
                refine ⟨462325836692066627960223173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308217224461377751973482115 462325836692066627960223173)
                ·
                  refine ⟨86686094379762492742541845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462325836692066627960223173 86686094379762492742541845)
                  ·
                    refine ⟨4063410674051366847306649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86686094379762492742541845 4063410674051366847306649)
                    ·
                      refine ⟨3047558005538525135479987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063410674051366847306649 3047558005538525135479987)
                      ·
                        rfl

theorem cell23_5935098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_5935098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935098 prefixEnd_5935098 := by exact prefixLift 5935098
  have htrace : WordTrace (prefixWord ++ tailWord_5935098) baseStart_5935098 baseEnd_5935098 := by
    simpa [prefixWord, tailWord_5935098, baseEnd_5935098] using wordTrace_append hprefix tailTrace_5935098
  have hstable : (prefixWord ++ tailWord_5935098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935098).length < 2 ^ (prefixWord ++ tailWord_5935098).sum := by decide
  have hdescent : baseEnd_5935098 < baseStart_5935098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935128 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5935128 : Nat := 118140960795 + 5935128 * 2 ^ 59
def prefixEnd_5935128 : Nat := 4983230072969 + 3 ^ 40 * 5935128 * 2
def baseEnd_5935128 : Nat := 3047573409958160018104849

theorem tailTrace_5935128 : CollatzResearch.WordTrace tailWord_5935128 prefixEnd_5935128 3047573409958160018104849 := by
  unfold tailWord_5935128
  simp only [CollatzResearch.WordTrace]
  refine ⟨108235951021026185003787019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144314601361368246671716025 108235951021026185003787019)
  ·
    refine ⟨162353926531539277505680529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108235951021026185003787019 162353926531539277505680529)
    ·
      refine ⟨121765444898654458129260397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162353926531539277505680529 121765444898654458129260397)
      ·
        refine ⟨45662041836995421798472649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121765444898654458129260397 45662041836995421798472649)
        ·
          refine ⟨34246531377746566348854487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45662041836995421798472649 34246531377746566348854487)
          ·
            refine ⟨51369797066619849523281731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34246531377746566348854487 51369797066619849523281731)
            ·
              refine ⟨77054695599929774284922597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51369797066619849523281731 77054695599929774284922597)
              ·
                refine ⟨14447755424986832678422987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77054695599929774284922597 14447755424986832678422987)
                ·
                  refine ⟨21671633137480249017634481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14447755424986832678422987 21671633137480249017634481)
                  ·
                    refine ⟨16253724853110186763225861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21671633137480249017634481 16253724853110186763225861)
                    ·
                      refine ⟨3047573409958160018104849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16253724853110186763225861 3047573409958160018104849)
                      ·
                        rfl

theorem cell23_5935128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5935128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935128 prefixEnd_5935128 := by exact prefixLift 5935128
  have htrace : WordTrace (prefixWord ++ tailWord_5935128) baseStart_5935128 baseEnd_5935128 := by
    simpa [prefixWord, tailWord_5935128, baseEnd_5935128] using wordTrace_append hprefix tailTrace_5935128
  have hstable : (prefixWord ++ tailWord_5935128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935128).length < 2 ^ (prefixWord ++ tailWord_5935128).sum := by decide
  have hdescent : baseEnd_5935128 < baseStart_5935128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935132 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5935132 : Nat := 118140960795 + 5935132 * 2 ^ 59
def prefixEnd_5935132 : Nat := 4983230072969 + 3 ^ 40 * 5935132 * 2
def baseEnd_5935132 : Nat := 3047575463880778002454831

theorem tailTrace_5935132 : CollatzResearch.WordTrace tailWord_5935132 prefixEnd_5935132 3047575463880778002454831 := by
  unfold tailWord_5935132
  simp only [CollatzResearch.WordTrace]
  refine ⟨108236023967018939345359825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144314698622691919127146433 108236023967018939345359825)
  ·
    refine ⟨81177017975264204509019869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108236023967018939345359825 81177017975264204509019869)
    ·
      refine ⟨30441381740724076690882451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81177017975264204509019869 30441381740724076690882451)
      ·
        refine ⟨45662072611086115036323677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30441381740724076690882451 45662072611086115036323677)
        ·
          refine ⟨17123277229157293138621379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45662072611086115036323677 17123277229157293138621379)
          ·
            refine ⟨25684915843735939707932069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17123277229157293138621379 25684915843735939707932069)
            ·
              refine ⟨4815921720700488695237263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25684915843735939707932069 4815921720700488695237263)
              ·
                refine ⟨7223882581050733042855895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815921720700488695237263 7223882581050733042855895)
                ·
                  refine ⟨10835823871576099564283843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7223882581050733042855895 10835823871576099564283843)
                  ·
                    refine ⟨16253735807364149346425765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10835823871576099564283843 16253735807364149346425765)
                    ·
                      refine ⟨3047575463880778002454831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16253735807364149346425765 3047575463880778002454831)
                      ·
                        rfl

theorem cell23_5935132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5935132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935132 prefixEnd_5935132 := by exact prefixLift 5935132
  have htrace : WordTrace (prefixWord ++ tailWord_5935132) baseStart_5935132 baseEnd_5935132 := by
    simpa [prefixWord, tailWord_5935132, baseEnd_5935132] using wordTrace_append hprefix tailTrace_5935132
  have hstable : (prefixWord ++ tailWord_5935132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935132).length < 2 ^ (prefixWord ++ tailWord_5935132).sum := by decide
  have hdescent : baseEnd_5935132 < baseStart_5935132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935135 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_5935135 : Nat := 118140960795 + 5935135 * 2 ^ 59
def prefixEnd_5935135 : Nat := 4983230072969 + 3 ^ 40 * 5935135 * 2
def baseEnd_5935135 : Nat := 3047577004322741490717317

theorem tailTrace_5935135 : CollatzResearch.WordTrace tailWord_5935135 prefixEnd_5935135 3047577004322741490717317 := by
  unfold tailWord_5935135
  simp only [CollatzResearch.WordTrace]
  refine ⟨216472157353027010203078859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144314771568684673468719239 216472157353027010203078859)
  ·
    refine ⟨324708236029540515304618289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216472157353027010203078859 324708236029540515304618289)
    ·
      refine ⟨243531177022155386478463717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324708236029540515304618289 243531177022155386478463717)
      ·
        refine ⟨45662095691654134964711947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243531177022155386478463717 45662095691654134964711947)
        ·
          refine ⟨68493143537481202447067921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45662095691654134964711947 68493143537481202447067921)
          ·
            refine ⟨51369857653110901835300941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68493143537481202447067921 51369857653110901835300941)
            ·
              refine ⟨19263696619916588188237853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51369857653110901835300941 19263696619916588188237853)
              ·
                refine ⟨7223886232468720570589195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19263696619916588188237853 7223886232468720570589195)
                ·
                  refine ⟨10835829348703080855883793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7223886232468720570589195 10835829348703080855883793)
                  ·
                    refine ⟨8126872011527310641912845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10835829348703080855883793 8126872011527310641912845)
                    ·
                      refine ⟨3047577004322741490717317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8126872011527310641912845 3047577004322741490717317)
                      ·
                        rfl

theorem cell23_5935135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_5935135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935135 prefixEnd_5935135 := by exact prefixLift 5935135
  have htrace : WordTrace (prefixWord ++ tailWord_5935135) baseStart_5935135 baseEnd_5935135 := by
    simpa [prefixWord, tailWord_5935135, baseEnd_5935135] using wordTrace_append hprefix tailTrace_5935135
  have hstable : (prefixWord ++ tailWord_5935135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935135).length < 2 ^ (prefixWord ++ tailWord_5935135).sum := by decide
  have hdescent : baseEnd_5935135 < baseStart_5935135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935151 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 7]
def baseStart_5935151 : Nat := 118140960795 + 5935151 * 2 ^ 59
def prefixEnd_5935151 : Nat := 4983230072969 + 3 ^ 40 * 5935151 * 2
def baseEnd_5935151 : Nat := 1015861740004404476039081

theorem tailTrace_5935151 : CollatzResearch.WordTrace tailWord_5935151 prefixEnd_5935151 1015861740004404476039081 := by
  unfold tailWord_5935151
  simp only [CollatzResearch.WordTrace]
  refine ⟨216472740920969044935661307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144315160613979363290440871 216472740920969044935661307)
  ·
    refine ⟨324709111381453567403491961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216472740920969044935661307 324709111381453567403491961)
    ·
      refine ⟨243531833536090175552618971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324709111381453567403491961 243531833536090175552618971)
      ·
        refine ⟨365297750304135263328928457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243531833536090175552618971 365297750304135263328928457)
        ·
          refine ⟨273973312728101447496696343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365297750304135263328928457 273973312728101447496696343)
          ·
            refine ⟨410959969092152171245044515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273973312728101447496696343 410959969092152171245044515)
            ·
              refine ⟨616439953638228256867566773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410959969092152171245044515 616439953638228256867566773)
              ·
                refine ⟨57791245653583899081334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616439953638228256867566773 57791245653583899081334385)
                ·
                  refine ⟨43343434240187924311000789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57791245653583899081334385 43343434240187924311000789)
                  ·
                    refine ⟨1015861740004404476039081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43343434240187924311000789 1015861740004404476039081)
                    ·
                      rfl

theorem cell23_5935151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_5935151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935151 prefixEnd_5935151 := by exact prefixLift 5935151
  have htrace : WordTrace (prefixWord ++ tailWord_5935151) baseStart_5935151 baseEnd_5935151 := by
    simpa [prefixWord, tailWord_5935151, baseEnd_5935151] using wordTrace_append hprefix tailTrace_5935151
  have hstable : (prefixWord ++ tailWord_5935151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935151).length < 2 ^ (prefixWord ++ tailWord_5935151).sum := by decide
  have hdescent : baseEnd_5935151 < baseStart_5935151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935171 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_5935171 : Nat := 118140960795 + 5935171 * 2 ^ 59
def prefixEnd_5935171 : Nat := 4983230072969 + 3 ^ 40 * 5935171 * 2
def baseEnd_5935171 : Nat := 3047595489626303349867151

theorem tailTrace_5935171 : CollatzResearch.WordTrace tailWord_5935171 prefixEnd_5935171 3047595489626303349867151 := by
  unfold tailWord_5935171
  simp only [CollatzResearch.WordTrace]
  refine ⟨216473470380896588351389367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144315646920597725567592911 216473470380896588351389367)
  ·
    refine ⟨324710205571344882527084051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216473470380896588351389367 324710205571344882527084051)
    ·
      refine ⟨487065308357017323790626077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324710205571344882527084051 487065308357017323790626077)
      ·
        refine ⟨182649490633881496421484779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487065308357017323790626077 182649490633881496421484779)
        ·
          refine ⟨273974235950822244632227169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182649490633881496421484779 273974235950822244632227169)
          ·
            refine ⟨205480676963116683474170377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273974235950822244632227169 205480676963116683474170377)
            ·
              refine ⟨154110507722337512605627783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205480676963116683474170377 154110507722337512605627783)
              ·
                refine ⟨231165761583506268908441675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154110507722337512605627783 231165761583506268908441675)
                ·
                  refine ⟨346748642375259403362662513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231165761583506268908441675 346748642375259403362662513)
                  ·
                    refine ⟨260061481781444552521996885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346748642375259403362662513 260061481781444552521996885)
                    ·
                      refine ⟨3047595489626303349867151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260061481781444552521996885 3047595489626303349867151)
                      ·
                        rfl

theorem cell23_5935171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_5935171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935171 prefixEnd_5935171 := by exact prefixLift 5935171
  have htrace : WordTrace (prefixWord ++ tailWord_5935171) baseStart_5935171 baseEnd_5935171 := by
    simpa [prefixWord, tailWord_5935171, baseEnd_5935171] using wordTrace_append hprefix tailTrace_5935171
  have hstable : (prefixWord ++ tailWord_5935171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935171).length < 2 ^ (prefixWord ++ tailWord_5935171).sum := by decide
  have hdescent : baseEnd_5935171 < baseStart_5935171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935188 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5935188 : Nat := 118140960795 + 5935188 * 2 ^ 59
def prefixEnd_5935188 : Nat := 4983230072969 + 3 ^ 40 * 5935188 * 2
def baseEnd_5935188 : Nat := 3047604218797429783354573

theorem tailTrace_5935188 : CollatzResearch.WordTrace tailWord_5935188 prefixEnd_5935188 3047604218797429783354573 := by
  unfold tailWord_5935188
  simp only [CollatzResearch.WordTrace]
  refine ⟨108237045210917500127379109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144316060281223333503172145 108237045210917500127379109)
  ·
    refine ⟨20294445977047031273883583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108237045210917500127379109 20294445977047031273883583)
    ·
      refine ⟨30441668965570546910825375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20294445977047031273883583 30441668965570546910825375)
      ·
        refine ⟨45662503448355820366238063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30441668965570546910825375 45662503448355820366238063)
        ·
          refine ⟨68493755172533730549357095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45662503448355820366238063 68493755172533730549357095)
          ·
            refine ⟨102740632758800595824035643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68493755172533730549357095 102740632758800595824035643)
            ·
              refine ⟨154110949138200893736053465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102740632758800595824035643 154110949138200893736053465)
              ·
                refine ⟨115583211853650670302040099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154110949138200893736053465 115583211853650670302040099)
                ·
                  refine ⟨173374817780476005453060149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115583211853650670302040099 173374817780476005453060149)
                  ·
                    refine ⟨16253889166919625511224389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173374817780476005453060149 16253889166919625511224389)
                    ·
                      refine ⟨3047604218797429783354573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16253889166919625511224389 3047604218797429783354573)
                      ·
                        rfl

theorem cell23_5935188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5935188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935188 prefixEnd_5935188 := by exact prefixLift 5935188
  have htrace : WordTrace (prefixWord ++ tailWord_5935188) baseStart_5935188 baseEnd_5935188 := by
    simpa [prefixWord, tailWord_5935188, baseEnd_5935188] using wordTrace_append hprefix tailTrace_5935188
  have hstable : (prefixWord ++ tailWord_5935188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935188).length < 2 ^ (prefixWord ++ tailWord_5935188).sum := by decide
  have hdescent : baseEnd_5935188 < baseStart_5935188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935192 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_5935192 : Nat := 118140960795 + 5935192 * 2 ^ 59
def prefixEnd_5935192 : Nat := 4983230072969 + 3 ^ 40 * 5935192 * 2
def baseEnd_5935192 : Nat := 3047606272720047767704555

theorem tailTrace_5935192 : CollatzResearch.WordTrace tailWord_5935192 prefixEnd_5935192 3047606272720047767704555 := by
  unfold tailWord_5935192
  simp only [CollatzResearch.WordTrace]
  refine ⟨108237118156910254468951915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144316157542547005958602553 108237118156910254468951915)
  ·
    refine ⟨162355677235365381703427873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108237118156910254468951915 162355677235365381703427873)
    ·
      refine ⟨121766757926524036277570905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162355677235365381703427873 121766757926524036277570905)
      ·
        refine ⟨91325068444893027208178179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121766757926524036277570905 91325068444893027208178179)
        ·
          refine ⟨136987602667339540812267269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91325068444893027208178179 136987602667339540812267269)
          ·
            refine ⟨25685175500126163902300113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136987602667339540812267269 25685175500126163902300113)
            ·
              refine ⟨19263881625094622926725085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25685175500126163902300113 19263881625094622926725085)
              ·
                refine ⟨7223955609410483597521907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19263881625094622926725085 7223955609410483597521907)
                ·
                  refine ⟨10835933414115725396282861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7223955609410483597521907 10835933414115725396282861)
                  ·
                    refine ⟨4063475030293397023606073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10835933414115725396282861 4063475030293397023606073)
                    ·
                      refine ⟨3047606272720047767704555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063475030293397023606073 3047606272720047767704555)
                      ·
                        rfl

theorem cell23_5935192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_5935192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935192 prefixEnd_5935192 := by exact prefixLift 5935192
  have htrace : WordTrace (prefixWord ++ tailWord_5935192) baseStart_5935192 baseEnd_5935192 := by
    simpa [prefixWord, tailWord_5935192, baseEnd_5935192] using wordTrace_append hprefix tailTrace_5935192
  have hstable : (prefixWord ++ tailWord_5935192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935192).length < 2 ^ (prefixWord ++ tailWord_5935192).sum := by decide
  have hdescent : baseEnd_5935192 < baseStart_5935192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935256 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_5935256 : Nat := 118140960795 + 5935256 * 2 ^ 59
def prefixEnd_5935256 : Nat := 4983230072969 + 3 ^ 40 * 5935256 * 2
def baseEnd_5935256 : Nat := 3047639135481935517304261

theorem tailTrace_5935256 : CollatzResearch.WordTrace tailWord_5935256 prefixEnd_5935256 3047639135481935517304261 := by
  unfold tailWord_5935256
  simp only [CollatzResearch.WordTrace]
  refine ⟨108238285292794323934116811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144317713723725765245489081 108238285292794323934116811)
  ·
    refine ⟨162357427939191485901175217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108238285292794323934116811 162357427939191485901175217)
    ·
      refine ⟨121768070954393614425881413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162357427939191485901175217 121768070954393614425881413)
      ·
        refine ⟨22831513303948802704852765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121768070954393614425881413 22831513303948802704852765)
        ·
          refine ⟨8561817488980801014319787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22831513303948802704852765 8561817488980801014319787)
          ·
            refine ⟨12842726233471201521479681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8561817488980801014319787 12842726233471201521479681)
            ·
              refine ⟨9632044675103401141109761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12842726233471201521479681 9632044675103401141109761)
              ·
                refine ⟨7224033506327550855832321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9632044675103401141109761 7224033506327550855832321)
                ·
                  refine ⟨5418025129745663141874241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7224033506327550855832321 5418025129745663141874241)
                  ·
                    refine ⟨4063518847309247356405681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5418025129745663141874241 4063518847309247356405681)
                    ·
                      refine ⟨3047639135481935517304261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063518847309247356405681 3047639135481935517304261)
                      ·
                        rfl

theorem cell23_5935256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_5935256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935256 prefixEnd_5935256 := by exact prefixLift 5935256
  have htrace : WordTrace (prefixWord ++ tailWord_5935256) baseStart_5935256 baseEnd_5935256 := by
    simpa [prefixWord, tailWord_5935256, baseEnd_5935256] using wordTrace_append hprefix tailTrace_5935256
  have hstable : (prefixWord ++ tailWord_5935256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935256).length < 2 ^ (prefixWord ++ tailWord_5935256).sum := by decide
  have hdescent : baseEnd_5935256 < baseStart_5935256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935295 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 6, 2]
def baseStart_5935295 : Nat := 118140960795 + 5935295 * 2 ^ 59
def prefixEnd_5935295 : Nat := 4983230072969 + 3 ^ 40 * 5935295 * 2
def baseEnd_5935295 : Nat := 3047659161227460864716581

theorem tailTrace_5935295 : CollatzResearch.WordTrace tailWord_5935295 prefixEnd_5935295 3047659161227460864716581 := by
  unfold tailWord_5935295
  simp only [CollatzResearch.WordTrace]
  refine ⟨216477993032447357528903339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144318662021631571685935559 216477993032447357528903339)
  ·
    refine ⟨324716989548671036293355009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216477993032447357528903339 324716989548671036293355009)
    ·
      refine ⟨243537742161503277220016257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324716989548671036293355009 243537742161503277220016257)
      ·
        refine ⟨182653306621127457915012193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243537742161503277220016257 182653306621127457915012193)
        ·
          refine ⟨136989979965845593436259145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182653306621127457915012193 136989979965845593436259145)
          ·
            refine ⟨102742484974384195077194359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136989979965845593436259145 102742484974384195077194359)
            ·
              refine ⟨154113727461576292615791539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102742484974384195077194359 154113727461576292615791539)
              ·
                refine ⟨231170591192364438923687309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154113727461576292615791539 231170591192364438923687309)
                ·
                  refine ⟨86688971697136664596382741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231170591192364438923687309 86688971697136664596382741)
                  ·
                    refine ⟨4063545548303281152955441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86688971697136664596382741 4063545548303281152955441)
                    ·
                      refine ⟨3047659161227460864716581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063545548303281152955441 3047659161227460864716581)
                      ·
                        rfl

theorem cell23_5935295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_5935295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935295 prefixEnd_5935295 := by exact prefixLift 5935295
  have htrace : WordTrace (prefixWord ++ tailWord_5935295) baseStart_5935295 baseEnd_5935295 := by
    simpa [prefixWord, tailWord_5935295, baseEnd_5935295] using wordTrace_append hprefix tailTrace_5935295
  have hstable : (prefixWord ++ tailWord_5935295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935295).length < 2 ^ (prefixWord ++ tailWord_5935295).sum := by decide
  have hdescent : baseEnd_5935295 < baseStart_5935295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935356 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_5935356 : Nat := 118140960795 + 5935356 * 2 ^ 59
def prefixEnd_5935356 : Nat := 4983230072969 + 3 ^ 40 * 5935356 * 2
def baseEnd_5935356 : Nat := 1015896827849128375351267

theorem tailTrace_5935356 : CollatzResearch.WordTrace tailWord_5935356 prefixEnd_5935356 1015896827849128375351267 := by
  unfold tailWord_5935356
  simp only [CollatzResearch.WordTrace]
  refine ⟨108240108942613182473436961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144320145256817576631249281 108240108942613182473436961)
  ·
    refine ⟨81180081706959886855077721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108240108942613182473436961 81180081706959886855077721)
    ·
      refine ⟨60885061280219915141308291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81180081706959886855077721 60885061280219915141308291)
      ·
        refine ⟨91327591920329872711962437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60885061280219915141308291 91327591920329872711962437)
        ·
          refine ⟨17123923485061851133492957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91327591920329872711962437 17123923485061851133492957)
          ·
            refine ⟨6421471306898194175059859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17123923485061851133492957 6421471306898194175059859)
            ·
              refine ⟨9632206960347291262589789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421471306898194175059859 9632206960347291262589789)
              ·
                refine ⟨3612077610130234223471171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9632206960347291262589789 3612077610130234223471171)
                ·
                  refine ⟨5418116415195351335206757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612077610130234223471171 5418116415195351335206757)
                  ·
                    refine ⟨1015896827849128375351267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418116415195351335206757 1015896827849128375351267)
                    ·
                      rfl

theorem cell23_5935356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_5935356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935356 prefixEnd_5935356 := by exact prefixLift 5935356
  have htrace : WordTrace (prefixWord ++ tailWord_5935356) baseStart_5935356 baseEnd_5935356 := by
    simpa [prefixWord, tailWord_5935356, baseEnd_5935356] using wordTrace_append hprefix tailTrace_5935356
  have hstable : (prefixWord ++ tailWord_5935356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935356).length < 2 ^ (prefixWord ++ tailWord_5935356).sum := by decide
  have hdescent : baseEnd_5935356 < baseStart_5935356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 1, 1, 3]
def baseStart_5935379 : Nat := 118140960795 + 5935379 * 2 ^ 59
def prefixEnd_5935379 : Nat := 4983230072969 + 3 ^ 40 * 5935379 * 2
def baseEnd_5935379 : Nat := 3047702293602438536066195

theorem tailTrace_5935379 : CollatzResearch.WordTrace tailWord_5935379 prefixEnd_5935379 3047702293602438536066195 := by
  unfold tailWord_5935379
  simp only [CollatzResearch.WordTrace]
  refine ⟨216481056764143039874961191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144320704509428693249974127 216481056764143039874961191)
  ·
    refine ⟨324721585146214559812441787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216481056764143039874961191 324721585146214559812441787)
    ·
      refine ⟨487082377719321839718662681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324721585146214559812441787 487082377719321839718662681)
      ·
        refine ⟨365311783289491379788997011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487082377719321839718662681 365311783289491379788997011)
        ·
          refine ⟨547967674934237069683495517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365311783289491379788997011 547967674934237069683495517)
          ·
            refine ⟨205487878100338901131310819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547967674934237069683495517 205487878100338901131310819)
            ·
              refine ⟨308231817150508351696966229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205487878100338901131310819 308231817150508351696966229)
              ·
                refine ⟨3612091607232519746448823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 308231817150508351696966229 3612091607232519746448823)
                ·
                  refine ⟨5418137410848779619673235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612091607232519746448823 5418137410848779619673235)
                  ·
                    refine ⟨8127206116273169429509853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418137410848779619673235 8127206116273169429509853)
                    ·
                      refine ⟨3047702293602438536066195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127206116273169429509853 3047702293602438536066195)
                      ·
                        rfl

theorem cell23_5935379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 1, 3].length) (baseStart_5935379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935379 prefixEnd_5935379 := by exact prefixLift 5935379
  have htrace : WordTrace (prefixWord ++ tailWord_5935379) baseStart_5935379 baseEnd_5935379 := by
    simpa [prefixWord, tailWord_5935379, baseEnd_5935379] using wordTrace_append hprefix tailTrace_5935379
  have hstable : (prefixWord ++ tailWord_5935379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935379).length < 2 ^ (prefixWord ++ tailWord_5935379).sum := by decide
  have hdescent : baseEnd_5935379 < baseStart_5935379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935386 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_5935386 : Nat := 118140960795 + 5935386 * 2 ^ 59
def prefixEnd_5935386 : Nat := 4983230072969 + 3 ^ 40 * 5935386 * 2
def baseEnd_5935386 : Nat := 338633987551891112075407

theorem tailTrace_5935386 : CollatzResearch.WordTrace tailWord_5935386 prefixEnd_5935386 338633987551891112075407 := by
  unfold tailWord_5935386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54120328018779420017616503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144320874716745120046977341 54120328018779420017616503)
  ·
    refine ⟨81180492028169130026424755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54120328018779420017616503 81180492028169130026424755)
    ·
      refine ⟨121770738042253695039637133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81180492028169130026424755 121770738042253695039637133)
      ·
        refine ⟨45664026765845135639863925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121770738042253695039637133 45664026765845135639863925)
        ·
          refine ⟨4281002509297981466237243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45664026765845135639863925 4281002509297981466237243)
          ·
            refine ⟨6421503763946972199355865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281002509297981466237243 6421503763946972199355865)
            ·
              refine ⟨4816127822960229149516899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6421503763946972199355865 4816127822960229149516899)
              ·
                refine ⟨7224191734440343724275349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816127822960229149516899 7224191734440343724275349)
                ·
                  refine ⟨338633987551891112075407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7224191734440343724275349 338633987551891112075407)
                  ·
                    rfl

theorem cell23_5935386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_5935386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935386 prefixEnd_5935386 := by exact prefixLift 5935386
  have htrace : WordTrace (prefixWord ++ tailWord_5935386) baseStart_5935386 baseEnd_5935386 := by
    simpa [prefixWord, tailWord_5935386, baseEnd_5935386] using wordTrace_append hprefix tailTrace_5935386
  have hstable : (prefixWord ++ tailWord_5935386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935386).length < 2 ^ (prefixWord ++ tailWord_5935386).sum := by decide
  have hdescent : baseEnd_5935386 < baseStart_5935386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935395 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 1, 6]
def baseStart_5935395 : Nat := 118140960795 + 5935395 * 2 ^ 59
def prefixEnd_5935395 : Nat := 4983230072969 + 3 ^ 40 * 5935395 * 2
def baseEnd_5935395 : Nat := 1015903503097636824488707

theorem tailTrace_5935395 : CollatzResearch.WordTrace tailWord_5935395 prefixEnd_5935395 1015903503097636824488707 := by
  unfold tailWord_5935395
  simp only [CollatzResearch.WordTrace]
  refine ⟨216481640332085074607543639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144321093554723383071695759 216481640332085074607543639)
  ·
    refine ⟨324722460498127611911315459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216481640332085074607543639 324722460498127611911315459)
    ·
      refine ⟨487083690747191417866973189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324722460498127611911315459 487083690747191417866973189)
      ·
        refine ⟨91328192015098390850057473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 487083690747191417866973189 91328192015098390850057473)
        ·
          refine ⟨68496144011323793137543105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91328192015098390850057473 68496144011323793137543105)
          ·
            refine ⟨51372108008492844853157329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68496144011323793137543105 51372108008492844853157329)
            ·
              refine ⟨38529081006369633639867997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51372108008492844853157329 38529081006369633639867997)
              ·
                refine ⟨14448405377388612614950499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38529081006369633639867997 14448405377388612614950499)
                ·
                  refine ⟨21672608066082918922425749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14448405377388612614950499 21672608066082918922425749)
                  ·
                    refine ⟨1015903503097636824488707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21672608066082918922425749 1015903503097636824488707)
                    ·
                      rfl

theorem cell23_5935395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 6].length) (baseStart_5935395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935395 prefixEnd_5935395 := by exact prefixLift 5935395
  have htrace : WordTrace (prefixWord ++ tailWord_5935395) baseStart_5935395 baseEnd_5935395 := by
    simpa [prefixWord, tailWord_5935395, baseEnd_5935395] using wordTrace_append hprefix tailTrace_5935395
  have hstable : (prefixWord ++ tailWord_5935395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935395).length < 2 ^ (prefixWord ++ tailWord_5935395).sum := by decide
  have hdescent : baseEnd_5935395 < baseStart_5935395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935412 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5935412 : Nat := 118140960795 + 5935412 * 2 ^ 59
def prefixEnd_5935412 : Nat := 4983230072969 + 3 ^ 40 * 5935412 * 2
def baseEnd_5935412 : Nat := 1015906412821345635651181

theorem tailTrace_5935412 : CollatzResearch.WordTrace tailWord_5935412 prefixEnd_5935412 1015906412821345635651181 := by
  unfold tailWord_5935412
  simp only [CollatzResearch.WordTrace]
  refine ⟨108241130186511743255456245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144321506915348991007274993 108241130186511743255456245)
  ·
    refine ⟨10147605954985475930199023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108241130186511743255456245 10147605954985475930199023)
    ·
      refine ⟨15221408932478213895298535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10147605954985475930199023 15221408932478213895298535)
      ·
        refine ⟨22832113398717320842947803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15221408932478213895298535 22832113398717320842947803)
        ·
          refine ⟨34248170098075981264421705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22832113398717320842947803 34248170098075981264421705)
          ·
            refine ⟨25686127573556985948316279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34248170098075981264421705 25686127573556985948316279)
            ·
              refine ⟨38529191360335478922474419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25686127573556985948316279 38529191360335478922474419)
              ·
                refine ⟨57793787040503218383711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38529191360335478922474419 57793787040503218383711629)
                ·
                  refine ⟨21672670140188706893891861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57793787040503218383711629 21672670140188706893891861)
                  ·
                    refine ⟨1015906412821345635651181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21672670140188706893891861 1015906412821345635651181)
                    ·
                      rfl

theorem cell23_5935412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5935412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935412 prefixEnd_5935412 := by exact prefixLift 5935412
  have htrace : WordTrace (prefixWord ++ tailWord_5935412) baseStart_5935412 baseEnd_5935412 := by
    simpa [prefixWord, tailWord_5935412, baseEnd_5935412] using wordTrace_append hprefix tailTrace_5935412
  have hstable : (prefixWord ++ tailWord_5935412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935412).length < 2 ^ (prefixWord ++ tailWord_5935412).sum := by decide
  have hdescent : baseEnd_5935412 < baseStart_5935412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935425 : List Nat := [1, 2, 5, 2, 13]
def baseStart_5935425 : Nat := 118140960795 + 5935425 * 2 ^ 59
def prefixEnd_5935425 : Nat := 4983230072969 + 3 ^ 40 * 5935425 * 2
def baseEnd_5935425 : Nat := 4180693983144781009727

theorem tailTrace_5935425 : CollatzResearch.WordTrace tailWord_5935425 prefixEnd_5935425 4180693983144781009727 := by
  unfold tailWord_5935425
  simp only [CollatzResearch.WordTrace]
  refine ⟨216482734521976389731135729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144321823014650926487423819 216482734521976389731135729)
  ·
    refine ⟨162362050891482292298351797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216482734521976389731135729 162362050891482292298351797)
    ·
      refine ⟨15221442271076464902970481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162362050891482292298351797 15221442271076464902970481)
      ·
        refine ⟨11416081703307348677227861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15221442271076464902970481 11416081703307348677227861)
        ·
          refine ⟨4180693983144781009727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11416081703307348677227861 4180693983144781009727)
          ·
            rfl

theorem cell23_5935425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 13].length) (baseStart_5935425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935425 prefixEnd_5935425 := by exact prefixLift 5935425
  have htrace : WordTrace (prefixWord ++ tailWord_5935425) baseStart_5935425 baseEnd_5935425 := by
    simpa [prefixWord, tailWord_5935425, baseEnd_5935425] using wordTrace_append hprefix tailTrace_5935425
  have hstable : (prefixWord ++ tailWord_5935425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935425).length < 2 ^ (prefixWord ++ tailWord_5935425).sum := by decide
  have hdescent : baseEnd_5935425 < baseStart_5935425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935465 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_5935465 : Nat := 118140960795 + 5935465 * 2 ^ 59
def prefixEnd_5935465 : Nat := 4983230072969 + 3 ^ 40 * 5935465 * 2
def baseEnd_5935465 : Nat := 3047746452938725199590799

theorem tailTrace_5935465 : CollatzResearch.WordTrace tailWord_5935465 prefixEnd_5935465 3047746452938725199590799 := by
  unfold tailWord_5935465
  simp only [CollatzResearch.WordTrace]
  refine ⟨216484193441831476562591849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144322795627887651041727899 216484193441831476562591849)
  ·
    refine ⟨162363145081373607421943887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216484193441831476562591849 162363145081373607421943887)
    ·
      refine ⟨243544717622060411132915831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162363145081373607421943887 243544717622060411132915831)
      ·
        refine ⟨365317076433090616699373747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243544717622060411132915831 365317076433090616699373747)
        ·
          refine ⟨547975614649635925049060621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365317076433090616699373747 547975614649635925049060621)
          ·
            refine ⟨205490855493613471893397733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547975614649635925049060621 205490855493613471893397733)
            ·
              refine ⟨38529535405052525980012075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205490855493613471893397733 38529535405052525980012075)
              ·
                refine ⟨57794303107578788970018113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38529535405052525980012075 57794303107578788970018113)
                ·
                  refine ⟨43345727330684091727513585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57794303107578788970018113 43345727330684091727513585)
                  ·
                    refine ⟨32509295498013068795635189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43345727330684091727513585 32509295498013068795635189)
                    ·
                      refine ⟨3047746452938725199590799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32509295498013068795635189 3047746452938725199590799)
                      ·
                        rfl

theorem cell23_5935465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_5935465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935465 prefixEnd_5935465 := by exact prefixLift 5935465
  have htrace : WordTrace (prefixWord ++ tailWord_5935465) baseStart_5935465 baseEnd_5935465 := by
    simpa [prefixWord, tailWord_5935465, baseEnd_5935465] using wordTrace_append hprefix tailTrace_5935465
  have hstable : (prefixWord ++ tailWord_5935465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935465).length < 2 ^ (prefixWord ++ tailWord_5935465).sum := by decide
  have hdescent : baseEnd_5935465 < baseStart_5935465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935469 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_5935469 : Nat := 118140960795 + 5935469 * 2 ^ 59
def prefixEnd_5935469 : Nat := 4983230072969 + 3 ^ 40 * 5935469 * 2
def baseEnd_5935469 : Nat := 3047748506861343183940781

theorem tailTrace_5935469 : CollatzResearch.WordTrace tailWord_5935469 prefixEnd_5935469 3047748506861343183940781 := by
  unfold tailWord_5935469
  simp only [CollatzResearch.WordTrace]
  refine ⟨216484339333816985245737461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144322892889211323497158307 216484339333816985245737461)
  ·
    refine ⟨20295406812545342366787887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216484339333816985245737461 20295406812545342366787887)
    ·
      refine ⟨30443110218818013550181831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20295406812545342366787887 30443110218818013550181831)
      ·
        refine ⟨45664665328227020325272747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30443110218818013550181831 45664665328227020325272747)
        ·
          refine ⟨68496997992340530487909121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45664665328227020325272747 68496997992340530487909121)
          ·
            refine ⟨51372748494255397865931841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68496997992340530487909121 51372748494255397865931841)
            ·
              refine ⟨38529561370691548399448881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51372748494255397865931841 38529561370691548399448881)
              ·
                refine ⟨28897171028018661299586661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38529561370691548399448881 28897171028018661299586661)
                ·
                  refine ⟨5418219567753498993672499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28897171028018661299586661 5418219567753498993672499)
                  ·
                    refine ⟨8127329351630248490508749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418219567753498993672499 8127329351630248490508749)
                    ·
                      refine ⟨3047748506861343183940781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127329351630248490508749 3047748506861343183940781)
                      ·
                        rfl

theorem cell23_5935469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_5935469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935469 prefixEnd_5935469 := by exact prefixLift 5935469
  have htrace : WordTrace (prefixWord ++ tailWord_5935469) baseStart_5935469 baseEnd_5935469 := by
    simpa [prefixWord, tailWord_5935469, baseEnd_5935469] using wordTrace_append hprefix tailTrace_5935469
  have hstable : (prefixWord ++ tailWord_5935469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935469).length < 2 ^ (prefixWord ++ tailWord_5935469).sum := by decide
  have hdescent : baseEnd_5935469 < baseStart_5935469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935475 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_5935475 : Nat := 118140960795 + 5935475 * 2 ^ 59
def prefixEnd_5935475 : Nat := 4983230072969 + 3 ^ 40 * 5935475 * 2
def baseEnd_5935475 : Nat := 3047751587745270160465753

theorem tailTrace_5935475 : CollatzResearch.WordTrace tailWord_5935475 prefixEnd_5935475 3047751587745270160465753 := by
  unfold tailWord_5935475
  simp only [CollatzResearch.WordTrace]
  refine ⟨216484558171795248270455879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144323038781196832180303919 216484558171795248270455879)
  ·
    refine ⟨324726837257692872405683819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216484558171795248270455879 324726837257692872405683819)
    ·
      refine ⟨487090255886539308608525729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324726837257692872405683819 487090255886539308608525729)
      ·
        refine ⟨365317691914904481456394297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487090255886539308608525729 365317691914904481456394297)
        ·
          refine ⟨273988268936178361092295723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365317691914904481456394297 273988268936178361092295723)
          ·
            refine ⟨410982403404267541638443585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273988268936178361092295723 410982403404267541638443585)
            ·
              refine ⟨308236802553200656228832689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410982403404267541638443585 308236802553200656228832689)
              ·
                refine ⟨231177601914900492171624517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308236802553200656228832689 231177601914900492171624517)
                ·
                  refine ⟨43345800359043842282179597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231177601914900492171624517 43345800359043842282179597)
                  ·
                    refine ⟨16254675134641440855817349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43345800359043842282179597 16254675134641440855817349)
                    ·
                      refine ⟨3047751587745270160465753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16254675134641440855817349 3047751587745270160465753)
                      ·
                        rfl

theorem cell23_5935475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_5935475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935475 prefixEnd_5935475 := by exact prefixLift 5935475
  have htrace : WordTrace (prefixWord ++ tailWord_5935475) baseStart_5935475 baseEnd_5935475 := by
    simpa [prefixWord, tailWord_5935475, baseEnd_5935475] using wordTrace_append hprefix tailTrace_5935475
  have hstable : (prefixWord ++ tailWord_5935475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935475).length < 2 ^ (prefixWord ++ tailWord_5935475).sum := by decide
  have hdescent : baseEnd_5935475 < baseStart_5935475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935510 : List Nat := [5, 3, 1, 2, 1, 2, 2, 7]
def baseStart_5935510 : Nat := 118140960795 + 5935510 * 2 ^ 59
def prefixEnd_5935510 : Nat := 4983230072969 + 3 ^ 40 * 5935510 * 2
def baseEnd_5935510 : Nat := 112880354058080649019559

theorem tailTrace_5935510 : CollatzResearch.WordTrace tailWord_5935510 prefixEnd_5935510 112880354058080649019559 := by
  unfold tailWord_5935510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530364670416778077998749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144323889817778966165319989 13530364670416778077998749)
  ·
    refine ⟨5073886751406291779249531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13530364670416778077998749 5073886751406291779249531)
    ·
      refine ⟨7610830127109437668874297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073886751406291779249531 7610830127109437668874297)
      ·
        refine ⟨5708122595332078251655723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7610830127109437668874297 5708122595332078251655723)
        ·
          refine ⟨8562183892998117377483585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708122595332078251655723 8562183892998117377483585)
          ·
            refine ⟨6421637919748588033112689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8562183892998117377483585 6421637919748588033112689)
            ·
              refine ⟨4816228439811441024834517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6421637919748588033112689 4816228439811441024834517)
              ·
                refine ⟨112880354058080649019559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4816228439811441024834517 112880354058080649019559)
                ·
                  rfl

theorem cell23_5935510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_5935510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935510 prefixEnd_5935510 := by exact prefixLift 5935510
  have htrace : WordTrace (prefixWord ++ tailWord_5935510) baseStart_5935510 baseEnd_5935510 := by
    simpa [prefixWord, tailWord_5935510, baseEnd_5935510] using wordTrace_append hprefix tailTrace_5935510
  have hstable : (prefixWord ++ tailWord_5935510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935510).length < 2 ^ (prefixWord ++ tailWord_5935510).sum := by decide
  have hdescent : baseEnd_5935510 < baseStart_5935510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935535 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_5935535 : Nat := 118140960795 + 5935535 * 2 ^ 59
def prefixEnd_5935535 : Nat := 4983230072969 + 3 ^ 40 * 5935535 * 2
def baseEnd_5935535 : Nat := 3047782396584539925715477

theorem tailTrace_5935535 : CollatzResearch.WordTrace tailWord_5935535 prefixEnd_5935535 3047782396584539925715477 := by
  unfold tailWord_5935535
  simp only [CollatzResearch.WordTrace]
  refine ⟨216486746551577878517640059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144324497701051919011760039 216486746551577878517640059)
  ·
    refine ⟨324730119827366817776460089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216486746551577878517640059 324730119827366817776460089)
    ·
      refine ⟨243547589870525113332345067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324730119827366817776460089 243547589870525113332345067)
      ·
        refine ⟨365321384805787669998517601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243547589870525113332345067 365321384805787669998517601)
        ·
          refine ⟨273991038604340752498888201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365321384805787669998517601 273991038604340752498888201)
          ·
            refine ⟨205493278953255564374166151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273991038604340752498888201 205493278953255564374166151)
            ·
              refine ⟨308239918429883346561249227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205493278953255564374166151 308239918429883346561249227)
              ·
                refine ⟨462359877644825019841873841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308239918429883346561249227 462359877644825019841873841)
                ·
                  refine ⟨346769908233618764881405381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462359877644825019841873841 346769908233618764881405381)
                  ·
                    refine ⟨65019357793803518415263509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346769908233618764881405381 65019357793803518415263509)
                    ·
                      refine ⟨3047782396584539925715477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65019357793803518415263509 3047782396584539925715477)
                      ·
                        rfl

theorem cell23_5935535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_5935535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935535 prefixEnd_5935535 := by exact prefixLift 5935535
  have htrace : WordTrace (prefixWord ++ tailWord_5935535) baseStart_5935535 baseEnd_5935535 := by
    simpa [prefixWord, tailWord_5935535, baseEnd_5935535] using wordTrace_append hprefix tailTrace_5935535
  have hstable : (prefixWord ++ tailWord_5935535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935535).length < 2 ^ (prefixWord ++ tailWord_5935535).sum := by decide
  have hdescent : baseEnd_5935535 < baseStart_5935535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935549 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 7]
def baseStart_5935549 : Nat := 118140960795 + 5935549 * 2 ^ 59
def prefixEnd_5935549 : Nat := 4983230072969 + 3 ^ 40 * 5935549 * 2
def baseEnd_5935549 : Nat := 338643287257078096771157

theorem tailTrace_5935549 : CollatzResearch.WordTrace tailWord_5935549 prefixEnd_5935549 338643287257078096771157 := by
  unfold tailWord_5935549
  simp only [CollatzResearch.WordTrace]
  refine ⟨216487257173527158908649701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144324838115684772605766467 216487257173527158908649701)
  ·
    refine ⟨40591360720036342295371819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216487257173527158908649701 40591360720036342295371819)
    ·
      refine ⟨60887041080054513443057729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40591360720036342295371819 60887041080054513443057729)
      ·
        refine ⟨45665280810040885082293297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60887041080054513443057729 45665280810040885082293297)
        ·
          refine ⟨34248960607530663811719973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45665280810040885082293297 34248960607530663811719973)
          ·
            refine ⟨6421680113911999464697495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34248960607530663811719973 6421680113911999464697495)
            ·
              refine ⟨9632520170867999197046243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421680113911999464697495 9632520170867999197046243)
              ·
                refine ⟨14448780256301998795569365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9632520170867999197046243 14448780256301998795569365)
                ·
                  refine ⟨338643287257078096771157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14448780256301998795569365 338643287257078096771157)
                  ·
                    rfl

theorem cell23_5935549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_5935549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935549 prefixEnd_5935549 := by exact prefixLift 5935549
  have htrace : WordTrace (prefixWord ++ tailWord_5935549) baseStart_5935549 baseEnd_5935549 := by
    simpa [prefixWord, tailWord_5935549, baseEnd_5935549] using wordTrace_append hprefix tailTrace_5935549
  have hstable : (prefixWord ++ tailWord_5935549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935549).length < 2 ^ (prefixWord ++ tailWord_5935549).sum := by decide
  have hdescent : baseEnd_5935549 < baseStart_5935549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935560 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_5935560 : Nat := 118140960795 + 5935560 * 2 ^ 59
def prefixEnd_5935560 : Nat := 4983230072969 + 3 ^ 40 * 5935560 * 2
def baseEnd_5935560 : Nat := 3047795233600902327902863

theorem tailTrace_5935560 : CollatzResearch.WordTrace tailWord_5935560 prefixEnd_5935560 3047795233600902327902863 := by
  unfold tailWord_5935560
  simp only [CollatzResearch.WordTrace]
  refine ⟨108243829188243653893650067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144325105584324871858200089 108243829188243653893650067)
  ·
    refine ⟨162365743782365480840475101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108243829188243653893650067 162365743782365480840475101)
    ·
      refine ⟨60887153918387055315178163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162365743782365480840475101 60887153918387055315178163)
      ·
        refine ⟨91330730877580582972767245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60887153918387055315178163 91330730877580582972767245)
        ·
          refine ⟨34249024079092718614787717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91330730877580582972767245 34249024079092718614787717)
          ·
            refine ⟨6421692014829884740272697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34249024079092718614787717 6421692014829884740272697)
            ·
              refine ⟨4816269011122413555204523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6421692014829884740272697 4816269011122413555204523)
              ·
                refine ⟨7224403516683620332806785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816269011122413555204523 7224403516683620332806785)
                ·
                  refine ⟨5418302637512715249605089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7224403516683620332806785 5418302637512715249605089)
                  ·
                    refine ⟨4063726978134536437203817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5418302637512715249605089 4063726978134536437203817)
                    ·
                      refine ⟨3047795233600902327902863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063726978134536437203817 3047795233600902327902863)
                      ·
                        rfl

theorem cell23_5935560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_5935560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935560 prefixEnd_5935560 := by exact prefixLift 5935560
  have htrace : WordTrace (prefixWord ++ tailWord_5935560) baseStart_5935560 baseEnd_5935560 := by
    simpa [prefixWord, tailWord_5935560, baseEnd_5935560] using wordTrace_append hprefix tailTrace_5935560
  have hstable : (prefixWord ++ tailWord_5935560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935560).length < 2 ^ (prefixWord ++ tailWord_5935560).sum := by decide
  have hdescent : baseEnd_5935560 < baseStart_5935560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935562 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_5935562 : Nat := 118140960795 + 5935562 * 2 ^ 59
def prefixEnd_5935562 : Nat := 4983230072969 + 3 ^ 40 * 5935562 * 2
def baseEnd_5935562 : Nat := 1015932086854070440025951

theorem tailTrace_5935562 : CollatzResearch.WordTrace tailWord_5935562 prefixEnd_5935562 1015932086854070440025951 := by
  unfold tailWord_5935562
  simp only [CollatzResearch.WordTrace]
  refine ⟨54121932830620015532218235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144325154214986708085915293 54121932830620015532218235)
  ·
    refine ⟨81182899245930023298327353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54121932830620015532218235 81182899245930023298327353)
    ·
      refine ⟨60887174434447517473745515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81182899245930023298327353 60887174434447517473745515)
      ·
        refine ⟨91330761651671276210618273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60887174434447517473745515 91330761651671276210618273)
        ·
          refine ⟨68498071238753457157963705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91330761651671276210618273 68498071238753457157963705)
          ·
            refine ⟨51373553429065092868472779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68498071238753457157963705 51373553429065092868472779)
            ·
              refine ⟨77060330143597639302709169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51373553429065092868472779 77060330143597639302709169)
              ·
                refine ⟨57795247607698229477031877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77060330143597639302709169 57795247607698229477031877)
                ·
                  refine ⟨10836608926443418026943477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57795247607698229477031877 10836608926443418026943477)
                  ·
                    refine ⟨1015932086854070440025951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10836608926443418026943477 1015932086854070440025951)
                    ·
                      rfl

theorem cell23_5935562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_5935562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935562 prefixEnd_5935562 := by exact prefixLift 5935562
  have htrace : WordTrace (prefixWord ++ tailWord_5935562) baseStart_5935562 baseEnd_5935562 := by
    simpa [prefixWord, tailWord_5935562, baseEnd_5935562] using wordTrace_append hprefix tailTrace_5935562
  have hstable : (prefixWord ++ tailWord_5935562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935562).length < 2 ^ (prefixWord ++ tailWord_5935562).sum := by decide
  have hdescent : baseEnd_5935562 < baseStart_5935562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935599 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 2, 4, 2]
def baseStart_5935599 : Nat := 118140960795 + 5935599 * 2 ^ 59
def prefixEnd_5935599 : Nat := 4983230072969 + 3 ^ 40 * 5935599 * 2
def baseEnd_5935599 : Nat := 3047815259346427675315183

theorem tailTrace_5935599 : CollatzResearch.WordTrace tailWord_5935599 prefixEnd_5935599 3047815259346427675315183 := by
  unfold tailWord_5935599
  simp only [CollatzResearch.WordTrace]
  refine ⟨216489080823346017447969851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144326053882230678298646567 216489080823346017447969851)
  ·
    refine ⟨324733621235019026171954777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216489080823346017447969851 324733621235019026171954777)
    ·
      refine ⟨243550215926264269628966083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324733621235019026171954777 243550215926264269628966083)
      ·
        refine ⟨365325323889396404443449125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243550215926264269628966083 365325323889396404443449125)
        ·
          refine ⟨68498498229261825833146711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365325323889396404443449125 68498498229261825833146711)
          ·
            refine ⟨102747747343892738749720067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68498498229261825833146711 102747747343892738749720067)
            ·
              refine ⟨154121621015839108124580101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102747747343892738749720067 154121621015839108124580101)
              ·
                refine ⟨28897803940469832773358769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154121621015839108124580101 28897803940469832773358769)
                ·
                  refine ⟨21673352955352374580019077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28897803940469832773358769 21673352955352374580019077)
                  ·
                    refine ⟨4063753679128570233753577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21673352955352374580019077 4063753679128570233753577)
                    ·
                      refine ⟨3047815259346427675315183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063753679128570233753577 3047815259346427675315183)
                      ·
                        rfl

theorem cell23_5935599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4, 2].length) (baseStart_5935599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935599 prefixEnd_5935599 := by exact prefixLift 5935599
  have htrace : WordTrace (prefixWord ++ tailWord_5935599) baseStart_5935599 baseEnd_5935599 := by
    simpa [prefixWord, tailWord_5935599, baseEnd_5935599] using wordTrace_append hprefix tailTrace_5935599
  have hstable : (prefixWord ++ tailWord_5935599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935599).length < 2 ^ (prefixWord ++ tailWord_5935599).sum := by decide
  have hdescent : baseEnd_5935599 < baseStart_5935599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935612 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_5935612 : Nat := 118140960795 + 5935612 * 2 ^ 59
def prefixEnd_5935612 : Nat := 4983230072969 + 3 ^ 40 * 5935612 * 2
def baseEnd_5935612 : Nat := 3047821934594936124452623

theorem tailTrace_5935612 : CollatzResearch.WordTrace tailWord_5935612 prefixEnd_5935612 3047821934594936124452623 := by
  unfold tailWord_5935612
  simp only [CollatzResearch.WordTrace]
  refine ⟨108244777486149460334096545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144326369981532613778795393 108244777486149460334096545)
  ·
    refine ⟨81183583114612095250572409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108244777486149460334096545 81183583114612095250572409)
    ·
      refine ⟨60887687335959071437929307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81183583114612095250572409 60887687335959071437929307)
      ·
        refine ⟨91331531003938607156893961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60887687335959071437929307 91331531003938607156893961)
        ·
          refine ⟨68498648252953955367670471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91331531003938607156893961 68498648252953955367670471)
          ·
            refine ⟨102747972379430933051505707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68498648252953955367670471 102747972379430933051505707)
            ·
              refine ⟨154121958569146399577258561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102747972379430933051505707 154121958569146399577258561)
              ·
                refine ⟨115591468926859799682943921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154121958569146399577258561 115591468926859799682943921)
                ·
                  refine ⟨86693601695144849762207941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115591468926859799682943921 86693601695144849762207941)
                  ·
                    refine ⟨16255050317839659330413989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86693601695144849762207941 16255050317839659330413989)
                    ·
                      refine ⟨3047821934594936124452623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16255050317839659330413989 3047821934594936124452623)
                      ·
                        rfl

theorem cell23_5935612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_5935612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935612 prefixEnd_5935612 := by exact prefixLift 5935612
  have htrace : WordTrace (prefixWord ++ tailWord_5935612) baseStart_5935612 baseEnd_5935612 := by
    simpa [prefixWord, tailWord_5935612, baseEnd_5935612] using wordTrace_append hprefix tailTrace_5935612
  have hstable : (prefixWord ++ tailWord_5935612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935612).length < 2 ^ (prefixWord ++ tailWord_5935612).sum := by decide
  have hdescent : baseEnd_5935612 < baseStart_5935612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935656 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 6]
def baseStart_5935656 : Nat := 118140960795 + 5935656 * 2 ^ 59
def prefixEnd_5935656 : Nat := 4983230072969 + 3 ^ 40 * 5935656 * 2
def baseEnd_5935656 : Nat := 338649391971525994700269

theorem tailTrace_5935656 : CollatzResearch.WordTrace tailWord_5935656 prefixEnd_5935656 338649391971525994700269 := by
  unfold tailWord_5935656
  simp only [CollatzResearch.WordTrace]
  refine ⟨108245579892069758091397411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144327439856093010788529881 108245579892069758091397411)
  ·
    refine ⟨162368369838104637137096117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108245579892069758091397411 162368369838104637137096117)
    ·
      refine ⟨15222034672322309731602761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162368369838104637137096117 15222034672322309731602761)
      ·
        refine ⟨11416526004241732298702071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15222034672322309731602761 11416526004241732298702071)
        ·
          refine ⟨17124789006362598448053107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11416526004241732298702071 17124789006362598448053107)
          ·
            refine ⟨25687183509543897672079661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17124789006362598448053107 25687183509543897672079661)
            ·
              refine ⟨9632693816078961627029873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25687183509543897672079661 9632693816078961627029873)
              ·
                refine ⟨7224520362059221220272405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9632693816078961627029873 7224520362059221220272405)
                ·
                  refine ⟨338649391971525994700269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7224520362059221220272405 338649391971525994700269)
                  ·
                    rfl

theorem cell23_5935656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_5935656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935656 prefixEnd_5935656 := by exact prefixLift 5935656
  have htrace : WordTrace (prefixWord ++ tailWord_5935656) baseStart_5935656 baseEnd_5935656 := by
    simpa [prefixWord, tailWord_5935656, baseEnd_5935656] using wordTrace_append hprefix tailTrace_5935656
  have hstable : (prefixWord ++ tailWord_5935656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935656).length < 2 ^ (prefixWord ++ tailWord_5935656).sum := by decide
  have hdescent : baseEnd_5935656 < baseStart_5935656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935666 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_5935666 : Nat := 118140960795 + 5935666 * 2 ^ 59
def prefixEnd_5935666 : Nat := 4983230072969 + 3 ^ 40 * 5935666 * 2
def baseEnd_5935666 : Nat := 3047849662550278913177375

theorem tailTrace_5935666 : CollatzResearch.WordTrace tailWord_5935666 prefixEnd_5935666 3047849662550278913177375 := by
  unfold tailWord_5935666
  simp only [CollatzResearch.WordTrace]
  refine ⟨54122881128525821972664713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144327683009402191927105901 54122881128525821972664713)
  ·
    refine ⟨40592160846394366479498535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54122881128525821972664713 40592160846394366479498535)
    ·
      refine ⟨60888241269591549719247803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40592160846394366479498535 60888241269591549719247803)
      ·
        refine ⟨91332361904387324578871705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60888241269591549719247803 91332361904387324578871705)
        ·
          refine ⟨68499271428290493434153779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91332361904387324578871705 68499271428290493434153779)
          ·
            refine ⟨102748907142435740151230669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68499271428290493434153779 102748907142435740151230669)
            ·
              refine ⟨38530840178413402556711501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102748907142435740151230669 38530840178413402556711501)
              ·
                refine ⟨14449065066905025958766813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38530840178413402556711501 14449065066905025958766813)
                ·
                  refine ⟨5418399400089384734537555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14449065066905025958766813 5418399400089384734537555)
                  ·
                    refine ⟨8127599100134077101806333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418399400089384734537555 8127599100134077101806333)
                    ·
                      refine ⟨3047849662550278913177375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127599100134077101806333 3047849662550278913177375)
                      ·
                        rfl

theorem cell23_5935666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_5935666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935666 prefixEnd_5935666 := by exact prefixLift 5935666
  have htrace : WordTrace (prefixWord ++ tailWord_5935666) baseStart_5935666 baseEnd_5935666 := by
    simpa [prefixWord, tailWord_5935666, baseEnd_5935666] using wordTrace_append hprefix tailTrace_5935666
  have hstable : (prefixWord ++ tailWord_5935666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935666).length < 2 ^ (prefixWord ++ tailWord_5935666).sum := by decide
  have hdescent : baseEnd_5935666 < baseStart_5935666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935676 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_5935676 : Nat := 118140960795 + 5935676 * 2 ^ 59
def prefixEnd_5935676 : Nat := 4983230072969 + 3 ^ 40 * 5935676 * 2
def baseEnd_5935676 : Nat := 3047854797356823874052329

theorem tailTrace_5935676 : CollatzResearch.WordTrace tailWord_5935676 prefixEnd_5935676 3047854797356823874052329 := by
  unfold tailWord_5935676
  simp only [CollatzResearch.WordTrace]
  refine ⟨108245944622033529799261441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144327926162711373065681921 108245944622033529799261441)
  ·
    refine ⟨81184458466525147349446081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108245944622033529799261441 81184458466525147349446081)
    ·
      refine ⟨60888343849893860512084561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81184458466525147349446081 60888343849893860512084561)
      ·
        refine ⟨45666257887420395384063421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60888343849893860512084561 45666257887420395384063421)
        ·
          refine ⟨17124846707782648269023783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45666257887420395384063421 17124846707782648269023783)
          ·
            refine ⟨25687270061673972403535675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17124846707782648269023783 25687270061673972403535675)
            ·
              refine ⟨38530905092510958605303513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25687270061673972403535675 38530905092510958605303513)
              ·
                refine ⟨28898178819383218953977635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38530905092510958605303513 28898178819383218953977635)
                ·
                  refine ⟨43347268229074828430966453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28898178819383218953977635 43347268229074828430966453)
                  ·
                    refine ⟨4063806396475765165403105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43347268229074828430966453 4063806396475765165403105)
                    ·
                      refine ⟨3047854797356823874052329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063806396475765165403105 3047854797356823874052329)
                      ·
                        rfl

theorem cell23_5935676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_5935676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935676 prefixEnd_5935676 := by exact prefixLift 5935676
  have htrace : WordTrace (prefixWord ++ tailWord_5935676) baseStart_5935676 baseEnd_5935676 := by
    simpa [prefixWord, tailWord_5935676, baseEnd_5935676] using wordTrace_append hprefix tailTrace_5935676
  have hstable : (prefixWord ++ tailWord_5935676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935676).length < 2 ^ (prefixWord ++ tailWord_5935676).sum := by decide
  have hdescent : baseEnd_5935676 < baseStart_5935676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935693 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_5935693 : Nat := 118140960795 + 5935693 * 2 ^ 59
def prefixEnd_5935693 : Nat := 4983230072969 + 3 ^ 40 * 5935693 * 2
def baseEnd_5935693 : Nat := 3047863526527950307539751

theorem tailTrace_5935693 : CollatzResearch.WordTrace tailWord_5935693 prefixEnd_5935693 3047863526527950307539751 := by
  unfold tailWord_5935693
  simp only [CollatzResearch.WordTrace]
  refine ⟨216492509285005471501891733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144328339523336981001261155 216492509285005471501891733)
  ·
    refine ⟨10148086372734631476651175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216492509285005471501891733 10148086372734631476651175)
    ·
      refine ⟨15222129559101947214976763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10148086372734631476651175 15222129559101947214976763)
      ·
        refine ⟨22833194338652920822465145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15222129559101947214976763 22833194338652920822465145)
        ·
          refine ⟨17124895753989690616848859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22833194338652920822465145 17124895753989690616848859)
          ·
            refine ⟨25687343630984535925273289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17124895753989690616848859 25687343630984535925273289)
            ·
              refine ⟨19265507723238401943954967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25687343630984535925273289 19265507723238401943954967)
              ·
                refine ⟨28898261584857602915932451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19265507723238401943954967 28898261584857602915932451)
                ·
                  refine ⟨43347392377286404373898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28898261584857602915932451 43347392377286404373898677)
                  ·
                    refine ⟨4063818035370600410053001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43347392377286404373898677 4063818035370600410053001)
                    ·
                      refine ⟨3047863526527950307539751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4063818035370600410053001 3047863526527950307539751)
                      ·
                        rfl

theorem cell23_5935693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_5935693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935693 prefixEnd_5935693 := by exact prefixLift 5935693
  have htrace : WordTrace (prefixWord ++ tailWord_5935693) baseStart_5935693 baseEnd_5935693 := by
    simpa [prefixWord, tailWord_5935693, baseEnd_5935693] using wordTrace_append hprefix tailTrace_5935693
  have hstable : (prefixWord ++ tailWord_5935693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935693).length < 2 ^ (prefixWord ++ tailWord_5935693).sum := by decide
  have hdescent : baseEnd_5935693 < baseStart_5935693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935700 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_5935700 : Nat := 118140960795 + 5935700 * 2 ^ 59
def prefixEnd_5935700 : Nat := 4983230072969 + 3 ^ 40 * 5935700 * 2
def baseEnd_5935700 : Nat := 3047867120892531780152219

theorem tailTrace_5935700 : CollatzResearch.WordTrace tailWord_5935700 prefixEnd_5935700 3047867120892531780152219 := by
  unfold tailWord_5935700
  simp only [CollatzResearch.WordTrace]
  refine ⟨108246382297990055848698277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144328509730653407798264369 108246382297990055848698277)
  ·
    refine ⟨20296196680873135471630927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108246382297990055848698277 20296196680873135471630927)
    ·
      refine ⟨30444295021309703207446391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20296196680873135471630927 30444295021309703207446391)
      ·
        refine ⟨45666442531964554811169587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30444295021309703207446391 45666442531964554811169587)
        ·
          refine ⟨68499663797946832216754381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45666442531964554811169587 68499663797946832216754381)
          ·
            refine ⟨25687373924230062081282893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68499663797946832216754381 25687373924230062081282893)
            ·
              refine ⟨9632765221586273280481085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25687373924230062081282893 9632765221586273280481085)
              ·
                refine ⟨3612286958094852480180407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9632765221586273280481085 3612286958094852480180407)
                ·
                  refine ⟨5418430437142278720270611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612286958094852480180407 5418430437142278720270611)
                  ·
                    refine ⟨8127645655713418080405917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418430437142278720270611 8127645655713418080405917)
                    ·
                      refine ⟨3047867120892531780152219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127645655713418080405917 3047867120892531780152219)
                      ·
                        rfl

theorem cell23_5935700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_5935700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935700 prefixEnd_5935700 := by exact prefixLift 5935700
  have htrace : WordTrace (prefixWord ++ tailWord_5935700) baseStart_5935700 baseEnd_5935700 := by
    simpa [prefixWord, tailWord_5935700, baseEnd_5935700] using wordTrace_append hprefix tailTrace_5935700
  have hstable : (prefixWord ++ tailWord_5935700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935700).length < 2 ^ (prefixWord ++ tailWord_5935700).sum := by decide
  have hdescent : baseEnd_5935700 < baseStart_5935700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935712 : List Nat := [2, 1, 1, 3, 2, 1, 13]
def baseStart_5935712 : Nat := 118140960795 + 5935712 * 2 ^ 59
def prefixEnd_5935712 : Nat := 4983230072969 + 3 ^ 40 * 5935712 * 2
def baseEnd_5935712 : Nat := 37628065218029453496323

theorem tailTrace_5935712 : CollatzResearch.WordTrace tailWord_5935712 prefixEnd_5935712 37628065218029453496323 := by
  unfold tailWord_5935712
  simp only [CollatzResearch.WordTrace]
  refine ⟨108246601135968318873416695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144328801514624425164555593 108246601135968318873416695)
  ·
    refine ⟨162369901703952478310125043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108246601135968318873416695 162369901703952478310125043)
    ·
      refine ⟨243554852555928717465187565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162369901703952478310125043 243554852555928717465187565)
      ·
        refine ⟨91333069708473269049445337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243554852555928717465187565 91333069708473269049445337)
        ·
          refine ⟨68499802281354951787084003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91333069708473269049445337 68499802281354951787084003)
          ·
            refine ⟨102749703422032427680626005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68499802281354951787084003 102749703422032427680626005)
            ·
              refine ⟨37628065218029453496323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 102749703422032427680626005 37628065218029453496323)
              ·
                rfl

theorem cell23_5935712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 13].length) (baseStart_5935712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935712 prefixEnd_5935712 := by exact prefixLift 5935712
  have htrace : WordTrace (prefixWord ++ tailWord_5935712) baseStart_5935712 baseEnd_5935712 := by
    simpa [prefixWord, tailWord_5935712, baseEnd_5935712] using wordTrace_append hprefix tailTrace_5935712
  have hstable : (prefixWord ++ tailWord_5935712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935712).length < 2 ^ (prefixWord ++ tailWord_5935712).sum := by decide
  have hdescent : baseEnd_5935712 < baseStart_5935712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935716 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_5935716 : Nat := 118140960795 + 5935716 * 2 ^ 59
def prefixEnd_5935716 : Nat := 4983230072969 + 3 ^ 40 * 5935716 * 2
def baseEnd_5935716 : Nat := 1015958445527667905850715

theorem tailTrace_5935716 : CollatzResearch.WordTrace tailWord_5935716 prefixEnd_5935716 1015958445527667905850715 := by
  unfold tailWord_5935716
  simp only [CollatzResearch.WordTrace]
  refine ⟨108246674081961073214989501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144328898775948097619986001 108246674081961073214989501)
  ·
    refine ⟨40592502780735402455621063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108246674081961073214989501 40592502780735402455621063)
    ·
      refine ⟨60888754171103103683431595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40592502780735402455621063 60888754171103103683431595)
      ·
        refine ⟨91333131256654655525147393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60888754171103103683431595 91333131256654655525147393)
        ·
          refine ⟨68499848442490991643860545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91333131256654655525147393 68499848442490991643860545)
          ·
            refine ⟨51374886331868243732895409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68499848442490991643860545 51374886331868243732895409)
            ·
              refine ⟨38531164748901182799671557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51374886331868243732895409 38531164748901182799671557)
              ·
                refine ⟨7224593390418971774938417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38531164748901182799671557 7224593390418971774938417)
                ·
                  refine ⟨5418445042814228831203813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7224593390418971774938417 5418445042814228831203813)
                  ·
                    refine ⟨1015958445527667905850715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418445042814228831203813 1015958445527667905850715)
                    ·
                      rfl

theorem cell23_5935716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_5935716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935716 prefixEnd_5935716 := by exact prefixLift 5935716
  have htrace : WordTrace (prefixWord ++ tailWord_5935716) baseStart_5935716 baseEnd_5935716 := by
    simpa [prefixWord, tailWord_5935716, baseEnd_5935716] using wordTrace_append hprefix tailTrace_5935716
  have hstable : (prefixWord ++ tailWord_5935716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935716).length < 2 ^ (prefixWord ++ tailWord_5935716).sum := by decide
  have hdescent : baseEnd_5935716 < baseStart_5935716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935717 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 1, 1, 3]
def baseStart_5935717 : Nat := 118140960795 + 5935717 * 2 ^ 59
def prefixEnd_5935717 : Nat := 4983230072969 + 3 ^ 40 * 5935717 * 2
def baseEnd_5935717 : Nat := 3047875850063658213639641

theorem tailTrace_5935717 : CollatzResearch.WordTrace tailWord_5935717 prefixEnd_5935717 3047875850063658213639641 := by
  unfold tailWord_5935717
  simp only [CollatzResearch.WordTrace]
  refine ⟨216493384636918523600765405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144328923091279015733843603 216493384636918523600765405)
  ·
    refine ⟨81185019238844446350287027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216493384636918523600765405 81185019238844446350287027)
    ·
      refine ⟨121777528858266669525430541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81185019238844446350287027 121777528858266669525430541)
      ·
        refine ⟨45666573321850001072036453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121777528858266669525430541 45666573321850001072036453)
        ·
          refine ⟨8562482497846875201006835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45666573321850001072036453 8562482497846875201006835)
          ·
            refine ⟨12843723746770312801510253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562482497846875201006835 12843723746770312801510253)
            ·
              refine ⟨4816396405038867300566345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12843723746770312801510253 4816396405038867300566345)
              ·
                refine ⟨3612297303779150475424759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4816396405038867300566345 3612297303779150475424759)
                ·
                  refine ⟨5418445955668725713137139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612297303779150475424759 5418445955668725713137139)
                  ·
                    refine ⟨8127668933503088569705709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418445955668725713137139 8127668933503088569705709)
                    ·
                      refine ⟨3047875850063658213639641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127668933503088569705709 3047875850063658213639641)
                      ·
                        rfl

theorem cell23_5935717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_5935717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935717 prefixEnd_5935717 := by exact prefixLift 5935717
  have htrace : WordTrace (prefixWord ++ tailWord_5935717) baseStart_5935717 baseEnd_5935717 := by
    simpa [prefixWord, tailWord_5935717, baseEnd_5935717] using wordTrace_append hprefix tailTrace_5935717
  have hstable : (prefixWord ++ tailWord_5935717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935717).length < 2 ^ (prefixWord ++ tailWord_5935717).sum := by decide
  have hdescent : baseEnd_5935717 < baseStart_5935717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935726 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5935726 : Nat := 118140960795 + 5935726 * 2 ^ 59
def prefixEnd_5935726 : Nat := 4983230072969 + 3 ^ 40 * 5935726 * 2
def baseEnd_5935726 : Nat := 3047880471389548678427099

theorem tailTrace_5935726 : CollatzResearch.WordTrace tailWord_5935726 prefixEnd_5935726 3047880471389548678427099 := by
  unfold tailWord_5935726
  simp only [CollatzResearch.WordTrace]
  refine ⟨27061714111735739767230379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144329141929257278758562021 27061714111735739767230379)
  ·
    refine ⟨40592571167603609650845569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27061714111735739767230379 40592571167603609650845569)
    ·
      refine ⟨30444428375702707238134177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40592571167603609650845569 30444428375702707238134177)
      ·
        refine ⟨22833321281777030428600633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30444428375702707238134177 22833321281777030428600633)
        ·
          refine ⟨17124990961332772821450475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22833321281777030428600633 17124990961332772821450475)
          ·
            refine ⟨25687486441999159232175713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17124990961332772821450475 25687486441999159232175713)
            ·
              refine ⟨19265614831499369424131785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25687486441999159232175713 19265614831499369424131785)
              ·
                refine ⟨14449211123624527068098839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19265614831499369424131785 14449211123624527068098839)
                ·
                  refine ⟨21673816685436790602148259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14449211123624527068098839 21673816685436790602148259)
                  ·
                    refine ⟨32510725028155185903222389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21673816685436790602148259 32510725028155185903222389)
                    ·
                      refine ⟨3047880471389548678427099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32510725028155185903222389 3047880471389548678427099)
                      ·
                        rfl

theorem cell23_5935726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5935726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935726 prefixEnd_5935726 := by exact prefixLift 5935726
  have htrace : WordTrace (prefixWord ++ tailWord_5935726) baseStart_5935726 baseEnd_5935726 := by
    simpa [prefixWord, tailWord_5935726, baseEnd_5935726] using wordTrace_append hprefix tailTrace_5935726
  have hstable : (prefixWord ++ tailWord_5935726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935726).length < 2 ^ (prefixWord ++ tailWord_5935726).sum := by decide
  have hdescent : baseEnd_5935726 < baseStart_5935726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935756 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_5935756 : Nat := 118140960795 + 5935756 * 2 ^ 59
def prefixEnd_5935756 : Nat := 4983230072969 + 3 ^ 40 * 5935756 * 2
def baseEnd_5935756 : Nat := 3047895875809183561051961

theorem tailTrace_5935756 : CollatzResearch.WordTrace tailWord_5935756 prefixEnd_5935756 3047895875809183561051961 := by
  unfold tailWord_5935756
  simp only [CollatzResearch.WordTrace]
  refine ⟨108247403541888616630717561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144329871389184822174290081 108247403541888616630717561)
  ·
    refine ⟨81185552656416462473038171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108247403541888616630717561 81185552656416462473038171)
    ·
      refine ⟨121778328984624693709557257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81185552656416462473038171 121778328984624693709557257)
      ·
        refine ⟨91333746738468520282167943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121778328984624693709557257 91333746738468520282167943)
        ·
          refine ⟨137000620107702780423251915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91333746738468520282167943 137000620107702780423251915)
          ·
            refine ⟨205500930161554170634877873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137000620107702780423251915 205500930161554170634877873)
            ·
              refine ⟨154125697621165627976158405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205500930161554170634877873 154125697621165627976158405)
              ·
                refine ⟨28898568303968555245529701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154125697621165627976158405 28898568303968555245529701)
                ·
                  refine ⟨5418481556994104108536819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28898568303968555245529701 5418481556994104108536819)
                  ·
                    refine ⟨8127722335491156162805229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418481556994104108536819 8127722335491156162805229)
                    ·
                      refine ⟨3047895875809183561051961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127722335491156162805229 3047895875809183561051961)
                      ·
                        rfl

theorem cell23_5935756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_5935756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935756 prefixEnd_5935756 := by exact prefixLift 5935756
  have htrace : WordTrace (prefixWord ++ tailWord_5935756) baseStart_5935756 baseEnd_5935756 := by
    simpa [prefixWord, tailWord_5935756, baseEnd_5935756] using wordTrace_append hprefix tailTrace_5935756
  have hstable : (prefixWord ++ tailWord_5935756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935756).length < 2 ^ (prefixWord ++ tailWord_5935756).sum := by decide
  have hdescent : baseEnd_5935756 < baseStart_5935756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935773 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_5935773 : Nat := 118140960795 + 5935773 * 2 ^ 59
def prefixEnd_5935773 : Nat := 4983230072969 + 3 ^ 40 * 5935773 * 2
def baseEnd_5935773 : Nat := 3047904604980309994539383

theorem tailTrace_5935773 : CollatzResearch.WordTrace tailWord_5935773 prefixEnd_5935773 3047904604980309994539383 := by
  unfold tailWord_5935773
  simp only [CollatzResearch.WordTrace]
  refine ⟨216495427124715645164803973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144330284749810430109869315 216495427124715645164803973)
  ·
    refine ⟨40592892585884183468400745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216495427124715645164803973 40592892585884183468400745)
    ·
      refine ⟨30444669439413137601300559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40592892585884183468400745 30444669439413137601300559)
      ·
        refine ⟨45667004159119706401950839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30444669439413137601300559 45667004159119706401950839)
        ·
          refine ⟨68500506238679559602926259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45667004159119706401950839 68500506238679559602926259)
          ·
            refine ⟨102750759358019339404389389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68500506238679559602926259 102750759358019339404389389)
            ·
              refine ⟨38531534759257252276646021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102750759358019339404389389 38531534759257252276646021)
              ·
                refine ⟨7224662767360734801871129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38531534759257252276646021 7224662767360734801871129)
                ·
                  refine ⟨5418497075520551101403347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7224662767360734801871129 5418497075520551101403347)
                  ·
                    refine ⟨8127745613280826652105021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418497075520551101403347 8127745613280826652105021)
                    ·
                      refine ⟨3047904604980309994539383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127745613280826652105021 3047904604980309994539383)
                      ·
                        rfl

theorem cell23_5935773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_5935773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935773 prefixEnd_5935773 := by exact prefixLift 5935773
  have htrace : WordTrace (prefixWord ++ tailWord_5935773) baseStart_5935773 baseEnd_5935773 := by
    simpa [prefixWord, tailWord_5935773, baseEnd_5935773] using wordTrace_append hprefix tailTrace_5935773
  have hstable : (prefixWord ++ tailWord_5935773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935773).length < 2 ^ (prefixWord ++ tailWord_5935773).sum := by decide
  have hdescent : baseEnd_5935773 < baseStart_5935773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935790 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5935790 : Nat := 118140960795 + 5935790 * 2 ^ 59
def prefixEnd_5935790 : Nat := 4983230072969 + 3 ^ 40 * 5935790 * 2
def baseEnd_5935790 : Nat := 3047913334151436428026805

theorem tailTrace_5935790 : CollatzResearch.WordTrace tailWord_5935790 prefixEnd_5935790 3047913334151436428026805 := by
  unfold tailWord_5935790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062005895706757133521603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144330698110436038045448549 27062005895706757133521603)
  ·
    refine ⟨40593008843560135700282405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27062005895706757133521603 40593008843560135700282405)
    ·
      refine ⟨7611189158167525443802951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40593008843560135700282405 7611189158167525443802951)
      ·
        refine ⟨11416783737251288165704427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611189158167525443802951 11416783737251288165704427)
        ·
          refine ⟨17125175605876932248556641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11416783737251288165704427 17125175605876932248556641)
          ·
            refine ⟨12843881704407699186417481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17125175605876932248556641 12843881704407699186417481)
            ·
              refine ⟨9632911278305774389813111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12843881704407699186417481 9632911278305774389813111)
              ·
                refine ⟨14449366917458661584719667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9632911278305774389813111 14449366917458661584719667)
                ·
                  refine ⟨21674050376187992377079501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14449366917458661584719667 21674050376187992377079501)
                  ·
                    refine ⟨8127768891070497141404813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21674050376187992377079501 8127768891070497141404813)
                    ·
                      refine ⟨3047913334151436428026805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127768891070497141404813 3047913334151436428026805)
                      ·
                        rfl

theorem cell23_5935790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5935790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935790 prefixEnd_5935790 := by exact prefixLift 5935790
  have htrace : WordTrace (prefixWord ++ tailWord_5935790) baseStart_5935790 baseEnd_5935790 := by
    simpa [prefixWord, tailWord_5935790, baseEnd_5935790] using wordTrace_append hprefix tailTrace_5935790
  have hstable : (prefixWord ++ tailWord_5935790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935790).length < 2 ^ (prefixWord ++ tailWord_5935790).sum := by decide
  have hdescent : baseEnd_5935790 < baseStart_5935790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935849 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_5935849 : Nat := 118140960795 + 5935849 * 2 ^ 59
def prefixEnd_5935849 : Nat := 4983230072969 + 3 ^ 40 * 5935849 * 2
def baseEnd_5935849 : Nat := 1015981209836683899063011

theorem tailTrace_5935849 : CollatzResearch.WordTrace tailWord_5935849 prefixEnd_5935849 1015981209836683899063011 := by
  unfold tailWord_5935849
  simp only [CollatzResearch.WordTrace]
  refine ⟨216498199072440310144570601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144332132714960206763047067 216498199072440310144570601)
  ·
    refine ⟨162373649304330232608427951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216498199072440310144570601 162373649304330232608427951)
    ·
      refine ⟨243560473956495348912641927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162373649304330232608427951 243560473956495348912641927)
      ·
        refine ⟨365340710934743023368962891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243560473956495348912641927 365340710934743023368962891)
        ·
          refine ⟨548011066402114535053444337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365340710934743023368962891 548011066402114535053444337)
          ·
            refine ⟨411008299801585901290083253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548011066402114535053444337 411008299801585901290083253)
            ·
              refine ⟨38532028106398678245945305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411008299801585901290083253 38532028106398678245945305)
              ·
                refine ⟨28899021079799008684458979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38532028106398678245945305 28899021079799008684458979)
                ·
                  refine ⟨43348531619698513026688469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28899021079799008684458979 43348531619698513026688469)
                  ·
                    refine ⟨1015981209836683899063011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43348531619698513026688469 1015981209836683899063011)
                    ·
                      rfl

theorem cell23_5935849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_5935849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935849 prefixEnd_5935849 := by exact prefixLift 5935849
  have htrace : WordTrace (prefixWord ++ tailWord_5935849) baseStart_5935849 baseEnd_5935849 := by
    simpa [prefixWord, tailWord_5935849, baseEnd_5935849] using wordTrace_append hprefix tailTrace_5935849
  have hstable : (prefixWord ++ tailWord_5935849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935849).length < 2 ^ (prefixWord ++ tailWord_5935849).sum := by decide
  have hdescent : baseEnd_5935849 < baseStart_5935849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935859 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_5935859 : Nat := 118140960795 + 5935859 * 2 ^ 59
def prefixEnd_5935859 : Nat := 4983230072969 + 3 ^ 40 * 5935859 * 2
def baseEnd_5935859 : Nat := 3047948764316596658063987

theorem tailTrace_5935859 : CollatzResearch.WordTrace tailWord_5935859 prefixEnd_5935859 3047948764316596658063987 := by
  unfold tailWord_5935859
  simp only [CollatzResearch.WordTrace]
  refine ⟨216498563802404081852434631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144332375868269387901623087 216498563802404081852434631)
  ·
    refine ⟨324747845703606122778651947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216498563802404081852434631 324747845703606122778651947)
    ·
      refine ⟨487121768555409184167977921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324747845703606122778651947 487121768555409184167977921)
      ·
        refine ⟨365341326416556888125983441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487121768555409184167977921 365341326416556888125983441)
        ·
          refine ⟨274005994812417666094487581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365341326416556888125983441 274005994812417666094487581)
          ·
            refine ⟨102752248054656624785432843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274005994812417666094487581 102752248054656624785432843)
            ·
              refine ⟨154128372081984937178149265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102752248054656624785432843 154128372081984937178149265)
              ·
                refine ⟨115596279061488702883611949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154128372081984937178149265 115596279061488702883611949)
                ·
                  refine ⟨43348604648058263581354481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115596279061488702883611949 43348604648058263581354481)
                  ·
                    refine ⟨32511453486043697686015861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43348604648058263581354481 32511453486043697686015861)
                    ·
                      refine ⟨3047948764316596658063987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32511453486043697686015861 3047948764316596658063987)
                      ·
                        rfl

theorem cell23_5935859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_5935859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935859 prefixEnd_5935859 := by exact prefixLift 5935859
  have htrace : WordTrace (prefixWord ++ tailWord_5935859) baseStart_5935859 baseEnd_5935859 := by
    simpa [prefixWord, tailWord_5935859, baseEnd_5935859] using wordTrace_append hprefix tailTrace_5935859
  have hstable : (prefixWord ++ tailWord_5935859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935859).length < 2 ^ (prefixWord ++ tailWord_5935859).sum := by decide
  have hdescent : baseEnd_5935859 < baseStart_5935859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935870 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_5935870 : Nat := 118140960795 + 5935870 * 2 ^ 59
def prefixEnd_5935870 : Nat := 4983230072969 + 3 ^ 40 * 5935870 * 2
def baseEnd_5935870 : Nat := 338661601400421790558493

theorem tailTrace_5935870 : CollatzResearch.WordTrace tailWord_5935870 prefixEnd_5935870 338661601400421790558493 := by
  unfold tailWord_5935870
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062370625670528841385633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144332643336909487154056709 27062370625670528841385633)
  ·
    refine ⟨20296777969252896631039225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27062370625670528841385633 20296777969252896631039225)
    ·
      refine ⟨15222583476939672473279419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20296777969252896631039225 15222583476939672473279419)
      ·
        refine ⟨22833875215409508709919129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15222583476939672473279419 22833875215409508709919129)
        ·
          refine ⟨17125406411557131532439347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22833875215409508709919129 17125406411557131532439347)
          ·
            refine ⟨25688109617335697298659021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17125406411557131532439347 25688109617335697298659021)
            ·
              refine ⟨9633041106500886486997133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25688109617335697298659021 9633041106500886486997133)
              ·
                refine ⟨3612390414937832432623925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9633041106500886486997133 3612390414937832432623925)
                ·
                  refine ⟨338661601400421790558493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3612390414937832432623925 338661601400421790558493)
                  ·
                    rfl

theorem cell23_5935870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_5935870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935870 prefixEnd_5935870 := by exact prefixLift 5935870
  have htrace : WordTrace (prefixWord ++ tailWord_5935870) baseStart_5935870 baseEnd_5935870 := by
    simpa [prefixWord, tailWord_5935870, baseEnd_5935870] using wordTrace_append hprefix tailTrace_5935870
  have hstable : (prefixWord ++ tailWord_5935870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935870).length < 2 ^ (prefixWord ++ tailWord_5935870).sum := by decide
  have hdescent : baseEnd_5935870 < baseStart_5935870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935876 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5935876 : Nat := 118140960795 + 5935876 * 2 ^ 59
def prefixEnd_5935876 : Nat := 4983230072969 + 3 ^ 40 * 5935876 * 2
def baseEnd_5935876 : Nat := 3047957493487723091551409

theorem tailTrace_5935876 : CollatzResearch.WordTrace tailWord_5935876 prefixEnd_5935876 3047957493487723091551409 := by
  unfold tailWord_5935876
  simp only [CollatzResearch.WordTrace]
  refine ⟨108249591921671246877901741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144332789228894995837202321 108249591921671246877901741)
  ·
    refine ⟨40593596970626717579213153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108249591921671246877901741 40593596970626717579213153)
    ·
      refine ⟨30445197727970038184409865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40593596970626717579213153 30445197727970038184409865)
      ·
        refine ⟨22833898295977528638307399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30445197727970038184409865 22833898295977528638307399)
        ·
          refine ⟨34250847443966292957461099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22833898295977528638307399 34250847443966292957461099)
          ·
            refine ⟨51376271165949439436191649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34250847443966292957461099 51376271165949439436191649)
            ·
              refine ⟨38532203374462079577143737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51376271165949439436191649 38532203374462079577143737)
              ·
                refine ⟨28899152530846559682857803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38532203374462079577143737 28899152530846559682857803)
                ·
                  refine ⟨43348728796269839524286705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28899152530846559682857803 43348728796269839524286705)
                  ·
                    refine ⟨32511546597202379643215029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43348728796269839524286705 32511546597202379643215029)
                    ·
                      refine ⟨3047957493487723091551409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32511546597202379643215029 3047957493487723091551409)
                      ·
                        rfl

theorem cell23_5935876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5935876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935876 prefixEnd_5935876 := by exact prefixLift 5935876
  have htrace : WordTrace (prefixWord ++ tailWord_5935876) baseStart_5935876 baseEnd_5935876 := by
    simpa [prefixWord, tailWord_5935876, baseEnd_5935876] using wordTrace_append hprefix tailTrace_5935876
  have hstable : (prefixWord ++ tailWord_5935876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935876).length < 2 ^ (prefixWord ++ tailWord_5935876).sum := by decide
  have hdescent : baseEnd_5935876 < baseStart_5935876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935917 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5935917 : Nat := 118140960795 + 5935917 * 2 ^ 59
def prefixEnd_5935917 : Nat := 4983230072969 + 3 ^ 40 * 5935917 * 2
def baseEnd_5935917 : Nat := 1015992848731519143712907

theorem tailTrace_5935917 : CollatzResearch.WordTrace tailWord_5935917 prefixEnd_5935917 1015992848731519143712907 := by
  unfold tailWord_5935917
  simp only [CollatzResearch.WordTrace]
  refine ⟨216500679236193957758046005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144333786157462638505364003 216500679236193957758046005)
  ·
    refine ⟨20296938678393183539816813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216500679236193957758046005 20296938678393183539816813)
    ·
      refine ⟨7611352004397443827431305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20296938678393183539816813 7611352004397443827431305)
      ·
        refine ⟨5708514003298082870573479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611352004397443827431305 5708514003298082870573479)
        ·
          refine ⟨8562771004947124305860219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708514003298082870573479 8562771004947124305860219)
          ·
            refine ⟨12844156507420686458790329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562771004947124305860219 12844156507420686458790329)
            ·
              refine ⟨9633117380565514844092747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12844156507420686458790329 9633117380565514844092747)
              ·
                refine ⟨14449676070848272266139121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633117380565514844092747 14449676070848272266139121)
                ·
                  refine ⟨10837257053136204199604341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14449676070848272266139121 10837257053136204199604341)
                  ·
                    refine ⟨1015992848731519143712907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10837257053136204199604341 1015992848731519143712907)
                    ·
                      rfl

theorem cell23_5935917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5935917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935917 prefixEnd_5935917 := by exact prefixLift 5935917
  have htrace : WordTrace (prefixWord ++ tailWord_5935917) baseStart_5935917 baseEnd_5935917 := by
    simpa [prefixWord, tailWord_5935917, baseEnd_5935917] using wordTrace_append hprefix tailTrace_5935917
  have hstable : (prefixWord ++ tailWord_5935917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935917).length < 2 ^ (prefixWord ++ tailWord_5935917).sum := by decide
  have hdescent : baseEnd_5935917 < baseStart_5935917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935919 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_5935919 : Nat := 118140960795 + 5935919 * 2 ^ 59
def prefixEnd_5935919 : Nat := 4983230072969 + 3 ^ 40 * 5935919 * 2
def baseEnd_5935919 : Nat := 3047979573155866423313711

theorem tailTrace_5935919 : CollatzResearch.WordTrace tailWord_5935919 prefixEnd_5935919 3047979573155866423313711 := by
  unfold tailWord_5935919
  simp only [CollatzResearch.WordTrace]
  refine ⟨216500752182186712099618811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144333834788124474733079207 216500752182186712099618811)
  ·
    refine ⟨324751128273280068149428217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216500752182186712099618811 324751128273280068149428217)
    ·
      refine ⟨243563346204960051112071163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324751128273280068149428217 243563346204960051112071163)
      ·
        refine ⟨365345019307440076668106745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243563346204960051112071163 365345019307440076668106745)
        ·
          refine ⟨274008764480580057501080059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365345019307440076668106745 274008764480580057501080059)
          ·
            refine ⟨411013146720870086251620089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274008764480580057501080059 411013146720870086251620089)
            ·
              refine ⟨308259860040652564688715067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411013146720870086251620089 308259860040652564688715067)
              ·
                refine ⟨462389790060978847033072601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308259860040652564688715067 462389790060978847033072601)
                ·
                  refine ⟨346792342545734135274804451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462389790060978847033072601 346792342545734135274804451)
                  ·
                    refine ⟨520188513818601202912206677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346792342545734135274804451 520188513818601202912206677)
                    ·
                      refine ⟨3047979573155866423313711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 520188513818601202912206677 3047979573155866423313711)
                      ·
                        rfl

theorem cell23_5935919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_5935919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935919 prefixEnd_5935919 := by exact prefixLift 5935919
  have htrace : WordTrace (prefixWord ++ tailWord_5935919) baseStart_5935919 baseEnd_5935919 := by
    simpa [prefixWord, tailWord_5935919, baseEnd_5935919] using wordTrace_append hprefix tailTrace_5935919
  have hstable : (prefixWord ++ tailWord_5935919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935919).length < 2 ^ (prefixWord ++ tailWord_5935919).sum := by decide
  have hdescent : baseEnd_5935919 < baseStart_5935919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935923 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3]
def baseStart_5935923 : Nat := 118140960795 + 5935923 * 2 ^ 59
def prefixEnd_5935923 : Nat := 4983230072969 + 3 ^ 40 * 5935923 * 2
def baseEnd_5935923 : Nat := 3047981627078484407663693

theorem tailTrace_5935923 : CollatzResearch.WordTrace tailWord_5935923 prefixEnd_5935923 3047981627078484407663693 := by
  unfold tailWord_5935923
  simp only [CollatzResearch.WordTrace]
  refine ⟨216500898074172220782764423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144333932049448147188509615 216500898074172220782764423)
  ·
    refine ⟨324751347111258331174146635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216500898074172220782764423 324751347111258331174146635)
    ·
      refine ⟨487127020666887496761219953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324751347111258331174146635 487127020666887496761219953)
      ·
        refine ⟨365345265500165622570914965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487127020666887496761219953 365345265500165622570914965)
        ·
          refine ⟨17125559320320263558011639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 365345265500165622570914965 17125559320320263558011639)
          ·
            refine ⟨25688338980480395337017459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17125559320320263558011639 25688338980480395337017459)
            ·
              refine ⟨38532508470720593005526189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25688338980480395337017459 38532508470720593005526189)
              ·
                refine ⟨14449690676520222377072321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38532508470720593005526189 14449690676520222377072321)
                ·
                  refine ⟨10837268007390166782804241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14449690676520222377072321 10837268007390166782804241)
                  ·
                    refine ⟨8127951005542625087103181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10837268007390166782804241 8127951005542625087103181)
                    ·
                      refine ⟨3047981627078484407663693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8127951005542625087103181 3047981627078484407663693)
                      ·
                        rfl

theorem cell23_5935923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_5935923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935923 prefixEnd_5935923 := by exact prefixLift 5935923
  have htrace : WordTrace (prefixWord ++ tailWord_5935923) baseStart_5935923 baseEnd_5935923 := by
    simpa [prefixWord, tailWord_5935923, baseEnd_5935923] using wordTrace_append hprefix tailTrace_5935923
  have hstable : (prefixWord ++ tailWord_5935923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935923).length < 2 ^ (prefixWord ++ tailWord_5935923).sum := by decide
  have hdescent : baseEnd_5935923 < baseStart_5935923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5935996 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_5935996 : Nat := 118140960795 + 5935996 * 2 ^ 59
def prefixEnd_5935996 : Nat := 4983230072969 + 3 ^ 40 * 5935996 * 2
def baseEnd_5935996 : Nat := 3048019111166262622050857

theorem tailTrace_5935996 : CollatzResearch.WordTrace tailWord_5935996 prefixEnd_5935996 3048019111166262622050857 := by
  unfold tailWord_5935996
  simp only [CollatzResearch.WordTrace]
  refine ⟨108251780301453877125085921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144335707068605169500114561 108251780301453877125085921)
  ·
    refine ⟨81188835226090407843814441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108251780301453877125085921 81188835226090407843814441)
    ·
      refine ⟨60891626419567805882860831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81188835226090407843814441 60891626419567805882860831)
      ·
        refine ⟨91337439629351708824291247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60891626419567805882860831 91337439629351708824291247)
        ·
          refine ⟨137006159444027563236436871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91337439629351708824291247 137006159444027563236436871)
          ·
            refine ⟨205509239166041344854655307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137006159444027563236436871 205509239166041344854655307)
            ·
              refine ⟨308263858749062017281982961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205509239166041344854655307 308263858749062017281982961)
              ·
                refine ⟨231197894061796512961487221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308263858749062017281982961 231197894061796512961487221)
                ·
                  refine ⟨21674802568293423090139427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231197894061796512961487221 21674802568293423090139427)
                  ·
                    refine ⟨32512203852440134635209141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21674802568293423090139427 32512203852440134635209141)
                    ·
                      refine ⟨3048019111166262622050857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32512203852440134635209141 3048019111166262622050857)
                      ·
                        rfl

theorem cell23_5935996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_5935996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5935996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5935996 prefixEnd_5935996 := by exact prefixLift 5935996
  have htrace : WordTrace (prefixWord ++ tailWord_5935996) baseStart_5935996 baseEnd_5935996 := by
    simpa [prefixWord, tailWord_5935996, baseEnd_5935996] using wordTrace_append hprefix tailTrace_5935996
  have hstable : (prefixWord ++ tailWord_5935996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5935996).length < 2 ^ (prefixWord ++ tailWord_5935996).sum := by decide
  have hdescent : baseEnd_5935996 < baseStart_5935996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5935996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936003 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 4, 4]
def baseStart_5936003 : Nat := 118140960795 + 5936003 * 2 ^ 59
def prefixEnd_5936003 : Nat := 4983230072969 + 3 ^ 40 * 5936003 * 2
def baseEnd_5936003 : Nat := 1016007568510281364887775

theorem tailTrace_5936003 : CollatzResearch.WordTrace tailWord_5936003 prefixEnd_5936003 1016007568510281364887775 := by
  unfold tailWord_5936003
  simp only [CollatzResearch.WordTrace]
  refine ⟨216503815913882394445676663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144335877275921596297117775 216503815913882394445676663)
  ·
    refine ⟨324755723870823591668514995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216503815913882394445676663 324755723870823591668514995)
    ·
      refine ⟨487133585806235387502772493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324755723870823591668514995 487133585806235387502772493)
      ·
        refine ⟨182675094677338270313539685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487133585806235387502772493 182675094677338270313539685)
        ·
          refine ⟨34251580252000925683788691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182675094677338270313539685 34251580252000925683788691)
          ·
            refine ⟨51377370378001388525683037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34251580252000925683788691 51377370378001388525683037)
            ·
              refine ⟨19266513891750520697131139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51377370378001388525683037 19266513891750520697131139)
              ·
                refine ⟨28899770837625781045696709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19266513891750520697131139 28899770837625781045696709)
                ·
                  refine ⟨5418707032054833946068133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28899770837625781045696709 5418707032054833946068133)
                  ·
                    refine ⟨1016007568510281364887775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418707032054833946068133 1016007568510281364887775)
                    ·
                      rfl

theorem cell23_5936003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 4].length) (baseStart_5936003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936003 prefixEnd_5936003 := by exact prefixLift 5936003
  have htrace : WordTrace (prefixWord ++ tailWord_5936003) baseStart_5936003 baseEnd_5936003 := by
    simpa [prefixWord, tailWord_5936003, baseEnd_5936003] using wordTrace_append hprefix tailTrace_5936003
  have hstable : (prefixWord ++ tailWord_5936003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936003).length < 2 ^ (prefixWord ++ tailWord_5936003).sum := by decide
  have hdescent : baseEnd_5936003 < baseStart_5936003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936033 : List Nat := [1, 2, 3, 4, 1, 2, 1, 9]
def baseStart_5936033 : Nat := 118140960795 + 5936033 * 2 ^ 59
def prefixEnd_5936033 : Nat := 4983230072969 + 3 ^ 40 * 5936033 * 2
def baseEnd_5936033 : Nat := 112890300368536258418081

theorem tailTrace_5936033 : CollatzResearch.WordTrace tailWord_5936033 prefixEnd_5936033 112890300368536258418081 := by
  unfold tailWord_5936033
  simp only [CollatzResearch.WordTrace]
  refine ⟨216504910103773709569268753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144336606735849139712845835 216504910103773709569268753)
  ·
    refine ⟨162378682577830282176951565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216504910103773709569268753 162378682577830282176951565)
    ·
      refine ⟨60892005966686355816356837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162378682577830282176951565 60892005966686355816356837)
      ·
        refine ⟨11417251118753691715566907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60892005966686355816356837 11417251118753691715566907)
        ·
          refine ⟨17125876678130537573350361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417251118753691715566907 17125876678130537573350361)
          ·
            refine ⟨12844407508597903180012771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17125876678130537573350361 12844407508597903180012771)
            ·
              refine ⟨19266611262896854770019157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12844407508597903180012771 19266611262896854770019157)
              ·
                refine ⟨112890300368536258418081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19266611262896854770019157 112890300368536258418081)
                ·
                  rfl

theorem cell23_5936033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 9].length) (baseStart_5936033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936033 prefixEnd_5936033 := by exact prefixLift 5936033
  have htrace : WordTrace (prefixWord ++ tailWord_5936033) baseStart_5936033 baseEnd_5936033 := by
    simpa [prefixWord, tailWord_5936033, baseEnd_5936033] using wordTrace_append hprefix tailTrace_5936033
  have hstable : (prefixWord ++ tailWord_5936033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936033).length < 2 ^ (prefixWord ++ tailWord_5936033).sum := by decide
  have hdescent : baseEnd_5936033 < baseStart_5936033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936061 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_5936061 : Nat := 118140960795 + 5936061 * 2 ^ 59
def prefixEnd_5936061 : Nat := 4983230072969 + 3 ^ 40 * 5936061 * 2
def baseEnd_5936061 : Nat := 3048052487408804867738059

theorem tailTrace_5936061 : CollatzResearch.WordTrace tailWord_5936061 prefixEnd_5936061 3048052487408804867738059 := by
  unfold tailWord_5936061
  simp only [CollatzResearch.WordTrace]
  refine ⟨216505931347672270351288037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144337287565114846900858691 216505931347672270351288037)
  ·
    refine ⟨40594862127688550690866507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216505931347672270351288037 40594862127688550690866507)
    ·
      refine ⟨60892293191532826036299761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40594862127688550690866507 60892293191532826036299761)
      ·
        refine ⟨45669219893649619527224821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60892293191532826036299761 45669219893649619527224821)
        ·
          refine ⟨4281489365029651830677327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45669219893649619527224821 4281489365029651830677327)
          ·
            refine ⟨6422234047544477746015991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281489365029651830677327 6422234047544477746015991)
            ·
              refine ⟨9633351071316716619023987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422234047544477746015991 9633351071316716619023987)
              ·
                refine ⟨14450026606975074928535981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633351071316716619023987 14450026606975074928535981)
                ·
                  refine ⟨5418759977615653098200993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14450026606975074928535981 5418759977615653098200993)
                  ·
                    refine ⟨4064069983211739823650745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5418759977615653098200993 4064069983211739823650745)
                    ·
                      refine ⟨3048052487408804867738059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064069983211739823650745 3048052487408804867738059)
                      ·
                        rfl

theorem cell23_5936061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_5936061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936061 prefixEnd_5936061 := by exact prefixLift 5936061
  have htrace : WordTrace (prefixWord ++ tailWord_5936061) baseStart_5936061 baseEnd_5936061 := by
    simpa [prefixWord, tailWord_5936061, baseEnd_5936061] using wordTrace_append hprefix tailTrace_5936061
  have hstable : (prefixWord ++ tailWord_5936061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936061).length < 2 ^ (prefixWord ++ tailWord_5936061).sum := by decide
  have hdescent : baseEnd_5936061 < baseStart_5936061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936167 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5936167 : Nat := 118140960795 + 5936167 * 2 ^ 59
def prefixEnd_5936167 : Nat := 4983230072969 + 3 ^ 40 * 5936167 * 2
def baseEnd_5936167 : Nat := 3048106916358181453012571

theorem tailTrace_5936167 : CollatzResearch.WordTrace tailWord_5936167 prefixEnd_5936167 3048106916358181453012571 := by
  unfold tailWord_5936167
  simp only [CollatzResearch.WordTrace]
  refine ⟨216509797485288250454646755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144339864990192166969764503 216509797485288250454646755)
  ·
    refine ⟨324764696227932375681970133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216509797485288250454646755 324764696227932375681970133)
    ·
      refine ⟨7611672567842165055046175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 324764696227932375681970133 7611672567842165055046175)
      ·
        refine ⟨11417508851763247582569263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611672567842165055046175 11417508851763247582569263)
        ·
          refine ⟨17126263277644871373853895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417508851763247582569263 17126263277644871373853895)
          ·
            refine ⟨25689394916467307060780843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17126263277644871373853895 25689394916467307060780843)
            ·
              refine ⟨38534092374700960591171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25689394916467307060780843 38534092374700960591171265)
              ·
                refine ⟨28900569281025720443378449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38534092374700960591171265 28900569281025720443378449)
                ·
                  refine ⟨21675426960769290332533837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28900569281025720443378449 21675426960769290332533837)
                  ·
                    refine ⟨8128285110288483874700189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21675426960769290332533837 8128285110288483874700189)
                    ·
                      refine ⟨3048106916358181453012571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128285110288483874700189 3048106916358181453012571)
                      ·
                        rfl

theorem cell23_5936167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5936167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936167 prefixEnd_5936167 := by exact prefixLift 5936167
  have htrace : WordTrace (prefixWord ++ tailWord_5936167) baseStart_5936167 baseEnd_5936167 := by
    simpa [prefixWord, tailWord_5936167, baseEnd_5936167] using wordTrace_append hprefix tailTrace_5936167
  have hstable : (prefixWord ++ tailWord_5936167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936167).length < 2 ^ (prefixWord ++ tailWord_5936167).sum := by decide
  have hdescent : baseEnd_5936167 < baseStart_5936167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936200 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_5936200 : Nat := 118140960795 + 5936200 * 2 ^ 59
def prefixEnd_5936200 : Nat := 4983230072969 + 3 ^ 40 * 5936200 * 2
def baseEnd_5936200 : Nat := 1016041287073259941299973

theorem tailTrace_5936200 : CollatzResearch.WordTrace tailWord_5936200 prefixEnd_5936200 1016041287073259941299973 := by
  unfold tailWord_5936200
  simp only [CollatzResearch.WordTrace]
  refine ⟨108255500547084348545299027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144340667396112464727065369 108255500547084348545299027)
  ·
    refine ⟨162383250820626522817948541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108255500547084348545299027 162383250820626522817948541)
    ·
      refine ⟨60893719057734946056730703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162383250820626522817948541 60893719057734946056730703)
      ·
        refine ⟨91340578586602419085096055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60893719057734946056730703 91340578586602419085096055)
        ·
          refine ⟨137010867879903628627644083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91340578586602419085096055 137010867879903628627644083)
          ·
            refine ⟨205516301819855442941466125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137010867879903628627644083 205516301819855442941466125)
            ·
              refine ⟨77068613182445791103049797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205516301819855442941466125 77068613182445791103049797)
              ·
                refine ⟨14450364971708585831821837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77068613182445791103049797 14450364971708585831821837)
                ·
                  refine ⟨5418886864390719686933189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14450364971708585831821837 5418886864390719686933189)
                  ·
                    refine ⟨1016041287073259941299973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418886864390719686933189 1016041287073259941299973)
                    ·
                      rfl

theorem cell23_5936200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_5936200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936200 prefixEnd_5936200 := by exact prefixLift 5936200
  have htrace : WordTrace (prefixWord ++ tailWord_5936200) baseStart_5936200 baseEnd_5936200 := by
    simpa [prefixWord, tailWord_5936200, baseEnd_5936200] using wordTrace_append hprefix tailTrace_5936200
  have hstable : (prefixWord ++ tailWord_5936200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936200).length < 2 ^ (prefixWord ++ tailWord_5936200).sum := by decide
  have hdescent : baseEnd_5936200 < baseStart_5936200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936213 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 10]
def baseStart_5936213 : Nat := 118140960795 + 5936213 * 2 ^ 59
def prefixEnd_5936213 : Nat := 4983230072969 + 3 ^ 40 * 5936213 * 2
def baseEnd_5936213 : Nat := 338681170718698697004151

theorem tailTrace_5936213 : CollatzResearch.WordTrace tailWord_5936213 prefixEnd_5936213 338681170718698697004151 := by
  unfold tailWord_5936213
  simp only [CollatzResearch.WordTrace]
  refine ⟨216511475243121600310821293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144340983495414400207214195 216511475243121600310821293)
  ·
    refine ⟨81191803216170600116557985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216511475243121600310821293 81191803216170600116557985)
    ·
      refine ⟨60893852412127950087418489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81191803216170600116557985 60893852412127950087418489)
      ·
        refine ⟨45670389309095962565563867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60893852412127950087418489 45670389309095962565563867)
        ·
          refine ⟨68505583963643943848345801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45670389309095962565563867 68505583963643943848345801)
          ·
            refine ⟨51379187972732957886259351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68505583963643943848345801 51379187972732957886259351)
            ·
              refine ⟨77068781959099436829389027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51379187972732957886259351 77068781959099436829389027)
              ·
                refine ⟨115603172938649155244083541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77068781959099436829389027 115603172938649155244083541)
                ·
                  refine ⟨338681170718698697004151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115603172938649155244083541 338681170718698697004151)
                  ·
                    rfl

theorem cell23_5936213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_5936213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936213 prefixEnd_5936213 := by exact prefixLift 5936213
  have htrace : WordTrace (prefixWord ++ tailWord_5936213) baseStart_5936213 baseEnd_5936213 := by
    simpa [prefixWord, tailWord_5936213, baseEnd_5936213] using wordTrace_append hprefix tailTrace_5936213
  have hstable : (prefixWord ++ tailWord_5936213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936213).length < 2 ^ (prefixWord ++ tailWord_5936213).sum := by decide
  have hdescent : baseEnd_5936213 < baseStart_5936213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936217 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 1, 4]
def baseStart_5936217 : Nat := 118140960795 + 5936217 * 2 ^ 59
def prefixEnd_5936217 : Nat := 4983230072969 + 3 ^ 40 * 5936217 * 2
def baseEnd_5936217 : Nat := 1016044196796968752462447

theorem tailTrace_5936217 : CollatzResearch.WordTrace tailWord_5936217 prefixEnd_5936217 1016044196796968752462447 := by
  unfold tailWord_5936217
  simp only [CollatzResearch.WordTrace]
  refine ⟨216511621135107108993966905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144341080756738072662644603 216511621135107108993966905)
  ·
    refine ⟨162383715851330331745475179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216511621135107108993966905 162383715851330331745475179)
    ·
      refine ⟨243575573776995497618212769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162383715851330331745475179 243575573776995497618212769)
      ·
        refine ⟨182681680332746623213659577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243575573776995497618212769 182681680332746623213659577)
        ·
          refine ⟨137011260249559967410244683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182681680332746623213659577 137011260249559967410244683)
          ·
            refine ⟨205516890374339951115367025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137011260249559967410244683 205516890374339951115367025)
            ·
              refine ⟨154137667780754963336525269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205516890374339951115367025 154137667780754963336525269)
              ·
                refine ⟨3612601588611444453199811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154137667780754963336525269 3612601588611444453199811)
                ·
                  refine ⟨5418902382917166679799717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612601588611444453199811 5418902382917166679799717)
                  ·
                    refine ⟨1016044196796968752462447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418902382917166679799717 1016044196796968752462447)
                    ·
                      rfl

theorem cell23_5936217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 4].length) (baseStart_5936217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936217 prefixEnd_5936217 := by exact prefixLift 5936217
  have htrace : WordTrace (prefixWord ++ tailWord_5936217) baseStart_5936217 baseEnd_5936217 := by
    simpa [prefixWord, tailWord_5936217, baseEnd_5936217] using wordTrace_append hprefix tailTrace_5936217
  have hstable : (prefixWord ++ tailWord_5936217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936217).length < 2 ^ (prefixWord ++ tailWord_5936217).sum := by decide
  have hdescent : baseEnd_5936217 < baseStart_5936217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936234 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_5936234 : Nat := 118140960795 + 5936234 * 2 ^ 59
def prefixEnd_5936234 : Nat := 4983230072969 + 3 ^ 40 * 5936234 * 2
def baseEnd_5936234 : Nat := 1016047106520677563624921

theorem tailTrace_5936234 : CollatzResearch.WordTrace tailWord_5936234 prefixEnd_5936234 1016047106520677563624921 := by
  unfold tailWord_5936234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54128060294011380224333939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144341494117363680598223837 54128060294011380224333939)
  ·
    refine ⟨81192090441017070336500909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54128060294011380224333939 81192090441017070336500909)
    ·
      refine ⟨30447033915381401376187841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81192090441017070336500909 30447033915381401376187841)
      ·
        refine ⟨22835275436536051032140881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30447033915381401376187841 22835275436536051032140881)
        ·
          refine ⟨17126456577402038274105661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22835275436536051032140881 17126456577402038274105661)
          ·
            refine ⟨6422421216525764352789623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17126456577402038274105661 6422421216525764352789623)
            ·
              refine ⟨9633631824788646529184435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422421216525764352789623 9633631824788646529184435)
              ·
                refine ⟨14450447737182969793776653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633631824788646529184435 14450447737182969793776653)
                ·
                  refine ⟨5418917901443613672666245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14450447737182969793776653 5418917901443613672666245)
                  ·
                    refine ⟨1016047106520677563624921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418917901443613672666245 1016047106520677563624921)
                    ·
                      rfl

theorem cell23_5936234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_5936234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936234 prefixEnd_5936234 := by exact prefixLift 5936234
  have htrace : WordTrace (prefixWord ++ tailWord_5936234) baseStart_5936234 baseEnd_5936234 := by
    simpa [prefixWord, tailWord_5936234, baseEnd_5936234] using wordTrace_append hprefix tailTrace_5936234
  have hstable : (prefixWord ++ tailWord_5936234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936234).length < 2 ^ (prefixWord ++ tailWord_5936234).sum := by decide
  have hdescent : baseEnd_5936234 < baseStart_5936234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936284 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5936284 : Nat := 118140960795 + 5936284 * 2 ^ 59
def prefixEnd_5936284 : Nat := 4983230072969 + 3 ^ 40 * 5936284 * 2
def baseEnd_5936284 : Nat := 3048166993594757495249533

theorem tailTrace_5936284 : CollatzResearch.WordTrace tailWord_5936284 prefixEnd_5936284 3048166993594757495249533 := by
  unfold tailWord_5936284
  simp only [CollatzResearch.WordTrace]
  refine ⟨108257032412932189718327953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144342709883909586291103937 108257032412932189718327953)
  ·
    refine ⟨81192774309699142288745965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108257032412932189718327953 81192774309699142288745965)
    ·
      refine ⟨30447290366137178358279737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81192774309699142288745965 30447290366137178358279737)
      ·
        refine ⟨22835467774602883768709803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30447290366137178358279737 22835467774602883768709803)
        ·
          refine ⟨34253201661904325653064705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22835467774602883768709803 34253201661904325653064705)
          ·
            refine ⟨25689901246428244239798529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34253201661904325653064705 25689901246428244239798529)
            ·
              refine ⟨19267425934821183179848897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25689901246428244239798529 19267425934821183179848897)
              ·
                refine ⟨14450569451115887384886673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19267425934821183179848897 14450569451115887384886673)
                ·
                  refine ⟨10837927088336915538665005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14450569451115887384886673 10837927088336915538665005)
                  ·
                    refine ⟨4064222658126343326999377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10837927088336915538665005 4064222658126343326999377)
                    ·
                      refine ⟨3048166993594757495249533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064222658126343326999377 3048166993594757495249533)
                      ·
                        rfl

theorem cell23_5936284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5936284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936284 prefixEnd_5936284 := by exact prefixLift 5936284
  have htrace : WordTrace (prefixWord ++ tailWord_5936284) baseStart_5936284 baseEnd_5936284 := by
    simpa [prefixWord, tailWord_5936284, baseEnd_5936284] using wordTrace_append hprefix tailTrace_5936284
  have hstable : (prefixWord ++ tailWord_5936284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936284).length < 2 ^ (prefixWord ++ tailWord_5936284).sum := by decide
  have hdescent : baseEnd_5936284 < baseStart_5936284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936307 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 2, 4]
def baseStart_5936307 : Nat := 118140960795 + 5936307 * 2 ^ 59
def prefixEnd_5936307 : Nat := 4983230072969 + 3 ^ 40 * 5936307 * 2
def baseEnd_5936307 : Nat := 1016059601216603635087309

theorem tailTrace_5936307 : CollatzResearch.WordTrace tailWord_5936307 prefixEnd_5936307 1016059601216603635087309 := by
  unfold tailWord_5936307
  simp only [CollatzResearch.WordTrace]
  refine ⟨216514903704781054364743175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144343269136520702909828783 216514903704781054364743175)
  ·
    refine ⟨324772355557171581547114763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216514903704781054364743175 324772355557171581547114763)
    ·
      refine ⟨487158533335757372320672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324772355557171581547114763 487158533335757372320672145)
      ·
        refine ⟨365368900001818029240504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487158533335757372320672145 365368900001818029240504109)
        ·
          refine ⟨137013337500681760965189041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365368900001818029240504109 137013337500681760965189041)
          ·
            refine ⟨102760003125511320723891781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137013337500681760965189041 102760003125511320723891781)
            ·
              refine ⟨19267500586033372635729709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102760003125511320723891781 19267500586033372635729709)
              ·
                refine ⟨7225312719762514738398641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19267500586033372635729709 7225312719762514738398641)
                ·
                  refine ⟨5418984539821886053798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7225312719762514738398641 5418984539821886053798981)
                  ·
                    refine ⟨1016059601216603635087309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5418984539821886053798981 1016059601216603635087309)
                    ·
                      rfl

theorem cell23_5936307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 4].length) (baseStart_5936307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936307 prefixEnd_5936307 := by exact prefixLift 5936307
  have htrace : WordTrace (prefixWord ++ tailWord_5936307) baseStart_5936307 baseEnd_5936307 := by
    simpa [prefixWord, tailWord_5936307, baseEnd_5936307] using wordTrace_append hprefix tailTrace_5936307
  have hstable : (prefixWord ++ tailWord_5936307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936307).length < 2 ^ (prefixWord ++ tailWord_5936307).sum := by decide
  have hdescent : baseEnd_5936307 < baseStart_5936307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936317 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_5936317 : Nat := 118140960795 + 5936317 * 2 ^ 59
def prefixEnd_5936317 : Nat := 4983230072969 + 3 ^ 40 * 5936317 * 2
def baseEnd_5936317 : Nat := 3048183938456355866136881

theorem tailTrace_5936317 : CollatzResearch.WordTrace tailWord_5936317 prefixEnd_5936317 3048183938456355866136881 := by
  unfold tailWord_5936317
  simp only [CollatzResearch.WordTrace]
  refine ⟨216515268434744826072607205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144343512289829884048404803 216515268434744826072607205)
  ·
    refine ⟨40596612831514654888613851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216515268434744826072607205 40596612831514654888613851)
    ·
      refine ⟨60894919247271982332920777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40596612831514654888613851 60894919247271982332920777)
      ·
        refine ⟨45671189435453986749690583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60894919247271982332920777 45671189435453986749690583)
        ·
          refine ⟨68506784153180980124535875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45671189435453986749690583 68506784153180980124535875)
          ·
            refine ⟨102760176229771470186803813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68506784153180980124535875 102760176229771470186803813)
            ·
              refine ⟨19267533043082150660025715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102760176229771470186803813 19267533043082150660025715)
              ·
                refine ⟨28901299564623225990038573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19267533043082150660025715 28901299564623225990038573)
                ·
                  refine ⟨10837987336733709746264465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28901299564623225990038573 10837987336733709746264465)
                  ·
                    refine ⟨8128490502550282309698349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10837987336733709746264465 8128490502550282309698349)
                    ·
                      refine ⟨3048183938456355866136881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128490502550282309698349 3048183938456355866136881)
                      ·
                        rfl

theorem cell23_5936317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_5936317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936317 prefixEnd_5936317 := by exact prefixLift 5936317
  have htrace : WordTrace (prefixWord ++ tailWord_5936317) baseStart_5936317 baseEnd_5936317 := by
    simpa [prefixWord, tailWord_5936317, baseEnd_5936317] using wordTrace_append hprefix tailTrace_5936317
  have hstable : (prefixWord ++ tailWord_5936317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936317).length < 2 ^ (prefixWord ++ tailWord_5936317).sum := by decide
  have hdescent : baseEnd_5936317 < baseStart_5936317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936341 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_5936341 : Nat := 118140960795 + 5936341 * 2 ^ 59
def prefixEnd_5936341 : Nat := 4983230072969 + 3 ^ 40 * 5936341 * 2
def baseEnd_5936341 : Nat := 1016065420664021257412257

theorem tailTrace_5936341 : CollatzResearch.WordTrace tailWord_5936341 prefixEnd_5936341 1016065420664021257412257 := by
  unfold tailWord_5936341
  simp only [CollatzResearch.WordTrace]
  refine ⟨216516143786657878171480877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144344095857771918780987251 216516143786657878171480877)
  ·
    refine ⟨81193553919996704314305329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216516143786657878171480877 81193553919996704314305329)
    ·
      refine ⟨60895165439997528235728997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81193553919996704314305329 60895165439997528235728997)
      ·
        refine ⟨11417843519999536544199187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60895165439997528235728997 11417843519999536544199187)
        ·
          refine ⟨17126765279999304816298781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417843519999536544199187 17126765279999304816298781)
          ·
            refine ⟨6422536979999739306112043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17126765279999304816298781 6422536979999739306112043)
            ·
              refine ⟨9633805469999608959168065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422536979999739306112043 9633805469999608959168065)
              ·
                refine ⟨7225354102499706719376049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9633805469999608959168065 7225354102499706719376049)
                ·
                  refine ⟨5419015576874780039532037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7225354102499706719376049 5419015576874780039532037)
                  ·
                    refine ⟨1016065420664021257412257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419015576874780039532037 1016065420664021257412257)
                    ·
                      rfl

theorem cell23_5936341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_5936341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936341 prefixEnd_5936341 := by exact prefixLift 5936341
  have htrace : WordTrace (prefixWord ++ tailWord_5936341) baseStart_5936341 baseEnd_5936341 := by
    simpa [prefixWord, tailWord_5936341, baseEnd_5936341] using wordTrace_append hprefix tailTrace_5936341
  have hstable : (prefixWord ++ tailWord_5936341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936341).length < 2 ^ (prefixWord ++ tailWord_5936341).sum := by decide
  have hdescent : baseEnd_5936341 < baseStart_5936341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936364 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_5936364 : Nat := 118140960795 + 5936364 * 2 ^ 59
def prefixEnd_5936364 : Nat := 4983230072969 + 3 ^ 40 * 5936364 * 2
def baseEnd_5936364 : Nat := 3048208072047117182249165

theorem tailTrace_5936364 : CollatzResearch.WordTrace tailWord_5936364 prefixEnd_5936364 3048208072047117182249165 := by
  unfold tailWord_5936364
  simp only [CollatzResearch.WordTrace]
  refine ⟨108258491332787276549784073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144344655110383035399712097 108258491332787276549784073)
  ·
    refine ⟨81193868499590457412338055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108258491332787276549784073 81193868499590457412338055)
    ·
      refine ⟨121790802749385686118507083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81193868499590457412338055 121790802749385686118507083)
      ·
        refine ⟨182686204124078529177760625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121790802749385686118507083 182686204124078529177760625)
        ·
          refine ⟨137014653093058896883320469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182686204124078529177760625 137014653093058896883320469)
          ·
            refine ⟨6422561863737135791405647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137014653093058896883320469 6422561863737135791405647)
            ·
              refine ⟨9633842795605703687108471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422561863737135791405647 9633842795605703687108471)
              ·
                refine ⟨14450764193408555530662707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633842795605703687108471 14450764193408555530662707)
                ·
                  refine ⟨21676146290112833295994061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14450764193408555530662707 21676146290112833295994061)
                  ·
                    refine ⟨8128554858792312485997773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21676146290112833295994061 8128554858792312485997773)
                    ·
                      refine ⟨3048208072047117182249165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128554858792312485997773 3048208072047117182249165)
                      ·
                        rfl

theorem cell23_5936364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_5936364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936364 prefixEnd_5936364 := by exact prefixLift 5936364
  have htrace : WordTrace (prefixWord ++ tailWord_5936364) baseStart_5936364 baseEnd_5936364 := by
    simpa [prefixWord, tailWord_5936364, baseEnd_5936364] using wordTrace_append hprefix tailTrace_5936364
  have hstable : (prefixWord ++ tailWord_5936364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936364).length < 2 ^ (prefixWord ++ tailWord_5936364).sum := by decide
  have hdescent : baseEnd_5936364 < baseStart_5936364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936407 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5936407 : Nat := 118140960795 + 5936407 * 2 ^ 59
def prefixEnd_5936407 : Nat := 4983230072969 + 3 ^ 40 * 5936407 * 2
def baseEnd_5936407 : Nat := 3048230151715260514011467

theorem tailTrace_5936407 : CollatzResearch.WordTrace tailWord_5936407 prefixEnd_5936407 3048230151715260514011467 := by
  unfold tailWord_5936407
  simp only [CollatzResearch.WordTrace]
  refine ⟨216518551004418771443383475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144345700669612514295588983 216518551004418771443383475)
  ·
    refine ⟨324777826506628157165075213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216518551004418771443383475 324777826506628157165075213)
    ·
      refine ⟨121791684939985558936903205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324777826506628157165075213 121791684939985558936903205)
      ·
        refine ⟨22835940926247292300669351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121791684939985558936903205 22835940926247292300669351)
        ·
          refine ⟨34253911389370938451004027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22835940926247292300669351 34253911389370938451004027)
          ·
            refine ⟨51380867084056407676506041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34253911389370938451004027 51380867084056407676506041)
            ·
              refine ⟨38535650313042305757379531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51380867084056407676506041 38535650313042305757379531)
              ·
                refine ⟨57803475469563458636069297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38535650313042305757379531 57803475469563458636069297)
                ·
                  refine ⟨43352606602172593977051973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57803475469563458636069297 43352606602172593977051973)
                  ·
                    refine ⟨8128613737907361370697245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43352606602172593977051973 8128613737907361370697245)
                    ·
                      refine ⟨3048230151715260514011467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128613737907361370697245 3048230151715260514011467)
                      ·
                        rfl

theorem cell23_5936407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5936407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936407 prefixEnd_5936407 := by exact prefixLift 5936407
  have htrace : WordTrace (prefixWord ++ tailWord_5936407) baseStart_5936407 baseEnd_5936407 := by
    simpa [prefixWord, tailWord_5936407, baseEnd_5936407] using wordTrace_append hprefix tailTrace_5936407
  have hstable : (prefixWord ++ tailWord_5936407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936407).length < 2 ^ (prefixWord ++ tailWord_5936407).sum := by decide
  have hdescent : baseEnd_5936407 < baseStart_5936407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936415 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 2, 1, 3]
def baseStart_5936415 : Nat := 118140960795 + 5936415 * 2 ^ 59
def prefixEnd_5936415 : Nat := 4983230072969 + 3 ^ 40 * 5936415 * 2
def baseEnd_5936415 : Nat := 3048234259560496482711431

theorem tailTrace_5936415 : CollatzResearch.WordTrace tailWord_5936415 prefixEnd_5936415 3048234259560496482711431 := by
  unfold tailWord_5936415
  simp only [CollatzResearch.WordTrace]
  refine ⟨216518842788389788809674699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144345895192259859206449799 216518842788389788809674699)
  ·
    refine ⟨324778264182584683214512049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216518842788389788809674699 324778264182584683214512049)
    ·
      refine ⟨243583698136938512410884037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324778264182584683214512049 243583698136938512410884037)
      ·
        refine ⟨45671943400675971077040757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243583698136938512410884037 45671943400675971077040757)
        ·
          refine ⟨4281744693813372288472571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45671943400675971077040757 4281744693813372288472571)
          ·
            refine ⟨6422617040720058432708857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281744693813372288472571 6422617040720058432708857)
            ·
              refine ⟨4816962780540043824531643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6422617040720058432708857 4816962780540043824531643)
              ·
                refine ⟨7225444170810065736797465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816962780540043824531643 7225444170810065736797465)
                ·
                  refine ⟨5419083128107549302598099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7225444170810065736797465 5419083128107549302598099)
                  ·
                    refine ⟨8128624692161323953897149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419083128107549302598099 8128624692161323953897149)
                    ·
                      refine ⟨3048234259560496482711431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128624692161323953897149 3048234259560496482711431)
                      ·
                        rfl

theorem cell23_5936415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_5936415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936415 prefixEnd_5936415 := by exact prefixLift 5936415
  have htrace : WordTrace (prefixWord ++ tailWord_5936415) baseStart_5936415 baseEnd_5936415 := by
    simpa [prefixWord, tailWord_5936415, baseEnd_5936415] using wordTrace_append hprefix tailTrace_5936415
  have hstable : (prefixWord ++ tailWord_5936415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936415).length < 2 ^ (prefixWord ++ tailWord_5936415).sum := by decide
  have hdescent : baseEnd_5936415 < baseStart_5936415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936457 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_5936457 : Nat := 118140960795 + 5936457 * 2 ^ 59
def prefixEnd_5936457 : Nat := 4983230072969 + 3 ^ 40 * 5936457 * 2
def baseEnd_5936457 : Nat := 1016085275249328439462079

theorem tailTrace_5936457 : CollatzResearch.WordTrace tailWord_5936457 prefixEnd_5936457 1016085275249328439462079 := by
  unfold tailWord_5936457
  simp only [CollatzResearch.WordTrace]
  refine ⟨216520374654237629982703625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144346916436158419988469083 216520374654237629982703625)
  ·
    refine ⟨162390280990678222487027719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216520374654237629982703625 162390280990678222487027719)
    ·
      refine ⟨243585421486017333730541579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162390280990678222487027719 243585421486017333730541579)
      ·
        refine ⟨365378132229026000595812369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243585421486017333730541579 365378132229026000595812369)
        ·
          refine ⟨274033599171769500446859277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365378132229026000595812369 274033599171769500446859277)
          ·
            refine ⟨102762599689413562667572229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274033599171769500446859277 102762599689413562667572229)
            ·
              refine ⟨19267987441765043000169793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102762599689413562667572229 19267987441765043000169793)
              ·
                refine ⟨14450990581323782250127345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19267987441765043000169793 14450990581323782250127345)
                ·
                  refine ⟨10838242935992836687595509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14450990581323782250127345 10838242935992836687595509)
                  ·
                    refine ⟨1016085275249328439462079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10838242935992836687595509 1016085275249328439462079)
                    ·
                      rfl

theorem cell23_5936457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_5936457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936457 prefixEnd_5936457 := by exact prefixLift 5936457
  have htrace : WordTrace (prefixWord ++ tailWord_5936457) baseStart_5936457 baseEnd_5936457 := by
    simpa [prefixWord, tailWord_5936457, baseEnd_5936457] using wordTrace_append hprefix tailTrace_5936457
  have hstable : (prefixWord ++ tailWord_5936457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936457).length < 2 ^ (prefixWord ++ tailWord_5936457).sum := by decide
  have hdescent : baseEnd_5936457 < baseStart_5936457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936521 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_5936521 : Nat := 118140960795 + 5936521 * 2 ^ 59
def prefixEnd_5936521 : Nat := 4983230072969 + 3 ^ 40 * 5936521 * 2
def baseEnd_5936521 : Nat := 1016096229503291022661981

theorem tailTrace_5936521 : CollatzResearch.WordTrace tailWord_5936521 prefixEnd_5936521 1016096229503291022661981 := by
  unfold tailWord_5936521
  simp only [CollatzResearch.WordTrace]
  refine ⟨216522708926005768913033417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144348472617337179275355611 216522708926005768913033417)
  ·
    refine ⟨162392031694504326684775063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216522708926005768913033417 162392031694504326684775063)
    ·
      refine ⟨243588047541756490027162595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162392031694504326684775063 243588047541756490027162595)
      ·
        refine ⟨365382071312634735040743893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243588047541756490027162595 365382071312634735040743893)
        ·
          refine ⟨8563642296389876602517435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 365382071312634735040743893 8563642296389876602517435)
          ·
            refine ⟨12845463444584814903776153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8563642296389876602517435 12845463444584814903776153)
            ·
              refine ⟨9634097583438611177832115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12845463444584814903776153 9634097583438611177832115)
              ·
                refine ⟨14451146375157916766748173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634097583438611177832115 14451146375157916766748173)
                ·
                  refine ⟨5419179890684218787530565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14451146375157916766748173 5419179890684218787530565)
                  ·
                    refine ⟨1016096229503291022661981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419179890684218787530565 1016096229503291022661981)
                    ·
                      rfl

theorem cell23_5936521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_5936521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936521 prefixEnd_5936521 := by exact prefixLift 5936521
  have htrace : WordTrace (prefixWord ++ tailWord_5936521) baseStart_5936521 baseEnd_5936521 := by
    simpa [prefixWord, tailWord_5936521, baseEnd_5936521] using wordTrace_append hprefix tailTrace_5936521
  have hstable : (prefixWord ++ tailWord_5936521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936521).length < 2 ^ (prefixWord ++ tailWord_5936521).sum := by decide
  have hdescent : baseEnd_5936521 < baseStart_5936521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936584 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_5936584 : Nat := 118140960795 + 5936584 * 2 ^ 59
def prefixEnd_5936584 : Nat := 4983230072969 + 3 ^ 40 * 5936584 * 2
def baseEnd_5936584 : Nat := 3048321037791106321498153

theorem tailTrace_5936584 : CollatzResearch.WordTrace tailWord_5936584 prefixEnd_5936584 3048321037791106321498153 := by
  unfold tailWord_5936584
  simp only [CollatzResearch.WordTrace]
  refine ⟨108262503362388765336288403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144350004483185020448384537 108262503362388765336288403)
  ·
    refine ⟨162393755043583148004432605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108262503362388765336288403 162393755043583148004432605)
    ·
      refine ⟨60897658141343680501662227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162393755043583148004432605 60897658141343680501662227)
      ·
        refine ⟨91346487212015520752493341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60897658141343680501662227 91346487212015520752493341)
        ·
          refine ⟨34254932704505820282185003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91346487212015520752493341 34254932704505820282185003)
          ·
            refine ⟨51382399056758730423277505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34254932704505820282185003 51382399056758730423277505)
            ·
              refine ⟨38536799292569047817458129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51382399056758730423277505 38536799292569047817458129)
              ·
                refine ⟨28902599469426785863093597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38536799292569047817458129 28902599469426785863093597)
                ·
                  refine ⟨10838474801035044698660099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28902599469426785863093597 10838474801035044698660099)
                  ·
                    refine ⟨16257712201552567047990149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10838474801035044698660099 16257712201552567047990149)
                    ·
                      refine ⟨3048321037791106321498153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16257712201552567047990149 3048321037791106321498153)
                      ·
                        rfl

theorem cell23_5936584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_5936584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936584 prefixEnd_5936584 := by exact prefixLift 5936584
  have htrace : WordTrace (prefixWord ++ tailWord_5936584) baseStart_5936584 baseEnd_5936584 := by
    simpa [prefixWord, tailWord_5936584, baseEnd_5936584] using wordTrace_append hprefix tailTrace_5936584
  have hstable : (prefixWord ++ tailWord_5936584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936584).length < 2 ^ (prefixWord ++ tailWord_5936584).sum := by decide
  have hdescent : baseEnd_5936584 < baseStart_5936584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936598 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5936598 : Nat := 118140960795 + 5936598 * 2 ^ 59
def prefixEnd_5936598 : Nat := 4983230072969 + 3 ^ 40 * 5936598 * 2
def baseEnd_5936598 : Nat := 1016109408840089755574363

theorem tailTrace_5936598 : CollatzResearch.WordTrace tailWord_5936598 prefixEnd_5936598 1016109408840089755574363 := by
  unfold tailWord_5936598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13532844834170425691474153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144350344897817874042390965 13532844834170425691474153)
  ·
    refine ⟨10149633625627819268605615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13532844834170425691474153 10149633625627819268605615)
    ·
      refine ⟨15224450438441728902908423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10149633625627819268605615 15224450438441728902908423)
      ·
        refine ⟨22836675657662593354362635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15224450438441728902908423 22836675657662593354362635)
        ·
          refine ⟨34255013486493890031543953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22836675657662593354362635 34255013486493890031543953)
          ·
            refine ⟨25691260114870417523657965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34255013486493890031543953 25691260114870417523657965)
            ·
              refine ⟨9634222543076406571371737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25691260114870417523657965 9634222543076406571371737)
              ·
                refine ⟨7225666907307304928528803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9634222543076406571371737 7225666907307304928528803)
                ·
                  refine ⟨10838500360960957392793205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7225666907307304928528803 10838500360960957392793205)
                  ·
                    refine ⟨1016109408840089755574363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10838500360960957392793205 1016109408840089755574363)
                    ·
                      rfl

theorem cell23_5936598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5936598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936598 prefixEnd_5936598 := by exact prefixLift 5936598
  have htrace : WordTrace (prefixWord ++ tailWord_5936598) baseStart_5936598 baseEnd_5936598 := by
    simpa [prefixWord, tailWord_5936598, baseEnd_5936598] using wordTrace_append hprefix tailTrace_5936598
  have hstable : (prefixWord ++ tailWord_5936598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936598).length < 2 ^ (prefixWord ++ tailWord_5936598).sum := by decide
  have hdescent : baseEnd_5936598 < baseStart_5936598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936601 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_5936601 : Nat := 118140960795 + 5936601 * 2 ^ 59
def prefixEnd_5936601 : Nat := 4983230072969 + 3 ^ 40 * 5936601 * 2
def baseEnd_5936601 : Nat := 3048329766962232754985575

theorem tailTrace_5936601 : CollatzResearch.WordTrace tailWord_5936601 prefixEnd_5936601 3048329766962232754985575 := by
  unfold tailWord_5936601
  simp only [CollatzResearch.WordTrace]
  refine ⟨216525626765715942575945657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144350417843810628383963771 216525626765715942575945657)
  ·
    refine ⟨162394220074286956931959243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216525626765715942575945657 162394220074286956931959243)
    ·
      refine ⟨243591330111430435397938865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162394220074286956931959243 243591330111430435397938865)
      ·
        refine ⟨182693497583572826548454149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243591330111430435397938865 182693497583572826548454149)
        ·
          refine ⟨34255030796919904977835153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182693497583572826548454149 34255030796919904977835153)
          ·
            refine ⟨25691273097689928733376365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34255030796919904977835153 25691273097689928733376365)
            ·
              refine ⟨9634227411633723275016137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25691273097689928733376365 9634227411633723275016137)
              ·
                refine ⟨7225670558725292456262103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9634227411633723275016137 7225670558725292456262103)
                ·
                  refine ⟨10838505838087938684393155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7225670558725292456262103 10838505838087938684393155)
                  ·
                    refine ⟨16257758757131908026589733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10838505838087938684393155 16257758757131908026589733)
                    ·
                      refine ⟨3048329766962232754985575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16257758757131908026589733 3048329766962232754985575)
                      ·
                        rfl

theorem cell23_5936601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_5936601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936601 prefixEnd_5936601 := by exact prefixLift 5936601
  have htrace : WordTrace (prefixWord ++ tailWord_5936601) baseStart_5936601 baseEnd_5936601 := by
    simpa [prefixWord, tailWord_5936601, baseEnd_5936601] using wordTrace_append hprefix tailTrace_5936601
  have hstable : (prefixWord ++ tailWord_5936601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936601).length < 2 ^ (prefixWord ++ tailWord_5936601).sum := by decide
  have hdescent : baseEnd_5936601 < baseStart_5936601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936607 : List Nat := [1, 1, 2, 3, 3, 1, 1, 11]
def baseStart_5936607 : Nat := 118140960795 + 5936607 * 2 ^ 59
def prefixEnd_5936607 : Nat := 4983230072969 + 3 ^ 40 * 5936607 * 2
def baseEnd_5936607 : Nat := 112901216586894804870761

theorem tailTrace_5936607 : CollatzResearch.WordTrace tailWord_5936607 prefixEnd_5936607 112901216586894804870761 := by
  unfold tailWord_5936607
  simp only [CollatzResearch.WordTrace]
  refine ⟨216525845603694205600664075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144350563735796137067109383 216525845603694205600664075)
  ·
    refine ⟨324788768405541308400996113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216525845603694205600664075 324788768405541308400996113)
    ·
      refine ⟨243591576304155981300747085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324788768405541308400996113 243591576304155981300747085)
      ·
        refine ⟨91346841114058492987780157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243591576304155981300747085 91346841114058492987780157)
        ·
          refine ⟨34255065417771934870417559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91346841114058492987780157 34255065417771934870417559)
          ·
            refine ⟨51382598126657902305626339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34255065417771934870417559 51382598126657902305626339)
            ·
              refine ⟨77073897189986853458439509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51382598126657902305626339 77073897189986853458439509)
              ·
                refine ⟨112901216586894804870761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77073897189986853458439509 112901216586894804870761)
                ·
                  rfl

theorem cell23_5936607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 11].length) (baseStart_5936607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936607 prefixEnd_5936607 := by exact prefixLift 5936607
  have htrace : WordTrace (prefixWord ++ tailWord_5936607) baseStart_5936607 baseEnd_5936607 := by
    simpa [prefixWord, tailWord_5936607, baseEnd_5936607] using wordTrace_append hprefix tailTrace_5936607
  have hstable : (prefixWord ++ tailWord_5936607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936607).length < 2 ^ (prefixWord ++ tailWord_5936607).sum := by decide
  have hdescent : baseEnd_5936607 < baseStart_5936607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936627 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_5936627 : Nat := 118140960795 + 5936627 * 2 ^ 59
def prefixEnd_5936627 : Nat := 4983230072969 + 3 ^ 40 * 5936627 * 2
def baseEnd_5936627 : Nat := 3048343117459249653260455

theorem tailTrace_5936627 : CollatzResearch.WordTrace tailWord_5936627 prefixEnd_5936627 3048343117459249653260455 := by
  unfold tailWord_5936627
  simp only [CollatzResearch.WordTrace]
  refine ⟨216526575063621749016392135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144351050042414499344261423 216526575063621749016392135)
  ·
    refine ⟨324789862595432623524588203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216526575063621749016392135 324789862595432623524588203)
    ·
      refine ⟨487184793893148935286882305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324789862595432623524588203 487184793893148935286882305)
      ·
        refine ⟨365388595419861701465161729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487184793893148935286882305 365388595419861701465161729)
        ·
          refine ⟨274041446564896276098871297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365388595419861701465161729 274041446564896276098871297)
          ·
            refine ⟨205531084923672207074153473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274041446564896276098871297 205531084923672207074153473)
            ·
              refine ⟨154148313692754155305615105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205531084923672207074153473 154148313692754155305615105)
              ·
                refine ⟨115611235269565616479211329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154148313692754155305615105 115611235269565616479211329)
                ·
                  refine ⟨86708426452174212359408497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115611235269565616479211329 86708426452174212359408497)
                  ·
                    refine ⟨65031319839130659269556373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86708426452174212359408497 65031319839130659269556373)
                    ·
                      refine ⟨3048343117459249653260455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65031319839130659269556373 3048343117459249653260455)
                      ·
                        rfl

theorem cell23_5936627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_5936627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936627 prefixEnd_5936627 := by exact prefixLift 5936627
  have htrace : WordTrace (prefixWord ++ tailWord_5936627) baseStart_5936627 baseEnd_5936627 := by
    simpa [prefixWord, tailWord_5936627, baseEnd_5936627] using wordTrace_append hprefix tailTrace_5936627
  have hstable : (prefixWord ++ tailWord_5936627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936627).length < 2 ^ (prefixWord ++ tailWord_5936627).sum := by decide
  have hdescent : baseEnd_5936627 < baseStart_5936627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936629 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5936629 : Nat := 118140960795 + 5936629 * 2 ^ 59
def prefixEnd_5936629 : Nat := 4983230072969 + 3 ^ 40 * 5936629 * 2
def baseEnd_5936629 : Nat := 3048344144420558645435447

theorem tailTrace_5936629 : CollatzResearch.WordTrace tailWord_5936629 prefixEnd_5936629 3048344144420558645435447 := by
  unfold tailWord_5936629
  simp only [CollatzResearch.WordTrace]
  refine ⟨216526648009614503357964941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144351098673076335571976627 216526648009614503357964941)
  ·
    refine ⟨81197493003605438759236853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216526648009614503357964941 81197493003605438759236853)
    ·
      refine ⟨7612264969088009883678455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81197493003605438759236853 7612264969088009883678455)
      ·
        refine ⟨11418397453632014825517683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7612264969088009883678455 11418397453632014825517683)
        ·
          refine ⟨17127596180448022238276525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11418397453632014825517683 17127596180448022238276525)
          ·
            refine ⟨6422848567668008339353697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17127596180448022238276525 6422848567668008339353697)
            ·
              refine ⟨4817136425751006254515273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6422848567668008339353697 4817136425751006254515273)
              ·
                refine ⟨3612852319313254690886455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817136425751006254515273 3612852319313254690886455)
                ·
                  refine ⟨5419278478969882036329683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612852319313254690886455 5419278478969882036329683)
                  ·
                    refine ⟨8128917718454823054494525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419278478969882036329683 8128917718454823054494525)
                    ·
                      refine ⟨3048344144420558645435447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128917718454823054494525 3048344144420558645435447)
                      ·
                        rfl

theorem cell23_5936629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5936629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936629 prefixEnd_5936629 := by exact prefixLift 5936629
  have htrace : WordTrace (prefixWord ++ tailWord_5936629) baseStart_5936629 baseEnd_5936629 := by
    simpa [prefixWord, tailWord_5936629, baseEnd_5936629] using wordTrace_append hprefix tailTrace_5936629
  have hstable : (prefixWord ++ tailWord_5936629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936629).length < 2 ^ (prefixWord ++ tailWord_5936629).sum := by decide
  have hdescent : baseEnd_5936629 < baseStart_5936629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936634 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_5936634 : Nat := 118140960795 + 5936634 * 2 ^ 59
def prefixEnd_5936634 : Nat := 4983230072969 + 3 ^ 40 * 5936634 * 2
def baseEnd_5936634 : Nat := 3048346711823831125872923

theorem tailTrace_5936634 : CollatzResearch.WordTrace tailWord_5936634 prefixEnd_5936634 3048346711823831125872923 := by
  unfold tailWord_5936634
  simp only [CollatzResearch.WordTrace]
  refine ⟨54131707593649097302974239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144351220249730926141264637 54131707593649097302974239)
  ·
    refine ⟨81197561390473645954461359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54131707593649097302974239 81197561390473645954461359)
    ·
      refine ⟨121796342085710468931692039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81197561390473645954461359 121796342085710468931692039)
      ·
        refine ⟨182694513128565703397538059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121796342085710468931692039 182694513128565703397538059)
        ·
          refine ⟨274041769692848555096307089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182694513128565703397538059 274041769692848555096307089)
          ·
            refine ⟨205531327269636416322230317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274041769692848555096307089 205531327269636416322230317)
            ·
              refine ⟨77074247726113656120836369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205531327269636416322230317 77074247726113656120836369)
              ·
                refine ⟨57805685794585242090627277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77074247726113656120836369 57805685794585242090627277)
                ·
                  refine ⟨21677132172969465783985229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57805685794585242090627277 21677132172969465783985229)
                  ·
                    refine ⟨8128924564863549668994461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21677132172969465783985229 8128924564863549668994461)
                    ·
                      refine ⟨3048346711823831125872923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8128924564863549668994461 3048346711823831125872923)
                      ·
                        rfl

theorem cell23_5936634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_5936634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936634 prefixEnd_5936634 := by exact prefixLift 5936634
  have htrace : WordTrace (prefixWord ++ tailWord_5936634) baseStart_5936634 baseEnd_5936634 := by
    simpa [prefixWord, tailWord_5936634, baseEnd_5936634] using wordTrace_append hprefix tailTrace_5936634
  have hstable : (prefixWord ++ tailWord_5936634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936634).length < 2 ^ (prefixWord ++ tailWord_5936634).sum := by decide
  have hdescent : baseEnd_5936634 < baseStart_5936634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936641 : List Nat := [1, 2, 4, 1, 4, 2, 1, 8]
def baseStart_5936641 : Nat := 118140960795 + 5936641 * 2 ^ 59
def prefixEnd_5936641 : Nat := 4983230072969 + 3 ^ 40 * 5936641 * 2
def baseEnd_5936641 : Nat := 112901863192163429573533

theorem tailTrace_5936641 : CollatzResearch.WordTrace tailWord_5936641 prefixEnd_5936641 112901863192163429573533 := by
  unfold tailWord_5936641
  simp only [CollatzResearch.WordTrace]
  refine ⟨216527085685571029407401777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144351390457047352938267851 216527085685571029407401777)
  ·
    refine ⟨162395314264178272055551333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216527085685571029407401777 162395314264178272055551333)
    ·
      refine ⟨30449121424533426010415875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162395314264178272055551333 30449121424533426010415875)
      ·
        refine ⟨45673682136800139015623813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30449121424533426010415875 45673682136800139015623813)
        ·
          refine ⟨8563815400650026065429465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45673682136800139015623813 8563815400650026065429465)
          ·
            refine ⟨6422861550487519549072099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8563815400650026065429465 6422861550487519549072099)
            ·
              refine ⟨9634292325731279323608149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422861550487519549072099 9634292325731279323608149)
              ·
                refine ⟨112901863192163429573533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9634292325731279323608149 112901863192163429573533)
                ·
                  rfl

theorem cell23_5936641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 8].length) (baseStart_5936641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936641 prefixEnd_5936641 := by exact prefixLift 5936641
  have htrace : WordTrace (prefixWord ++ tailWord_5936641) baseStart_5936641 baseEnd_5936641 := by
    simpa [prefixWord, tailWord_5936641, baseEnd_5936641] using wordTrace_append hprefix tailTrace_5936641
  have hstable : (prefixWord ++ tailWord_5936641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936641).length < 2 ^ (prefixWord ++ tailWord_5936641).sum := by decide
  have hdescent : baseEnd_5936641 < baseStart_5936641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936714 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_5936714 : Nat := 118140960795 + 5936714 * 2 ^ 59
def prefixEnd_5936714 : Nat := 4983230072969 + 3 ^ 40 * 5936714 * 2
def baseEnd_5936714 : Nat := 338709754475132312541395

theorem tailTrace_5936714 : CollatzResearch.WordTrace tailWord_5936714 prefixEnd_5936714 338709754475132312541395 := by
  unfold tailWord_5936714
  simp only [CollatzResearch.WordTrace]
  refine ⟨54132437053576640718702299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144353165476204375249872797 54132437053576640718702299)
  ·
    refine ⟨81198655580364961078053449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54132437053576640718702299 81198655580364961078053449)
    ·
      refine ⟨60898991685273720808540087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81198655580364961078053449 60898991685273720808540087)
      ·
        refine ⟨91348487527910581212810131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60898991685273720808540087 91348487527910581212810131)
        ·
          refine ⟨137022731291865871819215197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91348487527910581212810131 137022731291865871819215197)
          ·
            refine ⟨51383524234449701932205699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137022731291865871819215197 51383524234449701932205699)
            ·
              refine ⟨77075286351674552898308549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51383524234449701932205699 77075286351674552898308549)
              ·
                refine ⟨14451616190938978668432853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77075286351674552898308549 14451616190938978668432853)
                ·
                  refine ⟨338709754475132312541395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14451616190938978668432853 338709754475132312541395)
                  ·
                    rfl

theorem cell23_5936714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_5936714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936714 prefixEnd_5936714 := by exact prefixLift 5936714
  have htrace : WordTrace (prefixWord ++ tailWord_5936714) baseStart_5936714 baseEnd_5936714 := by
    simpa [prefixWord, tailWord_5936714, baseEnd_5936714] using wordTrace_append hprefix tailTrace_5936714
  have hstable : (prefixWord ++ tailWord_5936714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936714).length < 2 ^ (prefixWord ++ tailWord_5936714).sum := by decide
  have hdescent : baseEnd_5936714 < baseStart_5936714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936751 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 5, 2]
def baseStart_5936751 : Nat := 118140960795 + 5936751 * 2 ^ 59
def prefixEnd_5936751 : Nat := 4983230072969 + 3 ^ 40 * 5936751 * 2
def baseEnd_5936751 : Nat := 3048406789060407168109885

theorem tailTrace_5936751 : CollatzResearch.WordTrace tailWord_5936751 prefixEnd_5936751 3048406789060407168109885 := by
  unfold tailWord_5936751
  simp only [CollatzResearch.WordTrace]
  refine ⟨216531097715172518193906107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144354065143448345462604071 216531097715172518193906107)
  ·
    refine ⟨324796646572758777290859161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216531097715172518193906107 324796646572758777290859161)
    ·
      refine ⟨243597484929569082968144371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324796646572758777290859161 243597484929569082968144371)
      ·
        refine ⟨365396227394353624452216557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243597484929569082968144371 365396227394353624452216557)
        ·
          refine ⟨137023585272882609169581209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365396227394353624452216557 137023585272882609169581209)
          ·
            refine ⟨102767688954661956877185907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137023585272882609169581209 102767688954661956877185907)
            ·
              refine ⟨154151533431992935315778861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102767688954661956877185907 154151533431992935315778861)
              ·
                refine ⟨57806825036997350743417073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154151533431992935315778861 57806825036997350743417073)
                ·
                  refine ⟨43355118777748013057562805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57806825036997350743417073 43355118777748013057562805)
                  ·
                    refine ⟨4064542385413876224146513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43355118777748013057562805 4064542385413876224146513)
                    ·
                      refine ⟨3048406789060407168109885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064542385413876224146513 3048406789060407168109885)
                      ·
                        rfl

theorem cell23_5936751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5, 2].length) (baseStart_5936751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936751 prefixEnd_5936751 := by exact prefixLift 5936751
  have htrace : WordTrace (prefixWord ++ tailWord_5936751) baseStart_5936751 baseEnd_5936751 := by
    simpa [prefixWord, tailWord_5936751, baseEnd_5936751] using wordTrace_append hprefix tailTrace_5936751
  have hstable : (prefixWord ++ tailWord_5936751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936751).length < 2 ^ (prefixWord ++ tailWord_5936751).sum := by decide
  have hdescent : baseEnd_5936751 < baseStart_5936751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936778 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_5936778 : Nat := 118140960795 + 5936778 * 2 ^ 59
def prefixEnd_5936778 : Nat := 4983230072969 + 3 ^ 40 * 5936778 * 2
def baseEnd_5936778 : Nat := 1016140217679359520824087

theorem tailTrace_5936778 : CollatzResearch.WordTrace tailWord_5936778 prefixEnd_5936778 1016140217679359520824087 := by
  unfold tailWord_5936778
  simp only [CollatzResearch.WordTrace]
  refine ⟨54133020621518675451284747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144354721657383134536759325 54133020621518675451284747)
  ·
    refine ⟨81199530932278013176927121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54133020621518675451284747 81199530932278013176927121)
    ·
      refine ⟨60899648199208509882695341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81199530932278013176927121 60899648199208509882695341)
      ·
        refine ⟨22837368074703191206010753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60899648199208509882695341 22837368074703191206010753)
        ·
          refine ⟨17128026056027393404508065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22837368074703191206010753 17128026056027393404508065)
          ·
            refine ⟨12846019542020545053381049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17128026056027393404508065 12846019542020545053381049)
            ·
              refine ⟨9634514656515408790035787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12846019542020545053381049 9634514656515408790035787)
              ·
                refine ⟨14451771984773113185053681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634514656515408790035787 14451771984773113185053681)
                ·
                  refine ⟨10838828988579834888790261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14451771984773113185053681 10838828988579834888790261)
                  ·
                    refine ⟨1016140217679359520824087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10838828988579834888790261 1016140217679359520824087)
                    ·
                      rfl

theorem cell23_5936778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_5936778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936778 prefixEnd_5936778 := by exact prefixLift 5936778
  have htrace : WordTrace (prefixWord ++ tailWord_5936778) baseStart_5936778 baseEnd_5936778 := by
    simpa [prefixWord, tailWord_5936778, baseEnd_5936778] using wordTrace_append hprefix tailTrace_5936778
  have hstable : (prefixWord ++ tailWord_5936778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936778).length < 2 ^ (prefixWord ++ tailWord_5936778).sum := by decide
  have hdescent : baseEnd_5936778 < baseStart_5936778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936799 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 5]
def baseStart_5936799 : Nat := 118140960795 + 5936799 * 2 ^ 59
def prefixEnd_5936799 : Nat := 4983230072969 + 3 ^ 40 * 5936799 * 2
def baseEnd_5936799 : Nat := 338714604014646997812185

theorem tailTrace_5936799 : CollatzResearch.WordTrace tailWord_5936799 prefixEnd_5936799 338714604014646997812185 := by
  unfold tailWord_5936799
  simp only [CollatzResearch.WordTrace]
  refine ⟨216532848418998622391653451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144355232279332414927768967 216532848418998622391653451)
  ·
    refine ⟨324799272628497933587480177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216532848418998622391653451 324799272628497933587480177)
    ·
      refine ⟨243599454471373450190610133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324799272628497933587480177 243599454471373450190610133)
      ·
        refine ⟨5709362214172815238842425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 243599454471373450190610133 5709362214172815238842425)
        ·
          refine ⟨4282021660629611429131819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5709362214172815238842425 4282021660629611429131819)
          ·
            refine ⟨6423032490944417143697729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282021660629611429131819 6423032490944417143697729)
            ·
              refine ⟨4817274368208312857773297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423032490944417143697729 4817274368208312857773297)
              ·
                refine ⟨3612955776156234643329973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817274368208312857773297 3612955776156234643329973)
                ·
                  refine ⟨338714604014646997812185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3612955776156234643329973 338714604014646997812185)
                  ·
                    rfl

theorem cell23_5936799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 5].length) (baseStart_5936799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936799 prefixEnd_5936799 := by exact prefixLift 5936799
  have htrace : WordTrace (prefixWord ++ tailWord_5936799) baseStart_5936799 baseEnd_5936799 := by
    simpa [prefixWord, tailWord_5936799, baseEnd_5936799] using wordTrace_append hprefix tailTrace_5936799
  have hstable : (prefixWord ++ tailWord_5936799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936799).length < 2 ^ (prefixWord ++ tailWord_5936799).sum := by decide
  have hdescent : baseEnd_5936799 < baseStart_5936799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936842 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_5936842 : Nat := 118140960795 + 5936842 * 2 ^ 59
def prefixEnd_5936842 : Nat := 4983230072969 + 3 ^ 40 * 5936842 * 2
def baseEnd_5936842 : Nat := 1016151171933322104023989

theorem tailTrace_5936842 : CollatzResearch.WordTrace tailWord_5936842 prefixEnd_5936842 1016151171933322104023989 := by
  unfold tailWord_5936842
  simp only [CollatzResearch.WordTrace]
  refine ⟨54133604189460710183867195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144356277838561893823645853 54133604189460710183867195)
  ·
    refine ⟨81200406284191065275800793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54133604189460710183867195 81200406284191065275800793)
    ·
      refine ⟨60900304713143298956850595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81200406284191065275800793 60900304713143298956850595)
      ·
        refine ⟨91350457069714948435275893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60900304713143298956850595 91350457069714948435275893)
        ·
          refine ⟨8564105350285776415807115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91350457069714948435275893 8564105350285776415807115)
          ·
            refine ⟨12846158025428664623710673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564105350285776415807115 12846158025428664623710673)
            ·
              refine ⟨9634618519071498467783005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12846158025428664623710673 9634618519071498467783005)
              ·
                refine ⟨3612981944651811925418627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9634618519071498467783005 3612981944651811925418627)
                ·
                  refine ⟨5419472916977717888127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612981944651811925418627 5419472916977717888127941)
                  ·
                    refine ⟨1016151171933322104023989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419472916977717888127941 1016151171933322104023989)
                    ·
                      rfl

theorem cell23_5936842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_5936842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936842 prefixEnd_5936842 := by exact prefixLift 5936842
  have htrace : WordTrace (prefixWord ++ tailWord_5936842) baseStart_5936842 baseEnd_5936842 := by
    simpa [prefixWord, tailWord_5936842, baseEnd_5936842] using wordTrace_append hprefix tailTrace_5936842
  have hstable : (prefixWord ++ tailWord_5936842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936842).length < 2 ^ (prefixWord ++ tailWord_5936842).sum := by decide
  have hdescent : baseEnd_5936842 < baseStart_5936842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936898 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5936898 : Nat := 118140960795 + 5936898 * 2 ^ 59
def prefixEnd_5936898 : Nat := 4983230072969 + 3 ^ 40 * 5936898 * 2
def baseEnd_5936898 : Nat := 1016160756905539364323903

theorem tailTrace_5936898 : CollatzResearch.WordTrace tailWord_5936898 prefixEnd_5936898 1016160756905539364323903 := by
  unfold tailWord_5936898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54134114811409990574876837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144357639497093308199671565 54134114811409990574876837)
  ·
    refine ⟨10150146527139373232789407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54134114811409990574876837 10150146527139373232789407)
    ·
      refine ⟨15225219790709059849184111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150146527139373232789407 15225219790709059849184111)
      ·
        refine ⟨22837829686063589773776167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225219790709059849184111 22837829686063589773776167)
        ·
          refine ⟨34256744529095384660664251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22837829686063589773776167 34256744529095384660664251)
          ·
            refine ⟨51385116793643076990996377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34256744529095384660664251 51385116793643076990996377)
            ·
              refine ⟨38538837595232307743247283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51385116793643076990996377 38538837595232307743247283)
              ·
                refine ⟨57808256392848461614870925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38538837595232307743247283 57808256392848461614870925)
                ·
                  refine ⟨21678096147318173105576597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57808256392848461614870925 21678096147318173105576597)
                  ·
                    refine ⟨1016160756905539364323903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21678096147318173105576597 1016160756905539364323903)
                    ·
                      rfl

theorem cell23_5936898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5936898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936898 prefixEnd_5936898 := by exact prefixLift 5936898
  have htrace : WordTrace (prefixWord ++ tailWord_5936898) baseStart_5936898 baseEnd_5936898 := by
    simpa [prefixWord, tailWord_5936898, baseEnd_5936898] using wordTrace_append hprefix tailTrace_5936898
  have hstable : (prefixWord ++ tailWord_5936898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936898).length < 2 ^ (prefixWord ++ tailWord_5936898).sum := by decide
  have hdescent : baseEnd_5936898 < baseStart_5936898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936922 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_5936922 : Nat := 118140960795 + 5936922 * 2 ^ 59
def prefixEnd_5936922 : Nat := 4983230072969 + 3 ^ 40 * 5936922 * 2
def baseEnd_5936922 : Nat := 3048494594252325999071599

theorem tailTrace_5936922 : CollatzResearch.WordTrace tailWord_5936922 prefixEnd_5936922 3048494594252325999071599 := by
  unfold tailWord_5936922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54134333649388253599595255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144358223065035342932254013 54134333649388253599595255)
  ·
    refine ⟨81201500474082380399392883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54134333649388253599595255 81201500474082380399392883)
    ·
      refine ⟨121802250711123570599089325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81201500474082380399392883 121802250711123570599089325)
      ·
        refine ⟨45675844016671338974658497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121802250711123570599089325 45675844016671338974658497)
        ·
          refine ⟨34256883012503504230993873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45675844016671338974658497 34256883012503504230993873)
          ·
            refine ⟨25692662259377628173245405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34256883012503504230993873 25692662259377628173245405)
            ·
              refine ⟨9634748347266610564967027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25692662259377628173245405 9634748347266610564967027)
              ·
                refine ⟨14452122520899915847450541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634748347266610564967027 14452122520899915847450541)
                ·
                  refine ⟨5419545945337468442793953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14452122520899915847450541 5419545945337468442793953)
                  ·
                    refine ⟨4064659459003101332095465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5419545945337468442793953 4064659459003101332095465)
                    ·
                      refine ⟨3048494594252325999071599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064659459003101332095465 3048494594252325999071599)
                      ·
                        rfl

theorem cell23_5936922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_5936922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936922 prefixEnd_5936922 := by exact prefixLift 5936922
  have htrace : WordTrace (prefixWord ++ tailWord_5936922) baseStart_5936922 baseEnd_5936922 := by
    simpa [prefixWord, tailWord_5936922, baseEnd_5936922] using wordTrace_append hprefix tailTrace_5936922
  have hstable : (prefixWord ++ tailWord_5936922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936922).length < 2 ^ (prefixWord ++ tailWord_5936922).sum := by decide
  have hdescent : baseEnd_5936922 < baseStart_5936922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936932 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_5936932 : Nat := 118140960795 + 5936932 * 2 ^ 59
def prefixEnd_5936932 : Nat := 4983230072969 + 3 ^ 40 * 5936932 * 2
def baseEnd_5936932 : Nat := 1016166576352956986648851

theorem tailTrace_5936932 : CollatzResearch.WordTrace tailWord_5936932 prefixEnd_5936932 1016166576352956986648851 := by
  unfold tailWord_5936932
  simp only [CollatzResearch.WordTrace]
  refine ⟨108268849663758393053122525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144358466218344524070830033 108268849663758393053122525)
  ·
    refine ⟨40600818623909397394920947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108268849663758393053122525 40600818623909397394920947)
    ·
      refine ⟨60901227935864096092381421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40600818623909397394920947 60901227935864096092381421)
      ·
        refine ⟨22837960475949036034643033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60901227935864096092381421 22837960475949036034643033)
        ·
          refine ⟨17128470356961777025982275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22837960475949036034643033 17128470356961777025982275)
          ·
            refine ⟨25692705535442665538973413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17128470356961777025982275 25692705535442665538973413)
            ·
              refine ⟨4817382287895499788557515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25692705535442665538973413 4817382287895499788557515)
              ·
                refine ⟨7226073431843249682836273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817382287895499788557515 7226073431843249682836273)
                ·
                  refine ⟨5419555073882437262127205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7226073431843249682836273 5419555073882437262127205)
                  ·
                    refine ⟨1016166576352956986648851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419555073882437262127205 1016166576352956986648851)
                    ·
                      rfl

theorem cell23_5936932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_5936932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936932 prefixEnd_5936932 := by exact prefixLift 5936932
  have htrace : WordTrace (prefixWord ++ tailWord_5936932) baseStart_5936932 baseEnd_5936932 := by
    simpa [prefixWord, tailWord_5936932, baseEnd_5936932] using wordTrace_append hprefix tailTrace_5936932
  have hstable : (prefixWord ++ tailWord_5936932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936932).length < 2 ^ (prefixWord ++ tailWord_5936932).sum := by decide
  have hdescent : baseEnd_5936932 < baseStart_5936932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936942 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5936942 : Nat := 118140960795 + 5936942 * 2 ^ 59
def prefixEnd_5936942 : Nat := 4983230072969 + 3 ^ 40 * 5936942 * 2
def baseEnd_5936942 : Nat := 3048504863865415920821507

theorem tailTrace_5936942 : CollatzResearch.WordTrace tailWord_5936942 prefixEnd_5936942 3048504863865415920821507 := by
  unfold tailWord_5936942
  simp only [CollatzResearch.WordTrace]
  refine ⟨27067258007185069726763635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144358709371653705209406053 27067258007185069726763635)
  ·
    refine ⟨40600887010777604590145453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27067258007185069726763635 40600887010777604590145453)
    ·
      refine ⟨15225332629041601721304545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40600887010777604590145453 15225332629041601721304545)
      ·
        refine ⟨11418999471781201290978409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15225332629041601721304545 11418999471781201290978409)
        ·
          refine ⟨8564249603835900968233807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11418999471781201290978409 8564249603835900968233807)
          ·
            refine ⟨12846374405753851452350711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564249603835900968233807 12846374405753851452350711)
            ·
              refine ⟨19269561608630777178526067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12846374405753851452350711 19269561608630777178526067)
              ·
                refine ⟨28904342412946165767789101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19269561608630777178526067 28904342412946165767789101)
                ·
                  refine ⟨10839128404854812162920913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28904342412946165767789101 10839128404854812162920913)
                  ·
                    refine ⟨8129346303641109122190685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10839128404854812162920913 8129346303641109122190685)
                    ·
                      refine ⟨3048504863865415920821507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129346303641109122190685 3048504863865415920821507)
                      ·
                        rfl

theorem cell23_5936942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5936942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936942 prefixEnd_5936942 := by exact prefixLift 5936942
  have htrace : WordTrace (prefixWord ++ tailWord_5936942) baseStart_5936942 baseEnd_5936942 := by
    simpa [prefixWord, tailWord_5936942, baseEnd_5936942] using wordTrace_append hprefix tailTrace_5936942
  have hstable : (prefixWord ++ tailWord_5936942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936942).length < 2 ^ (prefixWord ++ tailWord_5936942).sum := by decide
  have hdescent : baseEnd_5936942 < baseStart_5936942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936951 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_5936951 : Nat := 118140960795 + 5936951 * 2 ^ 59
def prefixEnd_5936951 : Nat := 4983230072969 + 3 ^ 40 * 5936951 * 2
def baseEnd_5936951 : Nat := 3048509485191306385608965

theorem tailTrace_5936951 : CollatzResearch.WordTrace tailWord_5936951 prefixEnd_5936951 3048509485191306385608965 := by
  unfold tailWord_5936951
  simp only [CollatzResearch.WordTrace]
  refine ⟨216538392314447952351186707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144358928209631968234124471 216538392314447952351186707)
  ·
    refine ⟨324807588471671928526780061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216538392314447952351186707 324807588471671928526780061)
    ·
      refine ⟨121802845676876973197542523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324807588471671928526780061 121802845676876973197542523)
      ·
        refine ⟨182704268515315459796313785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121802845676876973197542523 182704268515315459796313785)
        ·
          refine ⟨137028201386486594847235339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182704268515315459796313785 137028201386486594847235339)
          ·
            refine ⟨205542302079729892270853009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137028201386486594847235339 205542302079729892270853009)
            ·
              refine ⟨154156726559797419203139757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205542302079729892270853009 154156726559797419203139757)
              ·
                refine ⟨57808772459924032201177409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154156726559797419203139757 57808772459924032201177409)
                ·
                  refine ⟨43356579344943024150883057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57808772459924032201177409 43356579344943024150883057)
                  ·
                    refine ⟨32517434508707268113162293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43356579344943024150883057 32517434508707268113162293)
                    ·
                      refine ⟨3048509485191306385608965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32517434508707268113162293 3048509485191306385608965)
                      ·
                        rfl

theorem cell23_5936951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_5936951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936951 prefixEnd_5936951 := by exact prefixLift 5936951
  have htrace : WordTrace (prefixWord ++ tailWord_5936951) baseStart_5936951 baseEnd_5936951 := by
    simpa [prefixWord, tailWord_5936951, baseEnd_5936951] using wordTrace_append hprefix tailTrace_5936951
  have hstable : (prefixWord ++ tailWord_5936951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936951).length < 2 ^ (prefixWord ++ tailWord_5936951).sum := by decide
  have hdescent : baseEnd_5936951 < baseStart_5936951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936973 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5936973 : Nat := 118140960795 + 5936973 * 2 ^ 59
def prefixEnd_5936973 : Nat := 4983230072969 + 3 ^ 40 * 5936973 * 2
def baseEnd_5936973 : Nat := 3048520781765705299533865

theorem tailTrace_5936973 : CollatzResearch.WordTrace tailWord_5936973 prefixEnd_5936973 3048520781765705299533865 := by
  unfold tailWord_5936973
  simp only [CollatzResearch.WordTrace]
  refine ⟨216539194720368250108487573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144359463146912166738991715 216539194720368250108487573)
  ·
    refine ⟨10150274752517261723835355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216539194720368250108487573 10150274752517261723835355)
    ·
      refine ⟨15225412128775892585753033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150274752517261723835355 15225412128775892585753033)
      ·
        refine ⟨11419059096581919439314775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15225412128775892585753033 11419059096581919439314775)
        ·
          refine ⟨17128588644872879158972163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11419059096581919439314775 17128588644872879158972163)
          ·
            refine ⟨25692882967309318738458245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17128588644872879158972163 25692882967309318738458245)
            ·
              refine ⟨4817415556370497263460921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25692882967309318738458245 4817415556370497263460921)
              ·
                refine ⟨3613061667277872947595691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817415556370497263460921 3613061667277872947595691)
                ·
                  refine ⟨5419592500916809421393537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613061667277872947595691 5419592500916809421393537)
                  ·
                    refine ⟨4064694375687607066045153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5419592500916809421393537 4064694375687607066045153)
                    ·
                      refine ⟨3048520781765705299533865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064694375687607066045153 3048520781765705299533865)
                      ·
                        rfl

theorem cell23_5936973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5936973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936973 prefixEnd_5936973 := by exact prefixLift 5936973
  have htrace : WordTrace (prefixWord ++ tailWord_5936973) baseStart_5936973 baseEnd_5936973 := by
    simpa [prefixWord, tailWord_5936973, baseEnd_5936973] using wordTrace_append hprefix tailTrace_5936973
  have hstable : (prefixWord ++ tailWord_5936973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936973).length < 2 ^ (prefixWord ++ tailWord_5936973).sum := by decide
  have hdescent : baseEnd_5936973 < baseStart_5936973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5936978 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_5936978 : Nat := 118140960795 + 5936978 * 2 ^ 59
def prefixEnd_5936978 : Nat := 4983230072969 + 3 ^ 40 * 5936978 * 2
def baseEnd_5936978 : Nat := 3048523349168977779971341

theorem tailTrace_5936978 : CollatzResearch.WordTrace tailWord_5936978 prefixEnd_5936978 3048523349168977779971341 := by
  unfold tailWord_5936978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54134844271337533990604897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144359584723566757308279725 54134844271337533990604897)
  ·
    refine ⟨40601133203503150492953673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54134844271337533990604897 40601133203503150492953673)
    ·
      refine ⟨30450849902627362869715255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40601133203503150492953673 30450849902627362869715255)
      ·
        refine ⟨45676274853941044304572883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30450849902627362869715255 45676274853941044304572883)
        ·
          refine ⟨68514412280911566456859325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45676274853941044304572883 68514412280911566456859325)
          ·
            refine ⟨25692904605341837421322247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68514412280911566456859325 25692904605341837421322247)
            ·
              refine ⟨38539356908012756131983371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25692904605341837421322247 38539356908012756131983371)
              ·
                refine ⟨57809035362019134197975057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38539356908012756131983371 57809035362019134197975057)
                ·
                  refine ⟨43356776521514350648481293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57809035362019134197975057 43356776521514350648481293)
                  ·
                    refine ⟨16258791195567881493180485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43356776521514350648481293 16258791195567881493180485)
                    ·
                      refine ⟨3048523349168977779971341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16258791195567881493180485 3048523349168977779971341)
                      ·
                        rfl

theorem cell23_5936978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_5936978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5936978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5936978 prefixEnd_5936978 := by exact prefixLift 5936978
  have htrace : WordTrace (prefixWord ++ tailWord_5936978) baseStart_5936978 baseEnd_5936978 := by
    simpa [prefixWord, tailWord_5936978, baseEnd_5936978] using wordTrace_append hprefix tailTrace_5936978
  have hstable : (prefixWord ++ tailWord_5936978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5936978).length < 2 ^ (prefixWord ++ tailWord_5936978).sum := by decide
  have hdescent : baseEnd_5936978 < baseStart_5936978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5936978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937011 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_5937011 : Nat := 118140960795 + 5937011 * 2 ^ 59
def prefixEnd_5937011 : Nat := 4983230072969 + 3 ^ 40 * 5937011 * 2
def baseEnd_5937011 : Nat := 3048540294030576150858689

theorem tailTrace_5937011 : CollatzResearch.WordTrace tailWord_5937011 prefixEnd_5937011 3048540294030576150858689 := by
  unfold tailWord_5937011
  simp only [CollatzResearch.WordTrace]
  refine ⟨216540580694230582598370887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144360387129487055065580591 216540580694230582598370887)
  ·
    refine ⟨324810871041345873897556331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216540580694230582598370887 324810871041345873897556331)
    ·
      refine ⟨487216306562018810846334497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324810871041345873897556331 487216306562018810846334497)
      ·
        refine ⟨365412229921514108134750873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487216306562018810846334497 365412229921514108134750873)
        ·
          refine ⟨274059172441135581101063155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365412229921514108134750873 274059172441135581101063155)
          ·
            refine ⟨411088758661703371651594733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274059172441135581101063155 411088758661703371651594733)
            ·
              refine ⟨154158284498138764369348025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411088758661703371651594733 154158284498138764369348025)
              ·
                refine ⟨115618713373604073277011019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154158284498138764369348025 115618713373604073277011019)
                ·
                  refine ⟨173428070060406109915516529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115618713373604073277011019 173428070060406109915516529)
                  ·
                    refine ⟨130071052545304582436637397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173428070060406109915516529 130071052545304582436637397)
                    ·
                      refine ⟨3048540294030576150858689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130071052545304582436637397 3048540294030576150858689)
                      ·
                        rfl

theorem cell23_5937011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_5937011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937011 prefixEnd_5937011 := by exact prefixLift 5937011
  have htrace : WordTrace (prefixWord ++ tailWord_5937011) baseStart_5937011 baseEnd_5937011 := by
    simpa [prefixWord, tailWord_5937011, baseEnd_5937011] using wordTrace_append hprefix tailTrace_5937011
  have hstable : (prefixWord ++ tailWord_5937011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937011).length < 2 ^ (prefixWord ++ tailWord_5937011).sum := by decide
  have hdescent : baseEnd_5937011 < baseStart_5937011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937085 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5937085 : Nat := 118140960795 + 5937085 * 2 ^ 59
def prefixEnd_5937085 : Nat := 4983230072969 + 3 ^ 40 * 5937085 * 2
def baseEnd_5937085 : Nat := 3048578291599008861333349

theorem tailTrace_5937085 : CollatzResearch.WordTrace tailWord_5937085 prefixEnd_5937085 3048578291599008861333349 := by
  unfold tailWord_5937085
  simp only [CollatzResearch.WordTrace]
  refine ⟨216543279695962493236564709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144362186463974995491043139 216543279695962493236564709)
  ·
    refine ⟨40601864942992967481855883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216543279695962493236564709 40601864942992967481855883)
    ·
      refine ⟨60902797414489451222783825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40601864942992967481855883 60902797414489451222783825)
      ·
        refine ⟨45677098060867088417087869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60902797414489451222783825 45677098060867088417087869)
        ·
          refine ⟨17128911772825158156407951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45677098060867088417087869 17128911772825158156407951)
          ·
            refine ⟨25693367659237737234611927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17128911772825158156407951 25693367659237737234611927)
            ·
              refine ⟨38540051488856605851917891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25693367659237737234611927 38540051488856605851917891)
              ·
                refine ⟨57810077233284908777876837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38540051488856605851917891 57810077233284908777876837)
                ·
                  refine ⟨10839389481240920395851907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57810077233284908777876837 10839389481240920395851907)
                  ·
                    refine ⟨16259084221861380593777861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10839389481240920395851907 16259084221861380593777861)
                    ·
                      refine ⟨3048578291599008861333349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16259084221861380593777861 3048578291599008861333349)
                      ·
                        rfl

theorem cell23_5937085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5937085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937085 prefixEnd_5937085 := by exact prefixLift 5937085
  have htrace : WordTrace (prefixWord ++ tailWord_5937085) baseStart_5937085 baseEnd_5937085 := by
    simpa [prefixWord, tailWord_5937085, baseEnd_5937085] using wordTrace_append hprefix tailTrace_5937085
  have hstable : (prefixWord ++ tailWord_5937085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937085).length < 2 ^ (prefixWord ++ tailWord_5937085).sum := by decide
  have hdescent : baseEnd_5937085 < baseStart_5937085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937098 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_5937098 : Nat := 118140960795 + 5937098 * 2 ^ 59
def prefixEnd_5937098 : Nat := 4983230072969 + 3 ^ 40 * 5937098 * 2
def baseEnd_5937098 : Nat := 3048584966847517310470789

theorem tailTrace_5937098 : CollatzResearch.WordTrace tailWord_5937098 prefixEnd_5937098 3048584966847517310470789 := by
  unfold tailWord_5937098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54135938461228849114196987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144362502563276930971191965 54135938461228849114196987)
  ·
    refine ⟨81203907691843273671295481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54135938461228849114196987 81203907691843273671295481)
    ·
      refine ⟨60902930768882455253471611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81203907691843273671295481 60902930768882455253471611)
      ·
        refine ⟨91354396153323682880207417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60902930768882455253471611 91354396153323682880207417)
        ·
          refine ⟨68515797114992762160155563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91354396153323682880207417 68515797114992762160155563)
          ·
            refine ⟨102773695672489143240233345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68515797114992762160155563 102773695672489143240233345)
            ·
              refine ⟨77080271754366857430175009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102773695672489143240233345 77080271754366857430175009)
              ·
                refine ⟨57810203815775143072631257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77080271754366857430175009 57810203815775143072631257)
                ·
                  refine ⟨43357652861831357304473443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57810203815775143072631257 43357652861831357304473443)
                  ·
                    refine ⟨65036479292747035956710165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43357652861831357304473443 65036479292747035956710165)
                    ·
                      refine ⟨3048584966847517310470789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65036479292747035956710165 3048584966847517310470789)
                      ·
                        rfl

theorem cell23_5937098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_5937098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937098 prefixEnd_5937098 := by exact prefixLift 5937098
  have htrace : WordTrace (prefixWord ++ tailWord_5937098) baseStart_5937098 baseEnd_5937098 := by
    simpa [prefixWord, tailWord_5937098, baseEnd_5937098] using wordTrace_append hprefix tailTrace_5937098
  have hstable : (prefixWord ++ tailWord_5937098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937098).length < 2 ^ (prefixWord ++ tailWord_5937098).sum := by decide
  have hdescent : baseEnd_5937098 < baseStart_5937098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937116 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5937116 : Nat := 118140960795 + 5937116 * 2 ^ 59
def prefixEnd_5937116 : Nat := 4983230072969 + 3 ^ 40 * 5937116 * 2
def baseEnd_5937116 : Nat := 1016198069833099413348569

theorem tailTrace_5937116 : CollatzResearch.WordTrace tailWord_5937116 prefixEnd_5937116 1016198069833099413348569 := by
  unfold tailWord_5937116
  simp only [CollatzResearch.WordTrace]
  refine ⟨108272205179425092765471601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144362940239233457020628801 108272205179425092765471601)
  ·
    refine ⟨81204153884568819574103701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108272205179425092765471601 81204153884568819574103701)
    ·
      refine ⟨3806444713339163417536111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81204153884568819574103701 3806444713339163417536111)
      ·
        refine ⟨5709667070008745126304167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806444713339163417536111 5709667070008745126304167)
        ·
          refine ⟨8564500605013117689456251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709667070008745126304167 8564500605013117689456251)
          ·
            refine ⟨12846750907519676534184377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564500605013117689456251 12846750907519676534184377)
            ·
              refine ⟨9635063180639757400638283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12846750907519676534184377 9635063180639757400638283)
              ·
                refine ⟨14452594770959636100957425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9635063180639757400638283 14452594770959636100957425)
                ·
                  refine ⟨10839446078219727075718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14452594770959636100957425 10839446078219727075718069)
                  ·
                    refine ⟨1016198069833099413348569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10839446078219727075718069 1016198069833099413348569)
                    ·
                      rfl

theorem cell23_5937116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5937116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937116 prefixEnd_5937116 := by exact prefixLift 5937116
  have htrace : WordTrace (prefixWord ++ tailWord_5937116) baseStart_5937116 baseEnd_5937116 := by
    simpa [prefixWord, tailWord_5937116, baseEnd_5937116] using wordTrace_append hprefix tailTrace_5937116
  have hstable : (prefixWord ++ tailWord_5937116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937116).length < 2 ^ (prefixWord ++ tailWord_5937116).sum := by decide
  have hdescent : baseEnd_5937116 < baseStart_5937116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5937128 : Nat := 118140960795 + 5937128 * 2 ^ 59
def prefixEnd_5937128 : Nat := 4983230072969 + 3 ^ 40 * 5937128 * 2
def baseEnd_5937128 : Nat := 3048600371267152193095651

theorem tailTrace_5937128 : CollatzResearch.WordTrace tailWord_5937128 prefixEnd_5937128 3048600371267152193095651 := by
  unfold tailWord_5937128
  simp only [CollatzResearch.WordTrace]
  refine ⟨108272424017403355790190019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144363232023204474386920025 108272424017403355790190019)
  ·
    refine ⟨162408636026105033685285029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108272424017403355790190019 162408636026105033685285029)
    ·
      refine ⟨30451619254894693815990943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162408636026105033685285029 30451619254894693815990943)
      ·
        refine ⟨45677428882342040723986415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30451619254894693815990943 45677428882342040723986415)
        ·
          refine ⟨68516143323513061085979623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45677428882342040723986415 68516143323513061085979623)
          ·
            refine ⟨102774214985269591628969435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68516143323513061085979623 102774214985269591628969435)
            ·
              refine ⟨154161322477904387443454153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102774214985269591628969435 154161322477904387443454153)
              ·
                refine ⟨115620991858428290582590615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154161322477904387443454153 115620991858428290582590615)
                ·
                  refine ⟨173431487787642435873885923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115620991858428290582590615 173431487787642435873885923)
                  ·
                    refine ⟨260147231681463653810828885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173431487787642435873885923 260147231681463653810828885)
                    ·
                      refine ⟨3048600371267152193095651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260147231681463653810828885 3048600371267152193095651)
                      ·
                        rfl

theorem cell23_5937128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5937128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937128 prefixEnd_5937128 := by exact prefixLift 5937128
  have htrace : WordTrace (prefixWord ++ tailWord_5937128) baseStart_5937128 baseEnd_5937128 := by
    simpa [prefixWord, tailWord_5937128, baseEnd_5937128] using wordTrace_append hprefix tailTrace_5937128
  have hstable : (prefixWord ++ tailWord_5937128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937128).length < 2 ^ (prefixWord ++ tailWord_5937128).sum := by decide
  have hdescent : baseEnd_5937128 < baseStart_5937128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937168 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_5937168 : Nat := 118140960795 + 5937168 * 2 ^ 59
def prefixEnd_5937168 : Nat := 4983230072969 + 3 ^ 40 * 5937168 * 2
def baseEnd_5937168 : Nat := 1016206970164444012198489

theorem tailTrace_5937168 : CollatzResearch.WordTrace tailWord_5937168 prefixEnd_5937168 1016206970164444012198489 := by
  unfold tailWord_5937168
  simp only [CollatzResearch.WordTrace]
  refine ⟨108273153477330899205918079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144364204636441198941224105 108273153477330899205918079)
  ·
    refine ⟨162409730215996348808877119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108273153477330899205918079 162409730215996348808877119)
    ·
      refine ⟨243614595323994523213315679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162409730215996348808877119 243614595323994523213315679)
      ·
        refine ⟨365421892985991784819973519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243614595323994523213315679 365421892985991784819973519)
        ·
          refine ⟨548132839478987677229960279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365421892985991784819973519 548132839478987677229960279)
          ·
            refine ⟨822199259218481515844940419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548132839478987677229960279 822199259218481515844940419)
            ·
              refine ⟨1233298888827722273767410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822199259218481515844940419 1233298888827722273767410629)
              ·
                refine ⟨231243541655197926331389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1233298888827722273767410629 231243541655197926331389493)
                ·
                  refine ⟨21679082030174805593567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231243541655197926331389493 21679082030174805593567765)
                  ·
                    refine ⟨1016206970164444012198489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21679082030174805593567765 1016206970164444012198489)
                    ·
                      rfl

theorem cell23_5937168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_5937168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937168 prefixEnd_5937168 := by exact prefixLift 5937168
  have htrace : WordTrace (prefixWord ++ tailWord_5937168) baseStart_5937168 baseEnd_5937168 := by
    simpa [prefixWord, tailWord_5937168, baseEnd_5937168] using wordTrace_append hprefix tailTrace_5937168
  have hstable : (prefixWord ++ tailWord_5937168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937168).length < 2 ^ (prefixWord ++ tailWord_5937168).sum := by decide
  have hdescent : baseEnd_5937168 < baseStart_5937168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937186 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_5937186 : Nat := 118140960795 + 5937186 * 2 ^ 59
def prefixEnd_5937186 : Nat := 4983230072969 + 3 ^ 40 * 5937186 * 2
def baseEnd_5937186 : Nat := 3048630153145112966170385

theorem tailTrace_5937186 : CollatzResearch.WordTrace tailWord_5937186 prefixEnd_5937186 3048630153145112966170385 := by
  unfold tailWord_5937186
  simp only [CollatzResearch.WordTrace]
  refine ⟨54136740867149146871497853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144364642312397724990660941 54136740867149146871497853)
  ·
    refine ⟨20301277825180930076811695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54136740867149146871497853 20301277825180930076811695)
    ·
      refine ⟨30451916737771395115217543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20301277825180930076811695 30451916737771395115217543)
      ·
        refine ⟨45677875106657092672826315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30451916737771395115217543 45677875106657092672826315)
        ·
          refine ⟨68516812659985639009239473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45677875106657092672826315 68516812659985639009239473)
          ·
            refine ⟨51387609494989229256929605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68516812659985639009239473 51387609494989229256929605)
            ·
              refine ⟨9635176780310480485674301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51387609494989229256929605 9635176780310480485674301)
              ·
                refine ⟨3613191292616430182127863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9635176780310480485674301 3613191292616430182127863)
                ·
                  refine ⟨5419786938924645273191795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613191292616430182127863 5419786938924645273191795)
                  ·
                    refine ⟨8129680408386967909787693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419786938924645273191795 8129680408386967909787693)
                    ·
                      refine ⟨3048630153145112966170385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129680408386967909787693 3048630153145112966170385)
                      ·
                        rfl

theorem cell23_5937186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_5937186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937186 prefixEnd_5937186 := by exact prefixLift 5937186
  have htrace : WordTrace (prefixWord ++ tailWord_5937186) baseStart_5937186 baseEnd_5937186 := by
    simpa [prefixWord, tailWord_5937186, baseEnd_5937186] using wordTrace_append hprefix tailTrace_5937186
  have hstable : (prefixWord ++ tailWord_5937186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937186).length < 2 ^ (prefixWord ++ tailWord_5937186).sum := by decide
  have hdescent : baseEnd_5937186 < baseStart_5937186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937189 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_5937189 : Nat := 118140960795 + 5937189 * 2 ^ 59
def prefixEnd_5937189 : Nat := 4983230072969 + 3 ^ 40 * 5937189 * 2
def baseEnd_5937189 : Nat := 1016210564529025484810957

theorem tailTrace_5937189 : CollatzResearch.WordTrace tailWord_5937189 prefixEnd_5937189 1016210564529025484810957 := by
  unfold tailWord_5937189
  simp only [CollatzResearch.WordTrace]
  refine ⟨216547072887585718998350621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144364715258390479332233747 216547072887585718998350621)
  ·
    refine ⟨81205152332844644624381483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216547072887585718998350621 81205152332844644624381483)
    ·
      refine ⟨121807728499266966936572225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81205152332844644624381483 121807728499266966936572225)
      ·
        refine ⟨91355796374450225202429169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121807728499266966936572225 91355796374450225202429169)
        ·
          refine ⟨68516847280837668901821877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91355796374450225202429169 68516847280837668901821877)
          ·
            refine ⟨6423454432578531459545801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68516847280837668901821877 6423454432578531459545801)
            ·
              refine ⟨4817590824433898594659351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423454432578531459545801 4817590824433898594659351)
              ·
                refine ⟨7226386236650847891989027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817590824433898594659351 7226386236650847891989027)
                ·
                  refine ⟨10839579354976271837983541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226386236650847891989027 10839579354976271837983541)
                  ·
                    refine ⟨1016210564529025484810957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10839579354976271837983541 1016210564529025484810957)
                    ·
                      rfl

theorem cell23_5937189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_5937189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937189 prefixEnd_5937189 := by exact prefixLift 5937189
  have htrace : WordTrace (prefixWord ++ tailWord_5937189) baseStart_5937189 baseEnd_5937189 := by
    simpa [prefixWord, tailWord_5937189, baseEnd_5937189] using wordTrace_append hprefix tailTrace_5937189
  have hstable : (prefixWord ++ tailWord_5937189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937189).length < 2 ^ (prefixWord ++ tailWord_5937189).sum := by decide
  have hdescent : baseEnd_5937189 < baseStart_5937189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937195 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3]
def baseStart_5937195 : Nat := 118140960795 + 5937195 * 2 ^ 59
def prefixEnd_5937195 : Nat := 4983230072969 + 3 ^ 40 * 5937195 * 2
def baseEnd_5937195 : Nat := 3048634774471003430957843

theorem tailTrace_5937195 : CollatzResearch.WordTrace tailWord_5937195 prefixEnd_5937195 3048634774471003430957843 := by
  unfold tailWord_5937195
  simp only [CollatzResearch.WordTrace]
  refine ⟨216547291725563982023069039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144364861150375988015379359 216547291725563982023069039)
  ·
    refine ⟨324820937588345973034603559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216547291725563982023069039 324820937588345973034603559)
    ·
      refine ⟨487231406382518959551905339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324820937588345973034603559 487231406382518959551905339)
      ·
        refine ⟨730847109573778439327858009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487231406382518959551905339 730847109573778439327858009)
        ·
          refine ⟨548135332180333829495893507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730847109573778439327858009 548135332180333829495893507)
          ·
            refine ⟨822202998270500744243840261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548135332180333829495893507 822202998270500744243840261)
            ·
              refine ⟨154163062175718889545720049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 822202998270500744243840261 154163062175718889545720049)
              ·
                refine ⟨115622296631789167159290037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154163062175718889545720049 115622296631789167159290037)
                ·
                  refine ⟨10839590309230234421183441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115622296631789167159290037 10839590309230234421183441)
                  ·
                    refine ⟨8129692731922675815887581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10839590309230234421183441 8129692731922675815887581)
                    ·
                      refine ⟨3048634774471003430957843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129692731922675815887581 3048634774471003430957843)
                      ·
                        rfl

theorem cell23_5937195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3].length) (baseStart_5937195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937195 prefixEnd_5937195 := by exact prefixLift 5937195
  have htrace : WordTrace (prefixWord ++ tailWord_5937195) baseStart_5937195 baseEnd_5937195 := by
    simpa [prefixWord, tailWord_5937195, baseEnd_5937195] using wordTrace_append hprefix tailTrace_5937195
  have hstable : (prefixWord ++ tailWord_5937195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937195).length < 2 ^ (prefixWord ++ tailWord_5937195).sum := by decide
  have hdescent : baseEnd_5937195 < baseStart_5937195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937202 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_5937202 : Nat := 118140960795 + 5937202 * 2 ^ 59
def prefixEnd_5937202 : Nat := 4983230072969 + 3 ^ 40 * 5937202 * 2
def baseEnd_5937202 : Nat := 1016212789611861634523437

theorem tailTrace_5937202 : CollatzResearch.WordTrace tailWord_5937202 prefixEnd_5937202 1016212789611861634523437 := by
  unfold tailWord_5937202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54136886759134655554643465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144365031357692414812382573 54136886759134655554643465)
  ·
    refine ⟨40602665069350991665982599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54136886759134655554643465 40602665069350991665982599)
    ·
      refine ⟨60903997604026487498973899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40602665069350991665982599 60903997604026487498973899)
      ·
        refine ⟨91355996406039731248460849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60903997604026487498973899 91355996406039731248460849)
        ·
          refine ⟨68516997304529798436345637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91355996406039731248460849 68516997304529798436345637)
          ·
            refine ⟨12846936994599337206814807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68516997304529798436345637 12846936994599337206814807)
            ·
              refine ⟨19270405491899005810222211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12846936994599337206814807 19270405491899005810222211)
              ·
                refine ⟨28905608237848508715333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19270405491899005810222211 28905608237848508715333317)
                ·
                  refine ⟨5419801544596595384124997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28905608237848508715333317 5419801544596595384124997)
                  ·
                    refine ⟨1016212789611861634523437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5419801544596595384124997 1016212789611861634523437)
                    ·
                      rfl

theorem cell23_5937202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_5937202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937202 prefixEnd_5937202 := by exact prefixLift 5937202
  have htrace : WordTrace (prefixWord ++ tailWord_5937202) baseStart_5937202 baseEnd_5937202 := by
    simpa [prefixWord, tailWord_5937202, baseEnd_5937202] using wordTrace_append hprefix tailTrace_5937202
  have hstable : (prefixWord ++ tailWord_5937202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937202).length < 2 ^ (prefixWord ++ tailWord_5937202).sum := by decide
  have hdescent : baseEnd_5937202 < baseStart_5937202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937205 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5937205 : Nat := 118140960795 + 5937205 * 2 ^ 59
def prefixEnd_5937205 : Nat := 4983230072969 + 3 ^ 40 * 5937205 * 2
def baseEnd_5937205 : Nat := 3048639909277548391832797

theorem tailTrace_5937205 : CollatzResearch.WordTrace tailWord_5937205 prefixEnd_5937205 3048639909277548391832797 := by
  unfold tailWord_5937205
  simp only [CollatzResearch.WordTrace]
  refine ⟨216547656455527753730933069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144365104303685169153955379 216547656455527753730933069)
  ·
    refine ⟨81205371170822907649099901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216547656455527753730933069 81205371170822907649099901)
    ·
      refine ⟨30452014189058590368412463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81205371170822907649099901 30452014189058590368412463)
      ·
        refine ⟨45678021283587885552618695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30452014189058590368412463 45678021283587885552618695)
        ·
          refine ⟨68517031925381828328928043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45678021283587885552618695 68517031925381828328928043)
          ·
            refine ⟨102775547888072742493392065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68517031925381828328928043 102775547888072742493392065)
            ·
              refine ⟨77081660916054556870044049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102775547888072742493392065 77081660916054556870044049)
              ·
                refine ⟨57811245687040917652533037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77081660916054556870044049 57811245687040917652533037)
                ·
                  refine ⟨21679217132640344119699889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57811245687040917652533037 21679217132640344119699889)
                  ·
                    refine ⟨16259412849480258089774917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21679217132640344119699889 16259412849480258089774917)
                    ·
                      refine ⟨3048639909277548391832797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16259412849480258089774917 3048639909277548391832797)
                      ·
                        rfl

theorem cell23_5937205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5937205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937205 prefixEnd_5937205 := by exact prefixLift 5937205
  have htrace : WordTrace (prefixWord ++ tailWord_5937205) baseStart_5937205 baseEnd_5937205 := by
    simpa [prefixWord, tailWord_5937205, baseEnd_5937205] using wordTrace_append hprefix tailTrace_5937205
  have hstable : (prefixWord ++ tailWord_5937205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937205).length < 2 ^ (prefixWord ++ tailWord_5937205).sum := by decide
  have hdescent : baseEnd_5937205 < baseStart_5937205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937242 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_5937242 : Nat := 118140960795 + 5937242 * 2 ^ 59
def prefixEnd_5937242 : Nat := 4983230072969 + 3 ^ 40 * 5937242 * 2
def baseEnd_5937242 : Nat := 3048658908061764747070127

theorem tailTrace_5937242 : CollatzResearch.WordTrace tailWord_5937242 prefixEnd_5937242 3048658908061764747070127 := by
  unfold tailWord_5937242
  simp only [CollatzResearch.WordTrace]
  refine ⟨54137251489098427262507495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144366003970929139366686653 54137251489098427262507495)
  ·
    refine ⟨81205877233647640893761243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54137251489098427262507495 81205877233647640893761243)
    ·
      refine ⟨121808815850471461340641865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81205877233647640893761243 121808815850471461340641865)
      ·
        refine ⟨91356611887853596005481399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121808815850471461340641865 91356611887853596005481399)
        ·
          refine ⟨137034917831780394008222099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91356611887853596005481399 137034917831780394008222099)
          ·
            refine ⟨205552376747670591012333149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137034917831780394008222099 205552376747670591012333149)
            ·
              refine ⟨77082141280376471629624931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205552376747670591012333149 77082141280376471629624931)
              ·
                refine ⟨115623211920564707444437397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77082141280376471629624931 115623211920564707444437397)
                ·
                  refine ⟨5419838058776470661458003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115623211920564707444437397 5419838058776470661458003)
                  ·
                    refine ⟨8129757088164705992187005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419838058776470661458003 8129757088164705992187005)
                    ·
                      refine ⟨3048658908061764747070127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129757088164705992187005 3048658908061764747070127)
                      ·
                        rfl

theorem cell23_5937242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_5937242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937242 prefixEnd_5937242 := by exact prefixLift 5937242
  have htrace : WordTrace (prefixWord ++ tailWord_5937242) baseStart_5937242 baseEnd_5937242 := by
    simpa [prefixWord, tailWord_5937242, baseEnd_5937242] using wordTrace_append hprefix tailTrace_5937242
  have hstable : (prefixWord ++ tailWord_5937242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937242).length < 2 ^ (prefixWord ++ tailWord_5937242).sum := by decide
  have hdescent : baseEnd_5937242 < baseStart_5937242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937255 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_5937255 : Nat := 118140960795 + 5937255 * 2 ^ 59
def prefixEnd_5937255 : Nat := 4983230072969 + 3 ^ 40 * 5937255 * 2
def baseEnd_5937255 : Nat := 3048665583310273196207567

theorem tailTrace_5937255 : CollatzResearch.WordTrace tailWord_5937255 prefixEnd_5937255 3048665583310273196207567 := by
  unfold tailWord_5937255
  simp only [CollatzResearch.WordTrace]
  refine ⟨216549480105346612270253219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144366320070231074846835479 216549480105346612270253219)
  ·
    refine ⟨324824220158019918405379829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216549480105346612270253219 324824220158019918405379829)
    ·
      refine ⟨30452270639814367350504359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324824220158019918405379829 30452270639814367350504359)
      ·
        refine ⟨45678405959721551025756539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30452270639814367350504359 45678405959721551025756539)
        ·
          refine ⟨68517608939582326538634809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45678405959721551025756539 68517608939582326538634809)
          ·
            refine ⟨51388206704686744903976107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68517608939582326538634809 51388206704686744903976107)
            ·
              refine ⟨77082310057030117355964161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51388206704686744903976107 77082310057030117355964161)
              ·
                refine ⟨57811732542772588016973121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77082310057030117355964161 57811732542772588016973121)
                ·
                  refine ⟨43358799407079441012729841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57811732542772588016973121 43358799407079441012729841)
                  ·
                    refine ⟨32519099555309580759547381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43358799407079441012729841 32519099555309580759547381)
                    ·
                      refine ⟨3048665583310273196207567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32519099555309580759547381 3048665583310273196207567)
                      ·
                        rfl

theorem cell23_5937255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_5937255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937255 prefixEnd_5937255 := by exact prefixLift 5937255
  have htrace : WordTrace (prefixWord ++ tailWord_5937255) baseStart_5937255 baseEnd_5937255 := by
    simpa [prefixWord, tailWord_5937255, baseEnd_5937255] using wordTrace_append hprefix tailTrace_5937255
  have hstable : (prefixWord ++ tailWord_5937255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937255).length < 2 ^ (prefixWord ++ tailWord_5937255).sum := by decide
  have hdescent : baseEnd_5937255 < baseStart_5937255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937265 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_5937265 : Nat := 118140960795 + 5937265 * 2 ^ 59
def prefixEnd_5937265 : Nat := 4983230072969 + 3 ^ 40 * 5937265 * 2
def baseEnd_5937265 : Nat := 3048670718116818157082521

theorem tailTrace_5937265 : CollatzResearch.WordTrace tailWord_5937265 prefixEnd_5937265 3048670718116818157082521 := by
  unfold tailWord_5937265
  simp only [CollatzResearch.WordTrace]
  refine ⟨216549844835310383978117249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144366563223540255985411499 216549844835310383978117249)
  ·
    refine ⟨162412383626482787983587937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216549844835310383978117249 162412383626482787983587937)
    ·
      refine ⟨121809287719862090987690953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162412383626482787983587937 121809287719862090987690953)
      ·
        refine ⟨91356965789896568240768215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121809287719862090987690953 91356965789896568240768215)
        ·
          refine ⟨137035448684844852361152323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91356965789896568240768215 137035448684844852361152323)
          ·
            refine ⟨205553173027267278541728485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137035448684844852361152323 205553173027267278541728485)
            ·
              refine ⟨38541219942612614726574091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205553173027267278541728485 38541219942612614726574091)
              ·
                refine ⟨57811829913918922089861137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38541219942612614726574091 57811829913918922089861137)
                ·
                  refine ⟨43358872435439191567395853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57811829913918922089861137 43358872435439191567395853)
                  ·
                    refine ⟨16259577163289696837773445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43358872435439191567395853 16259577163289696837773445)
                    ·
                      refine ⟨3048670718116818157082521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16259577163289696837773445 3048670718116818157082521)
                      ·
                        rfl

theorem cell23_5937265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_5937265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937265 prefixEnd_5937265 := by exact prefixLift 5937265
  have htrace : WordTrace (prefixWord ++ tailWord_5937265) baseStart_5937265 baseEnd_5937265 := by
    simpa [prefixWord, tailWord_5937265, baseEnd_5937265] using wordTrace_append hprefix tailTrace_5937265
  have hstable : (prefixWord ++ tailWord_5937265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937265).length < 2 ^ (prefixWord ++ tailWord_5937265).sum := by decide
  have hdescent : baseEnd_5937265 < baseStart_5937265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937276 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_5937276 : Nat := 118140960795 + 5937276 * 2 ^ 59
def prefixEnd_5937276 : Nat := 4983230072969 + 3 ^ 40 * 5937276 * 2
def baseEnd_5937276 : Nat := 3048676366404017614044971

theorem tailTrace_5937276 : CollatzResearch.WordTrace tailWord_5937276 prefixEnd_5937276 3048676366404017614044971 := by
  unfold tailWord_5937276
  simp only [CollatzResearch.WordTrace]
  refine ⟨108275123019135266428383841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144366830692180355237845121 108275123019135266428383841)
  ·
    refine ⟨81206342264351449821287881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108275123019135266428383841 81206342264351449821287881)
    ·
      refine ⟨60904756698263587365965911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81206342264351449821287881 60904756698263587365965911)
      ·
        refine ⟨91357135047395381048948867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60904756698263587365965911 91357135047395381048948867)
        ·
          refine ⟨137035702571093071573423301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91357135047395381048948867 137035702571093071573423301)
          ·
            refine ⟨25694194232079950920016869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137035702571093071573423301 25694194232079950920016869)
            ·
              refine ⟨4817661418514990797503163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25694194232079950920016869 4817661418514990797503163)
              ·
                refine ⟨7226492127772486196254745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817661418514990797503163 7226492127772486196254745)
                ·
                  refine ⟨5419869095829364647191059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7226492127772486196254745 5419869095829364647191059)
                  ·
                    refine ⟨8129803643744046970786589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5419869095829364647191059 8129803643744046970786589)
                    ·
                      refine ⟨3048676366404017614044971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129803643744046970786589 3048676366404017614044971)
                      ·
                        rfl

theorem cell23_5937276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_5937276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937276 prefixEnd_5937276 := by exact prefixLift 5937276
  have htrace : WordTrace (prefixWord ++ tailWord_5937276) baseStart_5937276 baseEnd_5937276 := by
    simpa [prefixWord, tailWord_5937276, baseEnd_5937276] using wordTrace_append hprefix tailTrace_5937276
  have hstable : (prefixWord ++ tailWord_5937276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937276).length < 2 ^ (prefixWord ++ tailWord_5937276).sum := by decide
  have hdescent : baseEnd_5937276 < baseStart_5937276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937303 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_5937303 : Nat := 118140960795 + 5937303 * 2 ^ 59
def prefixEnd_5937303 : Nat := 4983230072969 + 3 ^ 40 * 5937303 * 2
def baseEnd_5937303 : Nat := 3048690230381689008407347

theorem tailTrace_5937303 : CollatzResearch.WordTrace tailWord_5937303 prefixEnd_5937303 3048690230381689008407347 := by
  unfold tailWord_5937303
  simp only [CollatzResearch.WordTrace]
  refine ⟨216551230809172716468000563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144367487206115144312000375 216551230809172716468000563)
  ·
    refine ⟨324826846213759074702000845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216551230809172716468000563 324826846213759074702000845)
    ·
      refine ⟨121810067330159653013250317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324826846213759074702000845 121810067330159653013250317)
      ·
        refine ⟨45678775248809869879968869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121810067330159653013250317 45678775248809869879968869)
        ·
          refine ⟨8564770359151850602494163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45678775248809869879968869 8564770359151850602494163)
          ·
            refine ⟨12847155538727775903741245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564770359151850602494163 12847155538727775903741245)
            ·
              refine ⟨4817683327022915963902967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12847155538727775903741245 4817683327022915963902967)
              ·
                refine ⟨7226524990534373945854451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817683327022915963902967 7226524990534373945854451)
                ·
                  refine ⟨10839787485801560918781677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226524990534373945854451 10839787485801560918781677)
                  ·
                    refine ⟨4064920307175585344543129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10839787485801560918781677 4064920307175585344543129)
                    ·
                      refine ⟨3048690230381689008407347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064920307175585344543129 3048690230381689008407347)
                      ·
                        rfl

theorem cell23_5937303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_5937303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937303 prefixEnd_5937303 := by exact prefixLift 5937303
  have htrace : WordTrace (prefixWord ++ tailWord_5937303) baseStart_5937303 baseEnd_5937303 := by
    simpa [prefixWord, tailWord_5937303, baseEnd_5937303] using wordTrace_append hprefix tailTrace_5937303
  have hstable : (prefixWord ++ tailWord_5937303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937303).length < 2 ^ (prefixWord ++ tailWord_5937303).sum := by decide
  have hdescent : baseEnd_5937303 < baseStart_5937303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937326 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5937326 : Nat := 118140960795 + 5937326 * 2 ^ 59
def prefixEnd_5937326 : Nat := 4983230072969 + 3 ^ 40 * 5937326 * 2
def baseEnd_5937326 : Nat := 1016234013478914139473247

theorem tailTrace_5937326 : CollatzResearch.WordTrace tailWord_5937326 prefixEnd_5937326 1016234013478914139473247 := by
  unfold tailWord_5937326
  simp only [CollatzResearch.WordTrace]
  refine ⟨27069008711011173924510979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144368046458726260930725221 27069008711011173924510979)
  ·
    refine ⟨40603513066516760886766469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27069008711011173924510979 40603513066516760886766469)
    ·
      refine ⟨7613158699971892666268713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40603513066516760886766469 7613158699971892666268713)
      ·
        refine ⟨5709869024978919499701535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7613158699971892666268713 5709869024978919499701535)
        ·
          refine ⟨8564803537468379249552303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709869024978919499701535 8564803537468379249552303)
          ·
            refine ⟨12847205306202568874328455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564803537468379249552303 12847205306202568874328455)
            ·
              refine ⟨19270807959303853311492683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12847205306202568874328455 19270807959303853311492683)
              ·
                refine ⟨28906211938955779967239025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19270807959303853311492683 28906211938955779967239025)
                ·
                  refine ⟨21679658954216834975429269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28906211938955779967239025 21679658954216834975429269)
                  ·
                    refine ⟨1016234013478914139473247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21679658954216834975429269 1016234013478914139473247)
                    ·
                      rfl

theorem cell23_5937326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5937326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937326 prefixEnd_5937326 := by exact prefixLift 5937326
  have htrace : WordTrace (prefixWord ++ tailWord_5937326) baseStart_5937326 baseEnd_5937326 := by
    simpa [prefixWord, tailWord_5937326, baseEnd_5937326] using wordTrace_append hprefix tailTrace_5937326
  have hstable : (prefixWord ++ tailWord_5937326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937326).length < 2 ^ (prefixWord ++ tailWord_5937326).sum := by decide
  have hdescent : baseEnd_5937326 < baseStart_5937326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937329 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5937329 : Nat := 118140960795 + 5937329 * 2 ^ 59
def prefixEnd_5937329 : Nat := 4983230072969 + 3 ^ 40 * 5937329 * 2
def baseEnd_5937329 : Nat := 3048703580878705906682227

theorem tailTrace_5937329 : CollatzResearch.WordTrace tailWord_5937329 prefixEnd_5937329 3048703580878705906682227 := by
  unfold tailWord_5937329
  simp only [CollatzResearch.WordTrace]
  refine ⟨216552179107078522908447041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144368119404719015272298027 216552179107078522908447041)
  ·
    refine ⟨162414134330308892181335281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216552179107078522908447041 162414134330308892181335281)
    ·
      refine ⟨121810600747731669136001461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162414134330308892181335281 121810600747731669136001461)
      ·
        refine ⟨11419743820099843981500137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121810600747731669136001461 11419743820099843981500137)
        ·
          refine ⟨8564807865074882986125103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11419743820099843981500137 8564807865074882986125103)
          ·
            refine ⟨12847211797612324479187655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564807865074882986125103 12847211797612324479187655)
            ·
              refine ⟨19270817696418486718781483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12847211797612324479187655 19270817696418486718781483)
              ·
                refine ⟨28906226544627730078172225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19270817696418486718781483 28906226544627730078172225)
                ·
                  refine ⟨21679669908470797558629169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28906226544627730078172225 21679669908470797558629169)
                  ·
                    refine ⟨16259752431353098168971877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21679669908470797558629169 16259752431353098168971877)
                    ·
                      refine ⟨3048703580878705906682227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16259752431353098168971877 3048703580878705906682227)
                      ·
                        rfl

theorem cell23_5937329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5937329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937329 prefixEnd_5937329 := by exact prefixLift 5937329
  have htrace : WordTrace (prefixWord ++ tailWord_5937329) baseStart_5937329 baseEnd_5937329 := by
    simpa [prefixWord, tailWord_5937329, baseEnd_5937329] using wordTrace_append hprefix tailTrace_5937329
  have hstable : (prefixWord ++ tailWord_5937329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937329).length < 2 ^ (prefixWord ++ tailWord_5937329).sum := by decide
  have hdescent : baseEnd_5937329 < baseStart_5937329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937333 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5937333 : Nat := 118140960795 + 5937333 * 2 ^ 59
def prefixEnd_5937333 : Nat := 4983230072969 + 3 ^ 40 * 5937333 * 2
def baseEnd_5937333 : Nat := 3048705634801323891032209

theorem tailTrace_5937333 : CollatzResearch.WordTrace tailWord_5937333 prefixEnd_5937333 3048705634801323891032209 := by
  unfold tailWord_5937333
  simp only [CollatzResearch.WordTrace]
  refine ⟨216552324999064031591592653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144368216666042687727728435 216552324999064031591592653)
  ·
    refine ⟨81207121874649011846847245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216552324999064031591592653 81207121874649011846847245)
    ·
      refine ⟨30452670702993379442567717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81207121874649011846847245 30452670702993379442567717)
      ·
        refine ⟨5709875756811258645481447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30452670702993379442567717 5709875756811258645481447)
        ·
          refine ⟨8564813635216887968222171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709875756811258645481447 8564813635216887968222171)
          ·
            refine ⟨12847220452825331952333257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564813635216887968222171 12847220452825331952333257)
            ·
              refine ⟨9635415339618998964249943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12847220452825331952333257 9635415339618998964249943)
              ·
                refine ⟨14453123009428498446374915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9635415339618998964249943 14453123009428498446374915)
                ·
                  refine ⟨21679684514142747669562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14453123009428498446374915 21679684514142747669562373)
                  ·
                    refine ⟨4064940846401765188042945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21679684514142747669562373 4064940846401765188042945)
                    ·
                      refine ⟨3048705634801323891032209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4064940846401765188042945 3048705634801323891032209)
                      ·
                        rfl

theorem cell23_5937333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5937333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937333 prefixEnd_5937333 := by exact prefixLift 5937333
  have htrace : WordTrace (prefixWord ++ tailWord_5937333) baseStart_5937333 baseEnd_5937333 := by
    simpa [prefixWord, tailWord_5937333, baseEnd_5937333] using wordTrace_append hprefix tailTrace_5937333
  have hstable : (prefixWord ++ tailWord_5937333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937333).length < 2 ^ (prefixWord ++ tailWord_5937333).sum := by decide
  have hdescent : baseEnd_5937333 < baseStart_5937333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937366 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5937366 : Nat := 118140960795 + 5937366 * 2 ^ 59
def prefixEnd_5937366 : Nat := 4983230072969 + 3 ^ 40 * 5937366 * 2
def baseEnd_5937366 : Nat := 3048722579662922261919557

theorem tailTrace_5937366 : CollatzResearch.WordTrace tailWord_5937366 prefixEnd_5937366 3048722579662922261919557 := by
  unfold tailWord_5937366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534595537996529889221497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144369019071962985485029301 13534595537996529889221497)
  ·
    refine ⟨10150946653497397416916123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13534595537996529889221497 10150946653497397416916123)
    ·
      refine ⟨15226419980246096125374185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150946653497397416916123 15226419980246096125374185)
      ·
        refine ⟨11419814985184572094030639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15226419980246096125374185 11419814985184572094030639)
        ·
          refine ⟨17129722477776858141045959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11419814985184572094030639 17129722477776858141045959)
          ·
            refine ⟨25694583716665287211568939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17129722477776858141045959 25694583716665287211568939)
            ·
              refine ⟨38541875574997930817353409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25694583716665287211568939 38541875574997930817353409)
              ·
                refine ⟨28906406681248448113015057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38541875574997930817353409 28906406681248448113015057)
                ·
                  refine ⟨21679805010936336084761293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28906406681248448113015057 21679805010936336084761293)
                  ·
                    refine ⟨8129926879101126031785485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21679805010936336084761293 8129926879101126031785485)
                    ·
                      refine ⟨3048722579662922261919557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129926879101126031785485 3048722579662922261919557)
                      ·
                        rfl

theorem cell23_5937366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5937366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937366 prefixEnd_5937366 := by exact prefixLift 5937366
  have htrace : WordTrace (prefixWord ++ tailWord_5937366) baseStart_5937366 baseEnd_5937366 := by
    simpa [prefixWord, tailWord_5937366, baseEnd_5937366] using wordTrace_append hprefix tailTrace_5937366
  have hstable : (prefixWord ++ tailWord_5937366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937366).length < 2 ^ (prefixWord ++ tailWord_5937366).sum := by decide
  have hdescent : baseEnd_5937366 < baseStart_5937366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937409 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_5937409 : Nat := 118140960795 + 5937409 * 2 ^ 59
def prefixEnd_5937409 : Nat := 4983230072969 + 3 ^ 40 * 5937409 * 2
def baseEnd_5937409 : Nat := 3048744659331065593681859

theorem tailTrace_5937409 : CollatzResearch.WordTrace tailWord_5937409 prefixEnd_5937409 3048744659331065593681859 := by
  unfold tailWord_5937409
  simp only [CollatzResearch.WordTrace]
  refine ⟨216555096946788696571359281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144370064631192464380906187 216555096946788696571359281)
  ·
    refine ⟨162416322710091522428519461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216555096946788696571359281 162416322710091522428519461)
    ·
      refine ⟨30453060508142160455347399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162416322710091522428519461 30453060508142160455347399)
      ·
        refine ⟨45679590762213240683021099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30453060508142160455347399 45679590762213240683021099)
        ·
          refine ⟨68519386143319861024531649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45679590762213240683021099 68519386143319861024531649)
          ·
            refine ⟨51389539607489895768398737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68519386143319861024531649 51389539607489895768398737)
            ·
              refine ⟨38542154705617421826299053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51389539607489895768398737 38542154705617421826299053)
              ·
                refine ⟨14453308014606533184862145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38542154705617421826299053 14453308014606533184862145)
                ·
                  refine ⟨10839981010954899888646609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14453308014606533184862145 10839981010954899888646609)
                  ·
                    refine ⟨8129985758216174916484957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10839981010954899888646609 8129985758216174916484957)
                    ·
                      refine ⟨3048744659331065593681859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8129985758216174916484957 3048744659331065593681859)
                      ·
                        rfl

theorem cell23_5937409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_5937409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937409 prefixEnd_5937409 := by exact prefixLift 5937409
  have htrace : WordTrace (prefixWord ++ tailWord_5937409) baseStart_5937409 baseEnd_5937409 := by
    simpa [prefixWord, tailWord_5937409, baseEnd_5937409] using wordTrace_append hprefix tailTrace_5937409
  have hstable : (prefixWord ++ tailWord_5937409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937409).length < 2 ^ (prefixWord ++ tailWord_5937409).sum := by decide
  have hdescent : baseEnd_5937409 < baseStart_5937409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937466 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_5937466 : Nat := 118140960795 + 5937466 * 2 ^ 59
def prefixEnd_5937466 : Nat := 4983230072969 + 3 ^ 40 * 5937466 * 2
def baseEnd_5937466 : Nat := 3048773927728371870669097

theorem tailTrace_5937466 : CollatzResearch.WordTrace tailWord_5937466 prefixEnd_5937466 3048773927728371870669097 := by
  unfold tailWord_5937466
  simp only [CollatzResearch.WordTrace]
  refine ⟨54139293976895548826546063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144371450605054796870789501 54139293976895548826546063)
  ·
    refine ⟨81208940965343323239819095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54139293976895548826546063 81208940965343323239819095)
    ·
      refine ⟨121813411448014984859728643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81208940965343323239819095 121813411448014984859728643)
      ·
        refine ⟨182720117172022477289592965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121813411448014984859728643 182720117172022477289592965)
        ·
          refine ⟨34260021969754214491798681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182720117172022477289592965 34260021969754214491798681)
          ·
            refine ⟨25695016477315660868849011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34260021969754214491798681 25695016477315660868849011)
            ·
              refine ⟨38542524715973491303273517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695016477315660868849011 38542524715973491303273517)
              ·
                refine ⟨14453446768490059238727569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38542524715973491303273517 14453446768490059238727569)
                ·
                  refine ⟨10840085076367544429045677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14453446768490059238727569 10840085076367544429045677)
                  ·
                    refine ⟨4065031903637829160892129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10840085076367544429045677 4065031903637829160892129)
                    ·
                      refine ⟨3048773927728371870669097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065031903637829160892129 3048773927728371870669097)
                      ·
                        rfl

theorem cell23_5937466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_5937466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937466 prefixEnd_5937466 := by exact prefixLift 5937466
  have htrace : WordTrace (prefixWord ++ tailWord_5937466) baseStart_5937466 baseEnd_5937466 := by
    simpa [prefixWord, tailWord_5937466, baseEnd_5937466] using wordTrace_append hprefix tailTrace_5937466
  have hstable : (prefixWord ++ tailWord_5937466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937466).length < 2 ^ (prefixWord ++ tailWord_5937466).sum := by decide
  have hdescent : baseEnd_5937466 < baseStart_5937466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937490 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_5937490 : Nat := 118140960795 + 5937490 * 2 ^ 59
def prefixEnd_5937490 : Nat := 4983230072969 + 3 ^ 40 * 5937490 * 2
def baseEnd_5937490 : Nat := 3048786251264079776768987

theorem tailTrace_5937490 : CollatzResearch.WordTrace tailWord_5937490 prefixEnd_5937490 3048786251264079776768987 := by
  unfold tailWord_5937490
  simp only [CollatzResearch.WordTrace]
  refine ⟨54139512814873811851264481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144372034172996831603371949 54139512814873811851264481)
  ·
    refine ⟨40604634611155358888448361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54139512814873811851264481 40604634611155358888448361)
    ·
      refine ⟨30453475958366519166336271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40604634611155358888448361 30453475958366519166336271)
      ·
        refine ⟨45680213937549778749504407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30453475958366519166336271 45680213937549778749504407)
        ·
          refine ⟨68520320906324668124256611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45680213937549778749504407 68520320906324668124256611)
          ·
            refine ⟨102780481359487002186384917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68520320906324668124256611 102780481359487002186384917)
            ·
              refine ⟨4817835063725953227486793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102780481359487002186384917 4817835063725953227486793)
              ·
                refine ⟨3613376297794464920615095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817835063725953227486793 3613376297794464920615095)
                ·
                  refine ⟨5420064446691697380922643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613376297794464920615095 5420064446691697380922643)
                  ·
                    refine ⟨8130096670037546071383965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5420064446691697380922643 8130096670037546071383965)
                    ·
                      refine ⟨3048786251264079776768987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130096670037546071383965 3048786251264079776768987)
                      ·
                        rfl

theorem cell23_5937490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_5937490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937490 prefixEnd_5937490 := by exact prefixLift 5937490
  have htrace : WordTrace (prefixWord ++ tailWord_5937490) baseStart_5937490 baseEnd_5937490 := by
    simpa [prefixWord, tailWord_5937490, baseEnd_5937490] using wordTrace_append hprefix tailTrace_5937490
  have hstable : (prefixWord ++ tailWord_5937490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937490).length < 2 ^ (prefixWord ++ tailWord_5937490).sum := by decide
  have hdescent : baseEnd_5937490 < baseStart_5937490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937506 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5937506 : Nat := 118140960795 + 5937506 * 2 ^ 59
def prefixEnd_5937506 : Nat := 4983230072969 + 3 ^ 40 * 5937506 * 2
def baseEnd_5937506 : Nat := 1016264822318183904722971

theorem tailTrace_5937506 : CollatzResearch.WordTrace tailWord_5937506 prefixEnd_5937506 1016264822318183904722971 := by
  unfold tailWord_5937506
  simp only [CollatzResearch.WordTrace]
  refine ⟨54139658706859320534410093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144372423218291521425093581 54139658706859320534410093)
  ·
    refine ⟨20302372015072245200403785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54139658706859320534410093 20302372015072245200403785)
    ·
      refine ⟨15226779011304183900302839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20302372015072245200403785 15226779011304183900302839)
      ·
        refine ⟨22840168516956275850454259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15226779011304183900302839 22840168516956275850454259)
        ·
          refine ⟨34260252775434413775681389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22840168516956275850454259 34260252775434413775681389)
          ·
            refine ⟨12847594790787905165880521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34260252775434413775681389 12847594790787905165880521)
            ·
              refine ⟨9635696093090928874410391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12847594790787905165880521 9635696093090928874410391)
              ·
                refine ⟨14453544139636393311615587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9635696093090928874410391 14453544139636393311615587)
                ·
                  refine ⟨21680316209454589967423381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14453544139636393311615587 21680316209454589967423381)
                  ·
                    refine ⟨1016264822318183904722971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21680316209454589967423381 1016264822318183904722971)
                    ·
                      rfl

theorem cell23_5937506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5937506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937506 prefixEnd_5937506 := by exact prefixLift 5937506
  have htrace : WordTrace (prefixWord ++ tailWord_5937506) baseStart_5937506 baseEnd_5937506 := by
    simpa [prefixWord, tailWord_5937506, baseEnd_5937506] using wordTrace_append hprefix tailTrace_5937506
  have hstable : (prefixWord ++ tailWord_5937506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937506).length < 2 ^ (prefixWord ++ tailWord_5937506).sum := by decide
  have hdescent : baseEnd_5937506 < baseStart_5937506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937509 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5937509 : Nat := 118140960795 + 5937509 * 2 ^ 59
def prefixEnd_5937509 : Nat := 4983230072969 + 3 ^ 40 * 5937509 * 2
def baseEnd_5937509 : Nat := 3048796007396515202431399

theorem tailTrace_5937509 : CollatzResearch.WordTrace tailWord_5937509 prefixEnd_5937509 3048796007396515202431399 := by
  unfold tailWord_5937509
  simp only [CollatzResearch.WordTrace]
  refine ⟨216558744246426413649999581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144372496164284275766666387 216558744246426413649999581)
  ·
    refine ⟨81209529092409905118749843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216558744246426413649999581 81209529092409905118749843)
    ·
      refine ⟨121814293638614857678124765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81209529092409905118749843 121814293638614857678124765)
      ·
        refine ⟨45680360114480571629296787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121814293638614857678124765 45680360114480571629296787)
        ·
          refine ⟨68520540171720857443945181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45680360114480571629296787 68520540171720857443945181)
          ·
            refine ⟨25695202564395321541479443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68520540171720857443945181 25695202564395321541479443)
            ·
              refine ⟨38542803846592982312219165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695202564395321541479443 38542803846592982312219165)
              ·
                refine ⟨14453551442472368367082187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38542803846592982312219165 14453551442472368367082187)
                ·
                  refine ⟨21680327163708552550623281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14453551442472368367082187 21680327163708552550623281)
                  ·
                    refine ⟨16260245372781414412967461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21680327163708552550623281 16260245372781414412967461)
                    ·
                      refine ⟨3048796007396515202431399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16260245372781414412967461 3048796007396515202431399)
                      ·
                        rfl

theorem cell23_5937509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5937509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937509 prefixEnd_5937509 := by exact prefixLift 5937509
  have htrace : WordTrace (prefixWord ++ tailWord_5937509) baseStart_5937509 baseEnd_5937509 := by
    simpa [prefixWord, tailWord_5937509, baseEnd_5937509] using wordTrace_append hprefix tailTrace_5937509
  have hstable : (prefixWord ++ tailWord_5937509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937509).length < 2 ^ (prefixWord ++ tailWord_5937509).sum := by decide
  have hdescent : baseEnd_5937509 < baseStart_5937509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937532 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_5937532 : Nat := 118140960795 + 5937532 * 2 ^ 59
def prefixEnd_5937532 : Nat := 4983230072969 + 3 ^ 40 * 5937532 * 2
def baseEnd_5937532 : Nat := 1016269272483856204147931

theorem tailTrace_5937532 : CollatzResearch.WordTrace tailWord_5937532 prefixEnd_5937532 1016269272483856204147931 := by
  unfold tailWord_5937532
  simp only [CollatzResearch.WordTrace]
  refine ⟨108279791562671544289043425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144373055416895392385391233 108279791562671544289043425)
  ·
    refine ⟨81209843672003658216782569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108279791562671544289043425 81209843672003658216782569)
    ·
      refine ⟨60907382754002743662586927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81209843672003658216782569 60907382754002743662586927)
      ·
        refine ⟨91361074131004115493880391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60907382754002743662586927 91361074131004115493880391)
        ·
          refine ⟨137041611196506173240820587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91361074131004115493880391 137041611196506173240820587)
          ·
            refine ⟨205562416794759259861230881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137041611196506173240820587 205562416794759259861230881)
            ·
              refine ⟨154171812596069444895923161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205562416794759259861230881 154171812596069444895923161)
              ·
                refine ⟨115628859447052083671942371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154171812596069444895923161 115628859447052083671942371)
                ·
                  refine ⟨173443289170578125507913557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115628859447052083671942371 173443289170578125507913557)
                  ·
                    refine ⟨1016269272483856204147931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 173443289170578125507913557 1016269272483856204147931)
                    ·
                      rfl

theorem cell23_5937532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_5937532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937532 prefixEnd_5937532 := by exact prefixLift 5937532
  have htrace : WordTrace (prefixWord ++ tailWord_5937532) baseStart_5937532 baseEnd_5937532 := by
    simpa [prefixWord, tailWord_5937532, baseEnd_5937532] using wordTrace_append hprefix tailTrace_5937532
  have hstable : (prefixWord ++ tailWord_5937532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937532).length < 2 ^ (prefixWord ++ tailWord_5937532).sum := by decide
  have hdescent : baseEnd_5937532 < baseStart_5937532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937533 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_5937533 : Nat := 118140960795 + 5937533 * 2 ^ 59
def prefixEnd_5937533 : Nat := 4983230072969 + 3 ^ 40 * 5937533 * 2
def baseEnd_5937533 : Nat := 3048808330932223108531289

theorem tailTrace_5937533 : CollatzResearch.WordTrace tailWord_5937533 prefixEnd_5937533 3048808330932223108531289 := by
  unfold tailWord_5937533
  simp only [CollatzResearch.WordTrace]
  refine ⟨216559619598339465748873253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144373079732226310499248835 216559619598339465748873253)
  ·
    refine ⟨40604928674688649827913735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216559619598339465748873253 40604928674688649827913735)
    ·
      refine ⟨60907393012032974741870603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40604928674688649827913735 60907393012032974741870603)
      ·
        refine ⟨91361089518049462112805905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60907393012032974741870603 91361089518049462112805905)
        ·
          refine ⟨68520817138537096584604429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91361089518049462112805905 68520817138537096584604429)
          ·
            refine ⟨25695306426951411219226661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68520817138537096584604429 25695306426951411219226661)
            ·
              refine ⟨4817869955053389603604999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25695306426951411219226661 4817869955053389603604999)
              ·
                refine ⟨7226804932580084405407499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817869955053389603604999 7226804932580084405407499)
                ·
                  refine ⟨10840207398870126608111249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226804932580084405407499 10840207398870126608111249)
                  ·
                    refine ⟨8130155549152594956083437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10840207398870126608111249 8130155549152594956083437)
                    ·
                      refine ⟨3048808330932223108531289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130155549152594956083437 3048808330932223108531289)
                      ·
                        rfl

theorem cell23_5937533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_5937533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937533 prefixEnd_5937533 := by exact prefixLift 5937533
  have htrace : WordTrace (prefixWord ++ tailWord_5937533) baseStart_5937533 baseEnd_5937533 := by
    simpa [prefixWord, tailWord_5937533, baseEnd_5937533] using wordTrace_append hprefix tailTrace_5937533
  have hstable : (prefixWord ++ tailWord_5937533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937533).length < 2 ^ (prefixWord ++ tailWord_5937533).sum := by decide
  have hdescent : baseEnd_5937533 < baseStart_5937533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937573 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_5937573 : Nat := 118140960795 + 5937573 * 2 ^ 59
def prefixEnd_5937573 : Nat := 4983230072969 + 3 ^ 40 * 5937573 * 2
def baseEnd_5937573 : Nat := 3048828870158402952031105

theorem tailTrace_5937573 : CollatzResearch.WordTrace tailWord_5937573 prefixEnd_5937573 3048828870158402952031105 := by
  unfold tailWord_5937573
  simp only [CollatzResearch.WordTrace]
  refine ⟨216561078518194552580329373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144374052345463035053552915 216561078518194552580329373)
  ·
    refine ⟨81210404444322957217623515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216561078518194552580329373 81210404444322957217623515)
    ·
      refine ⟨121815606666484435826435273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81210404444322957217623515 121815606666484435826435273)
      ·
        refine ⟨91361704999863326869826455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121815606666484435826435273 91361704999863326869826455)
        ·
          refine ⟨137042557499794990304739683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91361704999863326869826455 137042557499794990304739683)
          ·
            refine ⟨205563836249692485457109525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137042557499794990304739683 205563836249692485457109525)
            ·
              refine ⟨9635804824204335255802009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205563836249692485457109525 9635804824204335255802009)
              ·
                refine ⟨7226853618153251441851507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9635804824204335255802009 7226853618153251441851507)
                ·
                  refine ⟨10840280427229877162777261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226853618153251441851507 10840280427229877162777261)
                  ·
                    refine ⟨4065105160211203936041473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10840280427229877162777261 4065105160211203936041473)
                    ·
                      refine ⟨3048828870158402952031105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065105160211203936041473 3048828870158402952031105)
                      ·
                        rfl

theorem cell23_5937573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_5937573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937573 prefixEnd_5937573 := by exact prefixLift 5937573
  have htrace : WordTrace (prefixWord ++ tailWord_5937573) baseStart_5937573 baseEnd_5937573 := by
    simpa [prefixWord, tailWord_5937573, baseEnd_5937573] using wordTrace_append hprefix tailTrace_5937573
  have hstable : (prefixWord ++ tailWord_5937573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937573).length < 2 ^ (prefixWord ++ tailWord_5937573).sum := by decide
  have hdescent : baseEnd_5937573 < baseStart_5937573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937576 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5937576 : Nat := 118140960795 + 5937576 * 2 ^ 59
def prefixEnd_5937576 : Nat := 4983230072969 + 3 ^ 40 * 5937576 * 2
def baseEnd_5937576 : Nat := 3048830410600366440293591

theorem tailTrace_5937576 : CollatzResearch.WordTrace tailWord_5937576 prefixEnd_5937576 3048830410600366440293591 := by
  unfold tailWord_5937576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108280593968591842046344291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144374125291455789395125721 108280593968591842046344291)
  ·
    refine ⟨162420890952887763069516437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108280593968591842046344291 162420890952887763069516437)
    ·
      refine ⟨7613479263416613893883583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 162420890952887763069516437 7613479263416613893883583)
      ·
        refine ⟨11420218895124920840825375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613479263416613893883583 11420218895124920840825375)
        ·
          refine ⟨17130328342687381261238063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11420218895124920840825375 17130328342687381261238063)
          ·
            refine ⟨25695492514031071891857095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17130328342687381261238063 25695492514031071891857095)
            ·
              refine ⟨38543238771046607837785643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695492514031071891857095 38543238771046607837785643)
              ·
                refine ⟨57814858156569911756678465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38543238771046607837785643 57814858156569911756678465)
                ·
                  refine ⟨43361143617427433817508849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57814858156569911756678465 43361143617427433817508849)
                  ·
                    refine ⟨32520857713070575363131637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43361143617427433817508849 32520857713070575363131637)
                    ·
                      refine ⟨3048830410600366440293591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32520857713070575363131637 3048830410600366440293591)
                      ·
                        rfl

theorem cell23_5937576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5937576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937576 prefixEnd_5937576 := by exact prefixLift 5937576
  have htrace : WordTrace (prefixWord ++ tailWord_5937576) baseStart_5937576 baseEnd_5937576 := by
    simpa [prefixWord, tailWord_5937576, baseEnd_5937576] using wordTrace_append hprefix tailTrace_5937576
  have hstable : (prefixWord ++ tailWord_5937576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937576).length < 2 ^ (prefixWord ++ tailWord_5937576).sum := by decide
  have hdescent : baseEnd_5937576 < baseStart_5937576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937581 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5937581 : Nat := 118140960795 + 5937581 * 2 ^ 59
def prefixEnd_5937581 : Nat := 4983230072969 + 3 ^ 40 * 5937581 * 2
def baseEnd_5937581 : Nat := 3048832978003638920731069

theorem tailTrace_5937581 : CollatzResearch.WordTrace tailWord_5937581 prefixEnd_5937581 3048832978003638920731069 := by
  unfold tailWord_5937581
  simp only [CollatzResearch.WordTrace]
  refine ⟨216561370302165569946620597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144374246868110379964413731 216561370302165569946620597)
  ·
    refine ⟨20302628465828022182495681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216561370302165569946620597 20302628465828022182495681)
    ·
      refine ⟨15226971349371016636871761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20302628465828022182495681 15226971349371016636871761)
      ·
        refine ⟨11420228512028262477653821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15226971349371016636871761 11420228512028262477653821)
        ·
          refine ⟨4282585692010598429120183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11420228512028262477653821 4282585692010598429120183)
          ·
            refine ⟨6423878538015897643680275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282585692010598429120183 6423878538015897643680275)
            ·
              refine ⟨9635817807023846465520413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423878538015897643680275 9635817807023846465520413)
              ·
                refine ⟨3613431677633942424570155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9635817807023846465520413 3613431677633942424570155)
                ·
                  refine ⟨5420147516450913636855233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613431677633942424570155 5420147516450913636855233)
                  ·
                    refine ⟨4065110637338185227641425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5420147516450913636855233 4065110637338185227641425)
                    ·
                      refine ⟨3048832978003638920731069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065110637338185227641425 3048832978003638920731069)
                      ·
                        rfl

theorem cell23_5937581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5937581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937581 prefixEnd_5937581 := by exact prefixLift 5937581
  have htrace : WordTrace (prefixWord ++ tailWord_5937581) baseStart_5937581 baseEnd_5937581 := by
    simpa [prefixWord, tailWord_5937581, baseEnd_5937581] using wordTrace_append hprefix tailTrace_5937581
  have hstable : (prefixWord ++ tailWord_5937581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937581).length < 2 ^ (prefixWord ++ tailWord_5937581).sum := by decide
  have hdescent : baseEnd_5937581 < baseStart_5937581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937586 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_5937586 : Nat := 118140960795 + 5937586 * 2 ^ 59
def prefixEnd_5937586 : Nat := 4983230072969 + 3 ^ 40 * 5937586 * 2
def baseEnd_5937586 : Nat := 3048835545406911401168545

theorem tailTrace_5937586 : CollatzResearch.WordTrace tailWord_5937586 prefixEnd_5937586 3048835545406911401168545 := by
  unfold tailWord_5937586
  simp only [CollatzResearch.WordTrace]
  refine ⟨54140388166786863950138153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144374368444764970533701741 54140388166786863950138153)
  ·
    refine ⟨40605291125090147962603615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54140388166786863950138153 40605291125090147962603615)
    ·
      refine ⟨60907936687635221943905423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40605291125090147962603615 60907936687635221943905423)
      ·
        refine ⟨91361905031452832915858135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60907936687635221943905423 91361905031452832915858135)
        ·
          refine ⟨137042857547179249373787203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91361905031452832915858135 137042857547179249373787203)
          ·
            refine ⟨205564286320768874060680805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137042857547179249373787203 205564286320768874060680805)
            ·
              refine ⟨38543303685144163886377651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205564286320768874060680805 38543303685144163886377651)
              ·
                refine ⟨57814955527716245829566477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38543303685144163886377651 57814955527716245829566477)
                ·
                  refine ⟨21680608322893592186087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57814955527716245829566477 21680608322893592186087429)
                  ·
                    refine ⟨4065114060542548534891393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21680608322893592186087429 4065114060542548534891393)
                    ·
                      refine ⟨3048835545406911401168545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065114060542548534891393 3048835545406911401168545)
                      ·
                        rfl

theorem cell23_5937586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_5937586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937586 prefixEnd_5937586 := by exact prefixLift 5937586
  have htrace : WordTrace (prefixWord ++ tailWord_5937586) baseStart_5937586 baseEnd_5937586 := by
    simpa [prefixWord, tailWord_5937586, baseEnd_5937586] using wordTrace_append hprefix tailTrace_5937586
  have hstable : (prefixWord ++ tailWord_5937586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937586).length < 2 ^ (prefixWord ++ tailWord_5937586).sum := by decide
  have hdescent : baseEnd_5937586 < baseStart_5937586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937603 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 2, 2, 2]
def baseStart_5937603 : Nat := 118140960795 + 5937603 * 2 ^ 59
def prefixEnd_5937603 : Nat := 4983230072969 + 3 ^ 40 * 5937603 * 2
def baseEnd_5937603 : Nat := 3048844274578037834655967

theorem tailTrace_5937603 : CollatzResearch.WordTrace tailWord_5937603 prefixEnd_5937603 3048844274578037834655967 := by
  unfold tailWord_5937603
  simp only [CollatzResearch.WordTrace]
  refine ⟨216562172708085867703921463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144374781805390578469280975 216562172708085867703921463)
  ·
    refine ⟨324843259062128801555882195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216562172708085867703921463 324843259062128801555882195)
    ·
      refine ⟨487264888593193202333823293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324843259062128801555882195 487264888593193202333823293)
      ·
        refine ⟨182724333222447450875183735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487264888593193202333823293 182724333222447450875183735)
        ·
          refine ⟨274086499833671176312775603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182724333222447450875183735 274086499833671176312775603)
          ·
            refine ⟨411129749750506764469163405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274086499833671176312775603 411129749750506764469163405)
            ·
              refine ⟨154173656156440036675936277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411129749750506764469163405 154173656156440036675936277)
              ·
                refine ⟨7226890132333126719184513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154173656156440036675936277 7226890132333126719184513)
                ·
                  refine ⟨5420167599249845039388385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7226890132333126719184513 5420167599249845039388385)
                  ·
                    refine ⟨4065125699437383779541289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5420167599249845039388385 4065125699437383779541289)
                    ·
                      refine ⟨3048844274578037834655967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065125699437383779541289 3048844274578037834655967)
                      ·
                        rfl

theorem cell23_5937603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_5937603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937603 prefixEnd_5937603 := by exact prefixLift 5937603
  have htrace : WordTrace (prefixWord ++ tailWord_5937603) baseStart_5937603 baseEnd_5937603 := by
    simpa [prefixWord, tailWord_5937603, baseEnd_5937603] using wordTrace_append hprefix tailTrace_5937603
  have hstable : (prefixWord ++ tailWord_5937603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937603).length < 2 ^ (prefixWord ++ tailWord_5937603).sum := by decide
  have hdescent : baseEnd_5937603 < baseStart_5937603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937609 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 7]
def baseStart_5937609 : Nat := 118140960795 + 5937609 * 2 ^ 59
def prefixEnd_5937609 : Nat := 4983230072969 + 3 ^ 40 * 5937609 * 2
def baseEnd_5937609 : Nat := 338760817273551645686771

theorem tailTrace_5937609 : CollatzResearch.WordTrace tailWord_5937609 prefixEnd_5937609 338760817273551645686771 := by
  unfold tailWord_5937609
  simp only [CollatzResearch.WordTrace]
  refine ⟨216562391546064130728639881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144374927697376087152426587 216562391546064130728639881)
  ·
    refine ⟨162421793659548098046479911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216562391546064130728639881 162421793659548098046479911)
    ·
      refine ⟨243632690489322147069719867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162421793659548098046479911 243632690489322147069719867)
      ·
        refine ⟨365449035733983220604579801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243632690489322147069719867 365449035733983220604579801)
        ·
          refine ⟨274086776800487415453434851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365449035733983220604579801 274086776800487415453434851)
          ·
            refine ⟨411130165200731123180152277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274086776800487415453434851 411130165200731123180152277)
            ·
              refine ⟨9635863246892135699534819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 411130165200731123180152277 9635863246892135699534819)
              ·
                refine ⟨14453794870338203549302229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9635863246892135699534819 14453794870338203549302229)
                ·
                  refine ⟨338760817273551645686771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14453794870338203549302229 338760817273551645686771)
                  ·
                    rfl

theorem cell23_5937609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_5937609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937609 prefixEnd_5937609 := by exact prefixLift 5937609
  have htrace : WordTrace (prefixWord ++ tailWord_5937609) baseStart_5937609 baseEnd_5937609 := by
    simpa [prefixWord, tailWord_5937609, baseEnd_5937609] using wordTrace_append hprefix tailTrace_5937609
  have hstable : (prefixWord ++ tailWord_5937609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937609).length < 2 ^ (prefixWord ++ tailWord_5937609).sum := by decide
  have hdescent : baseEnd_5937609 < baseStart_5937609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937619 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3]
def baseStart_5937619 : Nat := 118140960795 + 5937619 * 2 ^ 59
def prefixEnd_5937619 : Nat := 4983230072969 + 3 ^ 40 * 5937619 * 2
def baseEnd_5937619 : Nat := 3048852490268509772055893

theorem tailTrace_5937619 : CollatzResearch.WordTrace tailWord_5937619 prefixEnd_5937619 3048852490268509772055893 := by
  unfold tailWord_5937619
  simp only [CollatzResearch.WordTrace]
  refine ⟨216562756276027902436503911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144375170850685268291002607 216562756276027902436503911)
  ·
    refine ⟨324844134414041853654755867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216562756276027902436503911 324844134414041853654755867)
    ·
      refine ⟨487266201621062780482133801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324844134414041853654755867 487266201621062780482133801)
      ·
        refine ⟨365449651215797085361600351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487266201621062780482133801 365449651215797085361600351)
        ·
          refine ⟨548174476823695628042400527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365449651215797085361600351 548174476823695628042400527)
          ·
            refine ⟨822261715235543442063600791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548174476823695628042400527 822261715235543442063600791)
            ·
              refine ⟨1233392572853315163095401187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822261715235543442063600791 1233392572853315163095401187)
              ·
                refine ⟨1850088859279972744643101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233392572853315163095401187 1850088859279972744643101781)
                ·
                  refine ⟨21680728819687180601286349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1850088859279972744643101781 21680728819687180601286349)
                  ·
                    refine ⟨8130273307382692725482381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21680728819687180601286349 8130273307382692725482381)
                    ·
                      refine ⟨3048852490268509772055893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130273307382692725482381 3048852490268509772055893)
                      ·
                        rfl

theorem cell23_5937619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_5937619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937619 prefixEnd_5937619 := by exact prefixLift 5937619
  have htrace : WordTrace (prefixWord ++ tailWord_5937619) baseStart_5937619 baseEnd_5937619 := by
    simpa [prefixWord, tailWord_5937619, baseEnd_5937619] using wordTrace_append hprefix tailTrace_5937619
  have hstable : (prefixWord ++ tailWord_5937619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937619).length < 2 ^ (prefixWord ++ tailWord_5937619).sum := by decide
  have hdescent : baseEnd_5937619 < baseStart_5937619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937649 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_5937649 : Nat := 118140960795 + 5937649 * 2 ^ 59
def prefixEnd_5937649 : Nat := 4983230072969 + 3 ^ 40 * 5937649 * 2
def baseEnd_5937649 : Nat := 3048867894688144654680755

theorem tailTrace_5937649 : CollatzResearch.WordTrace tailWord_5937649 prefixEnd_5937649 3048867894688144654680755 := by
  unfold tailWord_5937649
  simp only [CollatzResearch.WordTrace]
  refine ⟨216563850465919217560096001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144375900310612811706730667 216563850465919217560096001)
  ·
    refine ⟨162422887849439413170072001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216563850465919217560096001 162422887849439413170072001)
    ·
      refine ⟨121817165887079559877554001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162422887849439413170072001 121817165887079559877554001)
      ·
        refine ⟨91362874415309669908165501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121817165887079559877554001 91362874415309669908165501)
        ·
          refine ⟨34261077905741126215562063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91362874415309669908165501 34261077905741126215562063)
          ·
            refine ⟨51391616858611689323343095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34261077905741126215562063 51391616858611689323343095)
            ·
              refine ⟨77087425287917533985014643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51391616858611689323343095 77087425287917533985014643)
              ·
                refine ⟨115631137931876300977521965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77087425287917533985014643 115631137931876300977521965)
                ·
                  refine ⟨43361676724453612866570737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115631137931876300977521965 43361676724453612866570737)
                  ·
                    refine ⟨32521257543340209649928053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43361676724453612866570737 32521257543340209649928053)
                    ·
                      refine ⟨3048867894688144654680755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32521257543340209649928053 3048867894688144654680755)
                      ·
                        rfl

theorem cell23_5937649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_5937649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937649 prefixEnd_5937649 := by exact prefixLift 5937649
  have htrace : WordTrace (prefixWord ++ tailWord_5937649) baseStart_5937649 baseEnd_5937649 := by
    simpa [prefixWord, tailWord_5937649, baseEnd_5937649] using wordTrace_append hprefix tailTrace_5937649
  have hstable : (prefixWord ++ tailWord_5937649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937649).length < 2 ^ (prefixWord ++ tailWord_5937649).sum := by decide
  have hdescent : baseEnd_5937649 < baseStart_5937649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937689 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_5937689 : Nat := 118140960795 + 5937689 * 2 ^ 59
def prefixEnd_5937689 : Nat := 4983230072969 + 3 ^ 40 * 5937689 * 2
def baseEnd_5937689 : Nat := 3048888433914324498180571

theorem tailTrace_5937689 : CollatzResearch.WordTrace tailWord_5937689 prefixEnd_5937689 3048888433914324498180571 := by
  unfold tailWord_5937689
  simp only [CollatzResearch.WordTrace]
  refine ⟨216565309385774304391552121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144376872923849536261034747 216565309385774304391552121)
  ·
    refine ⟨162423982039330728293664091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216565309385774304391552121 162423982039330728293664091)
    ·
      refine ⟨243635973058996092440496137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162423982039330728293664091 243635973058996092440496137)
      ·
        refine ⟨182726979794247069330372103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243635973058996092440496137 182726979794247069330372103)
        ·
          refine ⟨274090469691370603995558155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182726979794247069330372103 274090469691370603995558155)
          ·
            refine ⟨411135704537055905993337233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274090469691370603995558155 411135704537055905993337233)
            ·
              refine ⟨308351778402791929495002925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411135704537055905993337233 308351778402791929495002925)
              ·
                refine ⟨115631916901046973560626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308351778402791929495002925 115631916901046973560626097)
                ·
                  refine ⟨86723937675785230170469573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115631916901046973560626097 86723937675785230170469573)
                  ·
                    refine ⟨16260738314209730656963045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86723937675785230170469573 16260738314209730656963045)
                    ·
                      refine ⟨3048888433914324498180571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16260738314209730656963045 3048888433914324498180571)
                      ·
                        rfl

theorem cell23_5937689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_5937689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937689 prefixEnd_5937689 := by exact prefixLift 5937689
  have htrace : WordTrace (prefixWord ++ tailWord_5937689) baseStart_5937689 baseEnd_5937689 := by
    simpa [prefixWord, tailWord_5937689, baseEnd_5937689] using wordTrace_append hprefix tailTrace_5937689
  have hstable : (prefixWord ++ tailWord_5937689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937689).length < 2 ^ (prefixWord ++ tailWord_5937689).sum := by decide
  have hdescent : baseEnd_5937689 < baseStart_5937689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937693 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_5937693 : Nat := 118140960795 + 5937693 * 2 ^ 59
def prefixEnd_5937693 : Nat := 4983230072969 + 3 ^ 40 * 5937693 * 2
def baseEnd_5937693 : Nat := 3048890487836942482530553

theorem tailTrace_5937693 : CollatzResearch.WordTrace tailWord_5937693 prefixEnd_5937693 3048890487836942482530553 := by
  unfold tailWord_5937693
  simp only [CollatzResearch.WordTrace]
  refine ⟨216565455277759813074697733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144376970185173208716465155 216565455277759813074697733)
  ·
    refine ⟨40606022864579964951505825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216565455277759813074697733 40606022864579964951505825)
    ·
      refine ⟨30454517148434973713629369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40606022864579964951505825 30454517148434973713629369)
      ·
        refine ⟨22840887861326230285222027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30454517148434973713629369 22840887861326230285222027)
        ·
          refine ⟨34261331791989345427833041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22840887861326230285222027 34261331791989345427833041)
          ·
            refine ⟨25695998843992009070874781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34261331791989345427833041 25695998843992009070874781)
            ·
              refine ⟨9635999566497003401578043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25695998843992009070874781 9635999566497003401578043)
              ·
                refine ⟨14453999349745505102367065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9635999566497003401578043 14453999349745505102367065)
                ·
                  refine ⟨10840499512309128826775299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14453999349745505102367065 10840499512309128826775299)
                  ·
                    refine ⟨16260749268463693240162949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10840499512309128826775299 16260749268463693240162949)
                    ·
                      refine ⟨3048890487836942482530553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16260749268463693240162949 3048890487836942482530553)
                      ·
                        rfl

theorem cell23_5937693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_5937693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937693 prefixEnd_5937693 := by exact prefixLift 5937693
  have htrace : WordTrace (prefixWord ++ tailWord_5937693) baseStart_5937693 baseEnd_5937693 := by
    simpa [prefixWord, tailWord_5937693, baseEnd_5937693] using wordTrace_append hprefix tailTrace_5937693
  have hstable : (prefixWord ++ tailWord_5937693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937693).length < 2 ^ (prefixWord ++ tailWord_5937693).sum := by decide
  have hdescent : baseEnd_5937693 < baseStart_5937693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937706 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5937706 : Nat := 118140960795 + 5937706 * 2 ^ 59
def prefixEnd_5937706 : Nat := 4983230072969 + 3 ^ 40 * 5937706 * 2
def baseEnd_5937706 : Nat := 3048897163085450931667993

theorem tailTrace_5937706 : CollatzResearch.WordTrace tailWord_5937706 prefixEnd_5937706 3048897163085450931667993 := by
  unfold tailWord_5937706
  simp only [CollatzResearch.WordTrace]
  refine ⟨54141482356678179073730243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144377286284475144196613981 54141482356678179073730243)
  ·
    refine ⟨81212223535017268610595365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54141482356678179073730243 81212223535017268610595365)
    ·
      refine ⟨15227291912815737864486631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81212223535017268610595365 15227291912815737864486631)
      ·
        refine ⟨22840937869223606796729947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227291912815737864486631 22840937869223606796729947)
        ·
          refine ⟨34261406803835410195094921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22840937869223606796729947 34261406803835410195094921)
          ·
            refine ⟨25696055102876557646321191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34261406803835410195094921 25696055102876557646321191)
            ·
              refine ⟨38544082654314836469481787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25696055102876557646321191 38544082654314836469481787)
              ·
                refine ⟨57816123981472254704222681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38544082654314836469481787 57816123981472254704222681)
                ·
                  refine ⟨43362092986104191028167011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57816123981472254704222681 43362092986104191028167011)
                  ·
                    refine ⟨65043139479156286542250517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43362092986104191028167011 65043139479156286542250517)
                    ·
                      refine ⟨3048897163085450931667993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65043139479156286542250517 3048897163085450931667993)
                      ·
                        rfl

theorem cell23_5937706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5937706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937706 prefixEnd_5937706 := by exact prefixLift 5937706
  have htrace : WordTrace (prefixWord ++ tailWord_5937706) baseStart_5937706 baseEnd_5937706 := by
    simpa [prefixWord, tailWord_5937706, baseEnd_5937706] using wordTrace_append hprefix tailTrace_5937706
  have hstable : (prefixWord ++ tailWord_5937706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937706).length < 2 ^ (prefixWord ++ tailWord_5937706).sum := by decide
  have hdescent : baseEnd_5937706 < baseStart_5937706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937719 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_5937719 : Nat := 118140960795 + 5937719 * 2 ^ 59
def prefixEnd_5937719 : Nat := 4983230072969 + 3 ^ 40 * 5937719 * 2
def baseEnd_5937719 : Nat := 3048903838333959380805433

theorem tailTrace_5937719 : CollatzResearch.WordTrace tailWord_5937719 prefixEnd_5937719 3048903838333959380805433 := by
  unfold tailWord_5937719
  simp only [CollatzResearch.WordTrace]
  refine ⟨216566403575665619515144211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144377602383777079676762807 216566403575665619515144211)
  ·
    refine ⟨324849605363498429272716317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216566403575665619515144211 324849605363498429272716317)
    ·
      refine ⟨121818602011311910977268619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324849605363498429272716317 121818602011311910977268619)
      ·
        refine ⟨182727903016967866465902929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121818602011311910977268619 182727903016967866465902929)
        ·
          refine ⟨137045927262725899849427197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182727903016967866465902929 137045927262725899849427197)
          ·
            refine ⟨51392222723522212443535199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137045927262725899849427197 51392222723522212443535199)
            ·
              refine ⟨77088334085283318665302799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51392222723522212443535199 77088334085283318665302799)
              ·
                refine ⟨115632501127924977997954199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77088334085283318665302799 115632501127924977997954199)
                ·
                  refine ⟨173448751691887466996931299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115632501127924977997954199 173448751691887466996931299)
                  ·
                    refine ⟨260173127537831200495396949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173448751691887466996931299 260173127537831200495396949)
                    ·
                      refine ⟨3048903838333959380805433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260173127537831200495396949 3048903838333959380805433)
                      ·
                        rfl

theorem cell23_5937719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_5937719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937719 prefixEnd_5937719 := by exact prefixLift 5937719
  have htrace : WordTrace (prefixWord ++ tailWord_5937719) baseStart_5937719 baseEnd_5937719 := by
    simpa [prefixWord, tailWord_5937719, baseEnd_5937719] using wordTrace_append hprefix tailTrace_5937719
  have hstable : (prefixWord ++ tailWord_5937719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937719).length < 2 ^ (prefixWord ++ tailWord_5937719).sum := by decide
  have hdescent : baseEnd_5937719 < baseStart_5937719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937733 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 6]
def baseStart_5937733 : Nat := 118140960795 + 5937733 * 2 ^ 59
def prefixEnd_5937733 : Nat := 4983230072969 + 3 ^ 40 * 5937733 * 2
def baseEnd_5937733 : Nat := 338767891895902480670041

theorem tailTrace_5937733 : CollatzResearch.WordTrace tailWord_5937733 prefixEnd_5937733 338767891895902480670041 := by
  unfold tailWord_5937733
  simp only [CollatzResearch.WordTrace]
  refine ⟨216566914197614899906153853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144377942798409933270769235 216566914197614899906153853)
  ·
    refine ⟨81212592824105587464807695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216566914197614899906153853 81212592824105587464807695)
    ·
      refine ⟨121818889236158381197211543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81212592824105587464807695 121818889236158381197211543)
      ·
        refine ⟨182728333854237571795817315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121818889236158381197211543 182728333854237571795817315)
        ·
          refine ⟨274092500781356357693725973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182728333854237571795817315 274092500781356357693725973)
          ·
            refine ⟨12848085974126079266893405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 274092500781356357693725973 12848085974126079266893405)
            ·
              refine ⟨4818032240297279725085027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12848085974126079266893405 4818032240297279725085027)
              ·
                refine ⟨7227048360445919587627541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818032240297279725085027 7227048360445919587627541)
                ·
                  refine ⟨338767891895902480670041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7227048360445919587627541 338767891895902480670041)
                  ·
                    rfl

theorem cell23_5937733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_5937733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937733 prefixEnd_5937733 := by exact prefixLift 5937733
  have htrace : WordTrace (prefixWord ++ tailWord_5937733) baseStart_5937733 baseEnd_5937733 := by
    simpa [prefixWord, tailWord_5937733, baseEnd_5937733] using wordTrace_append hprefix tailTrace_5937733
  have hstable : (prefixWord ++ tailWord_5937733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937733).length < 2 ^ (prefixWord ++ tailWord_5937733).sum := by decide
  have hdescent : baseEnd_5937733 < baseStart_5937733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937739 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_5937739 : Nat := 118140960795 + 5937739 * 2 ^ 59
def prefixEnd_5937739 : Nat := 4983230072969 + 3 ^ 40 * 5937739 * 2
def baseEnd_5937739 : Nat := 3048914107947049302555341

theorem tailTrace_5937739 : CollatzResearch.WordTrace tailWord_5937739 prefixEnd_5937739 3048914107947049302555341 := by
  unfold tailWord_5937739
  simp only [CollatzResearch.WordTrace]
  refine ⟨216567133035593162930872271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144378088690395441953914847 216567133035593162930872271)
  ·
    refine ⟨324850699553389744396308407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216567133035593162930872271 324850699553389744396308407)
    ·
      refine ⟨487276049330084616594462611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324850699553389744396308407 487276049330084616594462611)
      ·
        refine ⟨730914073995126924891693917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487276049330084616594462611 730914073995126924891693917)
        ·
          refine ⟨274092777748172596834385219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730914073995126924891693917 274092777748172596834385219)
          ·
            refine ⟨411139166622258895251577829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274092777748172596834385219 411139166622258895251577829)
            ·
              refine ⟨77088593741673542859670843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411139166622258895251577829 77088593741673542859670843)
              ·
                refine ⟨115632890612510314289506265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77088593741673542859670843 115632890612510314289506265)
                ·
                  refine ⟨86724667959382735717129699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115632890612510314289506265 86724667959382735717129699)
                  ·
                    refine ⟨130087001939074103575694549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86724667959382735717129699 130087001939074103575694549)
                    ·
                      refine ⟨3048914107947049302555341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130087001939074103575694549 3048914107947049302555341)
                      ·
                        rfl

theorem cell23_5937739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_5937739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937739 prefixEnd_5937739 := by exact prefixLift 5937739
  have htrace : WordTrace (prefixWord ++ tailWord_5937739) baseStart_5937739 baseEnd_5937739 := by
    simpa [prefixWord, tailWord_5937739, baseEnd_5937739] using wordTrace_append hprefix tailTrace_5937739
  have hstable : (prefixWord ++ tailWord_5937739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937739).length < 2 ^ (prefixWord ++ tailWord_5937739).sum := by decide
  have hdescent : baseEnd_5937739 < baseStart_5937739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937743 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 3]
def baseStart_5937743 : Nat := 118140960795 + 5937743 * 2 ^ 59
def prefixEnd_5937743 : Nat := 4983230072969 + 3 ^ 40 * 5937743 * 2
def baseEnd_5937743 : Nat := 3048916161869667286905323

theorem tailTrace_5937743 : CollatzResearch.WordTrace tailWord_5937743 prefixEnd_5937743 3048916161869667286905323 := by
  unfold tailWord_5937743
  simp only [CollatzResearch.WordTrace]
  refine ⟨216567278927578671614017883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144378185951719114409345255 216567278927578671614017883)
  ·
    refine ⟨324850918391368007421026825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216567278927578671614017883 324850918391368007421026825)
    ·
      refine ⟨243638188793526005565770119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324850918391368007421026825 243638188793526005565770119)
      ·
        refine ⟨365457283190289008348655179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243638188793526005565770119 365457283190289008348655179)
        ·
          refine ⟨548185924785433512522982769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365457283190289008348655179 548185924785433512522982769)
          ·
            refine ⟨411139443589075134392237077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548185924785433512522982769 411139443589075134392237077)
            ·
              refine ⟨19272161418237896924636113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 411139443589075134392237077 19272161418237896924636113)
              ·
                refine ⟨14454121063678422693477085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19272161418237896924636113 14454121063678422693477085)
                ·
                  refine ⟨5420295398879408510053907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14454121063678422693477085 5420295398879408510053907)
                  ·
                    refine ⟨8130443098319112765080861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5420295398879408510053907 8130443098319112765080861)
                    ·
                      refine ⟨3048916161869667286905323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130443098319112765080861 3048916161869667286905323)
                      ·
                        rfl

theorem cell23_5937743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_5937743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937743 prefixEnd_5937743 := by exact prefixLift 5937743
  have htrace : WordTrace (prefixWord ++ tailWord_5937743) baseStart_5937743 baseEnd_5937743 := by
    simpa [prefixWord, tailWord_5937743, baseEnd_5937743] using wordTrace_append hprefix tailTrace_5937743
  have hstable : (prefixWord ++ tailWord_5937743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937743).length < 2 ^ (prefixWord ++ tailWord_5937743).sum := by decide
  have hdescent : baseEnd_5937743 < baseStart_5937743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937770 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5937770 : Nat := 118140960795 + 5937770 * 2 ^ 59
def prefixEnd_5937770 : Nat := 4983230072969 + 3 ^ 40 * 5937770 * 2
def baseEnd_5937770 : Nat := 3048930025847338681267699

theorem tailTrace_5937770 : CollatzResearch.WordTrace tailWord_5937770 prefixEnd_5937770 3048930025847338681267699 := by
  unfold tailWord_5937770
  simp only [CollatzResearch.WordTrace]
  refine ⟨54142065924620213806312691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144378842465653903483500509 54142065924620213806312691)
  ·
    refine ⟨81213098886930320709469037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54142065924620213806312691 81213098886930320709469037)
    ·
      refine ⟨30454912082598870266050889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81213098886930320709469037 30454912082598870266050889)
      ·
        refine ⟨22841184061949152699538167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30454912082598870266050889 22841184061949152699538167)
        ·
          refine ⟨34261776092923729049307251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22841184061949152699538167 34261776092923729049307251)
          ·
            refine ⟨51392664139385593573960877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34261776092923729049307251 51392664139385593573960877)
            ·
              refine ⟨19272249052269597590235329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51392664139385593573960877 19272249052269597590235329)
              ·
                refine ⟨14454186789202198192676497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19272249052269597590235329 14454186789202198192676497)
                ·
                  refine ⟨10840640091901648644507373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14454186789202198192676497 10840640091901648644507373)
                  ·
                    refine ⟨4065240034463118241690265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10840640091901648644507373 4065240034463118241690265)
                    ·
                      refine ⟨3048930025847338681267699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065240034463118241690265 3048930025847338681267699)
                      ·
                        rfl

theorem cell23_5937770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5937770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937770 prefixEnd_5937770 := by exact prefixLift 5937770
  have htrace : WordTrace (prefixWord ++ tailWord_5937770) baseStart_5937770 baseEnd_5937770 := by
    simpa [prefixWord, tailWord_5937770, baseEnd_5937770] using wordTrace_append hprefix tailTrace_5937770
  have hstable : (prefixWord ++ tailWord_5937770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937770).length < 2 ^ (prefixWord ++ tailWord_5937770).sum := by decide
  have hdescent : baseEnd_5937770 < baseStart_5937770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937803 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 3]
def baseStart_5937803 : Nat := 118140960795 + 5937803 * 2 ^ 59
def prefixEnd_5937803 : Nat := 4983230072969 + 3 ^ 40 * 5937803 * 2
def baseEnd_5937803 : Nat := 3048946970708937052155047

theorem tailTrace_5937803 : CollatzResearch.WordTrace tailWord_5937803 prefixEnd_5937803 3048946970708937052155047 := by
  unfold tailWord_5937803
  simp only [CollatzResearch.WordTrace]
  refine ⟨216569467307361301861202063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144379644871574201240801375 216569467307361301861202063)
  ·
    refine ⟨324854200961041952791803095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216569467307361301861202063 324854200961041952791803095)
    ·
      refine ⟨487281301441562929187704643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324854200961041952791803095 487281301441562929187704643)
      ·
        refine ⟨730921952162344393781556965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487281301441562929187704643 730921952162344393781556965)
        ·
          refine ⟨137047866030439573834041931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 730921952162344393781556965 137047866030439573834041931)
          ·
            refine ⟨205571799045659360751062897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137047866030439573834041931 205571799045659360751062897)
            ·
              refine ⟨154178849284244520563297173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205571799045659360751062897 154178849284244520563297173)
              ·
                refine ⟨7227133560198961901404555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154178849284244520563297173 7227133560198961901404555)
                ·
                  refine ⟨10840700340298442852106833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227133560198961901404555 10840700340298442852106833)
                  ·
                    refine ⟨8130525255223832139080125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10840700340298442852106833 8130525255223832139080125)
                    ·
                      refine ⟨3048946970708937052155047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130525255223832139080125 3048946970708937052155047)
                      ·
                        rfl

theorem cell23_5937803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 3].length) (baseStart_5937803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937803 prefixEnd_5937803 := by exact prefixLift 5937803
  have htrace : WordTrace (prefixWord ++ tailWord_5937803) baseStart_5937803 baseEnd_5937803 := by
    simpa [prefixWord, tailWord_5937803, baseEnd_5937803] using wordTrace_append hprefix tailTrace_5937803
  have hstable : (prefixWord ++ tailWord_5937803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937803).length < 2 ^ (prefixWord ++ tailWord_5937803).sum := by decide
  have hdescent : baseEnd_5937803 < baseStart_5937803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937806 : List Nat := [4, 1, 1, 3, 1, 1, 1, 11]
def baseStart_5937806 : Nat := 118140960795 + 5937806 * 2 ^ 59
def prefixEnd_5937806 : Nat := 4983230072969 + 3 ^ 40 * 5937806 * 2
def baseEnd_5937806 : Nat := 112924018931514834830279

theorem tailTrace_5937806 : CollatzResearch.WordTrace tailWord_5937806 prefixEnd_5937806 112924018931514834830279 := by
  unfold tailWord_5937806
  simp only [CollatzResearch.WordTrace]
  refine ⟨27071197090793804171695159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144379717817566955582374181 27071197090793804171695159)
  ·
    refine ⟨40606795636190706257542739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27071197090793804171695159 40606795636190706257542739)
    ·
      refine ⟨60910193454286059386314109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40606795636190706257542739 60910193454286059386314109)
      ·
        refine ⟨22841322545357272269867791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60910193454286059386314109 22841322545357272269867791)
        ·
          refine ⟨34261983818035908404801687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22841322545357272269867791 34261983818035908404801687)
          ·
            refine ⟨51392975727053862607202531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34261983818035908404801687 51392975727053862607202531)
            ·
              refine ⟨77089463590580793910803797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51392975727053862607202531 77089463590580793910803797)
              ·
                refine ⟨112924018931514834830279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77089463590580793910803797 112924018931514834830279)
                ·
                  rfl

theorem cell23_5937806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_5937806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937806 prefixEnd_5937806 := by exact prefixLift 5937806
  have htrace : WordTrace (prefixWord ++ tailWord_5937806) baseStart_5937806 baseEnd_5937806 := by
    simpa [prefixWord, tailWord_5937806, baseEnd_5937806] using wordTrace_append hprefix tailTrace_5937806
  have hstable : (prefixWord ++ tailWord_5937806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937806).length < 2 ^ (prefixWord ++ tailWord_5937806).sum := by decide
  have hdescent : baseEnd_5937806 < baseStart_5937806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937817 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 1, 2, 2]
def baseStart_5937817 : Nat := 118140960795 + 5937817 * 2 ^ 59
def prefixEnd_5937817 : Nat := 4983230072969 + 3 ^ 40 * 5937817 * 2
def baseEnd_5937817 : Nat := 3048954159438099997379983

theorem tailTrace_5937817 : CollatzResearch.WordTrace tailWord_5937817 prefixEnd_5937817 3048954159438099997379983 := by
  unfold tailWord_5937817
  simp only [CollatzResearch.WordTrace]
  refine ⟨216569977929310582252211705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144379985286207054834807803 216569977929310582252211705)
  ·
    refine ⟨162427483446982936689158779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216569977929310582252211705 162427483446982936689158779)
    ·
      refine ⟨243641225170474405033738169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162427483446982936689158779 243641225170474405033738169)
      ·
        refine ⟨182730918877855803775303627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243641225170474405033738169 182730918877855803775303627)
        ·
          refine ⟨274096378316783705662955441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182730918877855803775303627 274096378316783705662955441)
          ·
            refine ⟨205572283737587779247216581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274096378316783705662955441 205572283737587779247216581)
            ·
              refine ⟨38544803200797708608853109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205572283737587779247216581 38544803200797708608853109)
              ·
                refine ⟨3613575300074785182079979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38544803200797708608853109 3613575300074785182079979)
                ·
                  refine ⟨5420362950112177773119969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613575300074785182079979 5420362950112177773119969)
                  ·
                    refine ⟨4065272212584133329839977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5420362950112177773119969 4065272212584133329839977)
                    ·
                      refine ⟨3048954159438099997379983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065272212584133329839977 3048954159438099997379983)
                      ·
                        rfl

theorem cell23_5937817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_5937817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937817 prefixEnd_5937817 := by exact prefixLift 5937817
  have htrace : WordTrace (prefixWord ++ tailWord_5937817) baseStart_5937817 baseEnd_5937817 := by
    simpa [prefixWord, tailWord_5937817, baseEnd_5937817] using wordTrace_append hprefix tailTrace_5937817
  have hstable : (prefixWord ++ tailWord_5937817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937817).length < 2 ^ (prefixWord ++ tailWord_5937817).sum := by decide
  have hdescent : baseEnd_5937817 < baseStart_5937817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937820 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5937820 : Nat := 118140960795 + 5937820 * 2 ^ 59
def prefixEnd_5937820 : Nat := 4983230072969 + 3 ^ 40 * 5937820 * 2
def baseEnd_5937820 : Nat := 3048955699880063485642469

theorem tailTrace_5937820 : CollatzResearch.WordTrace tailWord_5937820 prefixEnd_5937820 3048955699880063485642469 := by
  unfold tailWord_5937820
  simp only [CollatzResearch.WordTrace]
  refine ⟨108285043674149856882285457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144380058232199809176380609 108285043674149856882285457)
  ·
    refine ⟨81213782755612392661714093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108285043674149856882285457 81213782755612392661714093)
    ·
      refine ⟨30455168533354647248142785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81213782755612392661714093 30455168533354647248142785)
      ·
        refine ⟨22841376400015985436107089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30455168533354647248142785 22841376400015985436107089)
        ·
          refine ⟨17131032300011989077080317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22841376400015985436107089 17131032300011989077080317)
          ·
            refine ⟨6424137112504495903905119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17131032300011989077080317 6424137112504495903905119)
            ·
              refine ⟨9636205668756743855857679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424137112504495903905119 9636205668756743855857679)
              ·
                refine ⟨14454308503135115783786519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9636205668756743855857679 14454308503135115783786519)
                ·
                  refine ⟨21681462754702673675679779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14454308503135115783786519 21681462754702673675679779)
                  ·
                    refine ⟨32522194132054010513519669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21681462754702673675679779 32522194132054010513519669)
                    ·
                      refine ⟨3048955699880063485642469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32522194132054010513519669 3048955699880063485642469)
                      ·
                        rfl

theorem cell23_5937820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5937820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937820 prefixEnd_5937820 := by exact prefixLift 5937820
  have htrace : WordTrace (prefixWord ++ tailWord_5937820) baseStart_5937820 baseEnd_5937820 := by
    simpa [prefixWord, tailWord_5937820, baseEnd_5937820] using wordTrace_append hprefix tailTrace_5937820
  have hstable : (prefixWord ++ tailWord_5937820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937820).length < 2 ^ (prefixWord ++ tailWord_5937820).sum := by decide
  have hdescent : baseEnd_5937820 < baseStart_5937820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937850 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_5937850 : Nat := 118140960795 + 5937850 * 2 ^ 59
def prefixEnd_5937850 : Nat := 4983230072969 + 3 ^ 40 * 5937850 * 2
def baseEnd_5937850 : Nat := 3048971104299698368267331

theorem tailTrace_5937850 : CollatzResearch.WordTrace tailWord_5937850 prefixEnd_5937850 3048971104299698368267331 := by
  unfold tailWord_5937850
  simp only [CollatzResearch.WordTrace]
  refine ⟨54142795384547757222040751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144380787692127352592108669 54142795384547757222040751)
  ·
    refine ⟨81214193076821635833061127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54142795384547757222040751 81214193076821635833061127)
    ·
      refine ⟨121821289615232453749591691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81214193076821635833061127 121821289615232453749591691)
      ·
        refine ⟨182731934422848680624387537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121821289615232453749591691 182731934422848680624387537)
        ·
          refine ⟨137048950817136510468290653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182731934422848680624387537 137048950817136510468290653)
          ·
            refine ⟨51393356556426191425608995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137048950817136510468290653 51393356556426191425608995)
            ·
              refine ⟨77090034834639287138413493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51393356556426191425608995 77090034834639287138413493)
              ·
                refine ⟨7227190765747433169226265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77090034834639287138413493 7227190765747433169226265)
                ·
                  refine ⟨5420393074310574876919699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7227190765747433169226265 5420393074310574876919699)
                  ·
                    refine ⟨8130589611465862315379549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5420393074310574876919699 8130589611465862315379549)
                    ·
                      refine ⟨3048971104299698368267331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130589611465862315379549 3048971104299698368267331)
                      ·
                        rfl

theorem cell23_5937850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_5937850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937850 prefixEnd_5937850 := by exact prefixLift 5937850
  have htrace : WordTrace (prefixWord ++ tailWord_5937850) baseStart_5937850 baseEnd_5937850 := by
    simpa [prefixWord, tailWord_5937850, baseEnd_5937850] using wordTrace_append hprefix tailTrace_5937850
  have hstable : (prefixWord ++ tailWord_5937850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937850).length < 2 ^ (prefixWord ++ tailWord_5937850).sum := by decide
  have hdescent : baseEnd_5937850 < baseStart_5937850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937857 : List Nat := [1, 2, 6, 2, 1, 1, 3, 7]
def baseStart_5937857 : Nat := 118140960795 + 5937857 * 2 ^ 59
def prefixEnd_5937857 : Nat := 4983230072969 + 3 ^ 40 * 5937857 * 2
def baseEnd_5937857 : Nat := 112924988839417771884437

theorem tailTrace_5937857 : CollatzResearch.WordTrace tailWord_5937857 prefixEnd_5937857 112924988839417771884437 := by
  unfold tailWord_5937857
  simp only [CollatzResearch.WordTrace]
  refine ⟨216571436849165669083667825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144380957899443779389111883 216571436849165669083667825)
  ·
    refine ⟨162428577636874251812750869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216571436849165669083667825 162428577636874251812750869)
    ·
      refine ⟨7613839576728480553722697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 162428577636874251812750869 7613839576728480553722697)
      ·
        refine ⟨5710379682546360415292023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7613839576728480553722697 5710379682546360415292023)
        ·
          refine ⟨8565569523819540622938035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710379682546360415292023 8565569523819540622938035)
          ·
            refine ⟨12848354285729310934407053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565569523819540622938035 12848354285729310934407053)
            ·
              refine ⟨4818132857148491600402645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12848354285729310934407053 4818132857148491600402645)
              ·
                refine ⟨112924988839417771884437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4818132857148491600402645 112924988839417771884437)
                ·
                  rfl

theorem cell23_5937857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 7].length) (baseStart_5937857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937857 prefixEnd_5937857 := by exact prefixLift 5937857
  have htrace : WordTrace (prefixWord ++ tailWord_5937857) baseStart_5937857 baseEnd_5937857 := by
    simpa [prefixWord, tailWord_5937857, baseEnd_5937857] using wordTrace_append hprefix tailTrace_5937857
  have hstable : (prefixWord ++ tailWord_5937857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937857).length < 2 ^ (prefixWord ++ tailWord_5937857).sum := by decide
  have hdescent : baseEnd_5937857 < baseStart_5937857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937884 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5937884 : Nat := 118140960795 + 5937884 * 2 ^ 59
def prefixEnd_5937884 : Nat := 4983230072969 + 3 ^ 40 * 5937884 * 2
def baseEnd_5937884 : Nat := 3048988562641951235242175

theorem tailTrace_5937884 : CollatzResearch.WordTrace tailWord_5937884 prefixEnd_5937884 3048988562641951235242175 := by
  unfold tailWord_5937884
  simp only [CollatzResearch.WordTrace]
  refine ⟨108286210810033926347450353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144381614413378568463267137 108286210810033926347450353)
  ·
    refine ⟨81214658107525444760587765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108286210810033926347450353 81214658107525444760587765)
    ·
      refine ⟨7613874197580510446305103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81214658107525444760587765 7613874197580510446305103)
      ·
        refine ⟨11420811296370765669457655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613874197580510446305103 11420811296370765669457655)
        ·
          refine ⟨17131216944556148504186483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11420811296370765669457655 17131216944556148504186483)
          ·
            refine ⟨25696825416834222756279725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17131216944556148504186483 25696825416834222756279725)
            ·
              refine ⟨9636309531312833533604897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25696825416834222756279725 9636309531312833533604897)
              ·
                refine ⟨7227232148484625150203673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9636309531312833533604897 7227232148484625150203673)
                ·
                  refine ⟨5420424111363468862652755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7227232148484625150203673 5420424111363468862652755)
                  ·
                    refine ⟨8130636167045203293979133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5420424111363468862652755 8130636167045203293979133)
                    ·
                      refine ⟨3048988562641951235242175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130636167045203293979133 3048988562641951235242175)
                      ·
                        rfl

theorem cell23_5937884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5937884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937884 prefixEnd_5937884 := by exact prefixLift 5937884
  have htrace : WordTrace (prefixWord ++ tailWord_5937884) baseStart_5937884 baseEnd_5937884 := by
    simpa [prefixWord, tailWord_5937884, baseEnd_5937884] using wordTrace_append hprefix tailTrace_5937884
  have hstable : (prefixWord ++ tailWord_5937884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937884).length < 2 ^ (prefixWord ++ tailWord_5937884).sum := by decide
  have hdescent : baseEnd_5937884 < baseStart_5937884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937903 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_5937903 : Nat := 118140960795 + 5937903 * 2 ^ 59
def prefixEnd_5937903 : Nat := 4983230072969 + 3 ^ 40 * 5937903 * 2
def baseEnd_5937903 : Nat := 3048998318774386660904587

theorem tailTrace_5937903 : CollatzResearch.WordTrace tailWord_5937903 prefixEnd_5937903 3048998318774386660904587 := by
  unfold tailWord_5937903
  simp only [CollatzResearch.WordTrace]
  refine ⟨216573114606999018939842363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144382076404666012626561575 216573114606999018939842363)
  ·
    refine ⟨324859671910498528409763545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216573114606999018939842363 324859671910498528409763545)
    ·
      refine ⟨243644753932873896307322659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324859671910498528409763545 243644753932873896307322659)
      ·
        refine ⟨365467130899310844460983989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243644753932873896307322659 365467130899310844460983989)
        ·
          refine ⟨34262543521810391668217249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365467130899310844460983989 34262543521810391668217249)
          ·
            refine ⟨25696907641357793751162937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34262543521810391668217249 25696907641357793751162937)
            ·
              refine ⟨19272680731018345313372203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25696907641357793751162937 19272680731018345313372203)
              ·
                refine ⟨28909021096527517970058305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19272680731018345313372203 28909021096527517970058305)
                ·
                  refine ⟨21681765822395638477543729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28909021096527517970058305 21681765822395638477543729)
                  ·
                    refine ⟨16261324366796728858157797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21681765822395638477543729 16261324366796728858157797)
                    ·
                      refine ⟨3048998318774386660904587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16261324366796728858157797 3048998318774386660904587)
                      ·
                        rfl

theorem cell23_5937903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_5937903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937903 prefixEnd_5937903 := by exact prefixLift 5937903
  have htrace : WordTrace (prefixWord ++ tailWord_5937903) baseStart_5937903 baseEnd_5937903 := by
    simpa [prefixWord, tailWord_5937903, baseEnd_5937903] using wordTrace_append hprefix tailTrace_5937903
  have hstable : (prefixWord ++ tailWord_5937903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937903).length < 2 ^ (prefixWord ++ tailWord_5937903).sum := by decide
  have hdescent : baseEnd_5937903 < baseStart_5937903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937953 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5937953 : Nat := 118140960795 + 5937953 * 2 ^ 59
def prefixEnd_5937953 : Nat := 4983230072969 + 3 ^ 40 * 5937953 * 2
def baseEnd_5937953 : Nat := 3049023992807111465279357

theorem tailTrace_5937953 : CollatzResearch.WordTrace tailWord_5937953 prefixEnd_5937953 3049023992807111465279357 := by
  unfold tailWord_5937953
  simp only [CollatzResearch.WordTrace]
  refine ⟨216574938256817877479162513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144383292171211918319441675 216574938256817877479162513)
  ·
    refine ⟨162431203692613408109371885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216574938256817877479162513 162431203692613408109371885)
    ·
      refine ⟨60911701384730028041014457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162431203692613408109371885 60911701384730028041014457)
      ·
        refine ⟨45683776038547521030760843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60911701384730028041014457 45683776038547521030760843)
        ·
          refine ⟨68525664057821281546141265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45683776038547521030760843 68525664057821281546141265)
          ·
            refine ⟨51394248043365961159605949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68525664057821281546141265 51394248043365961159605949)
            ·
              refine ⟨19272843016262235434852231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51394248043365961159605949 19272843016262235434852231)
              ·
                refine ⟨28909264524393353152278347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19272843016262235434852231 28909264524393353152278347)
                ·
                  refine ⟨43363896786590029728417521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28909264524393353152278347 43363896786590029728417521)
                  ·
                    refine ⟨32522922589942522296313141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43363896786590029728417521 32522922589942522296313141)
                    ·
                      refine ⟨3049023992807111465279357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32522922589942522296313141 3049023992807111465279357)
                      ·
                        rfl

theorem cell23_5937953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5937953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937953 prefixEnd_5937953 := by exact prefixLift 5937953
  have htrace : WordTrace (prefixWord ++ tailWord_5937953) baseStart_5937953 baseEnd_5937953 := by
    simpa [prefixWord, tailWord_5937953, baseEnd_5937953] using wordTrace_append hprefix tailTrace_5937953
  have hstable : (prefixWord ++ tailWord_5937953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937953).length < 2 ^ (prefixWord ++ tailWord_5937953).sum := by decide
  have hdescent : baseEnd_5937953 < baseStart_5937953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5937980 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_5937980 : Nat := 118140960795 + 5937980 * 2 ^ 59
def prefixEnd_5937980 : Nat := 4983230072969 + 3 ^ 40 * 5937980 * 2
def baseEnd_5937980 : Nat := 3049037856784782859641733

theorem tailTrace_5937980 : CollatzResearch.WordTrace tailWord_5937980 prefixEnd_5937980 3049037856784782859641733 := by
  unfold tailWord_5937980
  simp only [CollatzResearch.WordTrace]
  refine ⟨108287961513860030545197697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144383948685146707393596929 108287961513860030545197697)
  ·
    refine ⟨81215971135395022908898273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108287961513860030545197697 81215971135395022908898273)
    ·
      refine ⟨60911978351546267181673705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81215971135395022908898273 60911978351546267181673705)
      ·
        refine ⟨45683983763659700386255279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60911978351546267181673705 45683983763659700386255279)
        ·
          refine ⟨68525975645489550579382919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45683983763659700386255279 68525975645489550579382919)
          ·
            refine ⟨102788963468234325869074379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68525975645489550579382919 102788963468234325869074379)
            ·
              refine ⟨154183445202351488803611569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102788963468234325869074379 154183445202351488803611569)
              ·
                refine ⟨115637583901763616602708677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154183445202351488803611569 115637583901763616602708677)
                ·
                  refine ⟨21682046981580678113007877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115637583901763616602708677 21682046981580678113007877)
                  ·
                    refine ⟨4065383809046377146188977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21682046981580678113007877 4065383809046377146188977)
                    ·
                      refine ⟨3049037856784782859641733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065383809046377146188977 3049037856784782859641733)
                      ·
                        rfl

theorem cell23_5937980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_5937980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5937980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5937980 prefixEnd_5937980 := by exact prefixLift 5937980
  have htrace : WordTrace (prefixWord ++ tailWord_5937980) baseStart_5937980 baseEnd_5937980 := by
    simpa [prefixWord, tailWord_5937980, baseEnd_5937980] using wordTrace_append hprefix tailTrace_5937980
  have hstable : (prefixWord ++ tailWord_5937980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5937980).length < 2 ^ (prefixWord ++ tailWord_5937980).sum := by decide
  have hdescent : baseEnd_5937980 < baseStart_5937980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5937980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938000 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_5938000 : Nat := 118140960795 + 5938000 * 2 ^ 59
def prefixEnd_5938000 : Nat := 4983230072969 + 3 ^ 40 * 5938000 * 2
def baseEnd_5938000 : Nat := 3049048126397872781391641

theorem tailTrace_5938000 : CollatzResearch.WordTrace tailWord_5938000 prefixEnd_5938000 3049048126397872781391641 := by
  unfold tailWord_5938000
  simp only [CollatzResearch.WordTrace]
  refine ⟨108288326243823802253061727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144384434991765069670748969 108288326243823802253061727)
  ·
    refine ⟨162432489365735703379592591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108288326243823802253061727 162432489365735703379592591)
    ·
      refine ⟨243648734048603555069388887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162432489365735703379592591 243648734048603555069388887)
      ·
        refine ⟨365473101072905332604083331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243648734048603555069388887 365473101072905332604083331)
        ·
          refine ⟨548209651609357998906124997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365473101072905332604083331 548209651609357998906124997)
          ·
            refine ⟨102789309676754624794898437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 548209651609357998906124997 102789309676754624794898437)
            ·
              refine ⟨19272995564391492149043457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102789309676754624794898437 19272995564391492149043457)
              ·
                refine ⟨14454746673293619111782593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19272995564391492149043457 14454746673293619111782593)
                ·
                  refine ⟨10841060004970214333836945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14454746673293619111782593 10841060004970214333836945)
                  ·
                    refine ⟨8130795003727660750377709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10841060004970214333836945 8130795003727660750377709)
                    ·
                      refine ⟨3049048126397872781391641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130795003727660750377709 3049048126397872781391641)
                      ·
                        rfl

theorem cell23_5938000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_5938000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938000 prefixEnd_5938000 := by exact prefixLift 5938000
  have htrace : WordTrace (prefixWord ++ tailWord_5938000) baseStart_5938000 baseEnd_5938000 := by
    simpa [prefixWord, tailWord_5938000, baseEnd_5938000] using wordTrace_append hprefix tailTrace_5938000
  have hstable : (prefixWord ++ tailWord_5938000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938000).length < 2 ^ (prefixWord ++ tailWord_5938000).sum := by decide
  have hdescent : baseEnd_5938000 < baseStart_5938000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938020 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 6]
def baseStart_5938020 : Nat := 118140960795 + 5938020 * 2 ^ 59
def prefixEnd_5938020 : Nat := 4983230072969 + 3 ^ 40 * 5938020 * 2
def baseEnd_5938020 : Nat := 338784266223440300349061

theorem tailTrace_5938020 : CollatzResearch.WordTrace tailWord_5938020 prefixEnd_5938020 338784266223440300349061 := by
  unfold tailWord_5938020
  simp only [CollatzResearch.WordTrace]
  refine ⟨108288690973787573960925757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144384921298383431947901009 108288690973787573960925757)
  ·
    refine ⟨40608259115170340235347159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108288690973787573960925757 40608259115170340235347159)
    ·
      refine ⟨60912388672755510353020739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40608259115170340235347159 60912388672755510353020739)
      ·
        refine ⟨91368583009133265529531109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60912388672755510353020739 91368583009133265529531109)
        ·
          refine ⟨17131609314212487286787083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91368583009133265529531109 17131609314212487286787083)
          ·
            refine ⟨25697413971318730930180625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17131609314212487286787083 25697413971318730930180625)
            ·
              refine ⟨19273060478489048197635469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25697413971318730930180625 19273060478489048197635469)
              ·
                refine ⟨7227397679433393074113301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19273060478489048197635469 7227397679433393074113301)
                ·
                  refine ⟨338784266223440300349061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7227397679433393074113301 338784266223440300349061)
                  ·
                    rfl

theorem cell23_5938020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_5938020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938020 prefixEnd_5938020 := by exact prefixLift 5938020
  have htrace : WordTrace (prefixWord ++ tailWord_5938020) baseStart_5938020 baseEnd_5938020 := by
    simpa [prefixWord, tailWord_5938020, baseEnd_5938020] using wordTrace_append hprefix tailTrace_5938020
  have hstable : (prefixWord ++ tailWord_5938020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938020).length < 2 ^ (prefixWord ++ tailWord_5938020).sum := by decide
  have hdescent : baseEnd_5938020 < baseStart_5938020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938080 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_5938080 : Nat := 118140960795 + 5938080 * 2 ^ 59
def prefixEnd_5938080 : Nat := 4983230072969 + 3 ^ 40 * 5938080 * 2
def baseEnd_5938080 : Nat := 1016363068283410822797091

theorem tailTrace_5938080 : CollatzResearch.WordTrace tailWord_5938080 prefixEnd_5938080 1016363068283410822797091 := by
  unfold tailWord_5938080
  simp only [CollatzResearch.WordTrace]
  refine ⟨108289785163678889084517847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144386380218238518779357129 108289785163678889084517847)
  ·
    refine ⟨162434677745518333626776771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108289785163678889084517847 162434677745518333626776771)
    ·
      refine ⟨243652016618277500440165157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162434677745518333626776771 243652016618277500440165157)
      ·
        refine ⟨45684753115927031332530967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243652016618277500440165157 45684753115927031332530967)
        ·
          refine ⟨68527129673890546998796451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45684753115927031332530967 68527129673890546998796451)
          ·
            refine ⟨102790694510835820498194677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68527129673890546998796451 102790694510835820498194677)
            ·
              refine ⟨9636627610390858171705751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102790694510835820498194677 9636627610390858171705751)
              ·
                refine ⟨14454941415586287257558627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9636627610390858171705751 14454941415586287257558627)
                ·
                  refine ⟨21682412123379430886337941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14454941415586287257558627 21682412123379430886337941)
                  ·
                    refine ⟨1016363068283410822797091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21682412123379430886337941 1016363068283410822797091)
                    ·
                      rfl

theorem cell23_5938080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_5938080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938080 prefixEnd_5938080 := by exact prefixLift 5938080
  have htrace : WordTrace (prefixWord ++ tailWord_5938080) baseStart_5938080 baseEnd_5938080 := by
    simpa [prefixWord, tailWord_5938080, baseEnd_5938080] using wordTrace_append hprefix tailTrace_5938080
  have hstable : (prefixWord ++ tailWord_5938080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938080).length < 2 ^ (prefixWord ++ tailWord_5938080).sum := by decide
  have hdescent : baseEnd_5938080 < baseStart_5938080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938141 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5938141 : Nat := 118140960795 + 5938141 * 2 ^ 59
def prefixEnd_5938141 : Nat := 4983230072969 + 3 ^ 40 * 5938141 * 2
def baseEnd_5938141 : Nat := 3049120527170156729728493

theorem tailTrace_5938141 : CollatzResearch.WordTrace tailWord_5938141 prefixEnd_5938141 3049120527170156729728493 := by
  unfold tailWord_5938141
  simp only [CollatzResearch.WordTrace]
  refine ⟨216581795180136785587006277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144387863453424523724670851 216581795180136785587006277)
  ·
    refine ⟨40609086596275647297563677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216581795180136785587006277 40609086596275647297563677)
    ·
      refine ⟨15228407473603367736586379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40609086596275647297563677 15228407473603367736586379)
      ·
        refine ⟨22842611210405051604879569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15228407473603367736586379 22842611210405051604879569)
        ·
          refine ⟨17131958407803788703659677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22842611210405051604879569 17131958407803788703659677)
          ·
            refine ⟨6424484402926420763872379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17131958407803788703659677 6424484402926420763872379)
            ·
              refine ⟨9636726604389631145808569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424484402926420763872379 9636726604389631145808569)
              ·
                refine ⟨7227544953292223359356427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9636726604389631145808569 7227544953292223359356427)
                ·
                  refine ⟨10841317429938335039034641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227544953292223359356427 10841317429938335039034641)
                  ·
                    refine ⟨8130988072453751279275981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10841317429938335039034641 8130988072453751279275981)
                    ·
                      refine ⟨3049120527170156729728493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8130988072453751279275981 3049120527170156729728493)
                      ·
                        rfl

theorem cell23_5938141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5938141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938141 prefixEnd_5938141 := by exact prefixLift 5938141
  have htrace : WordTrace (prefixWord ++ tailWord_5938141) baseStart_5938141 baseEnd_5938141 := by
    simpa [prefixWord, tailWord_5938141, baseEnd_5938141] using wordTrace_append hprefix tailTrace_5938141
  have hstable : (prefixWord ++ tailWord_5938141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938141).length < 2 ^ (prefixWord ++ tailWord_5938141).sum := by decide
  have hdescent : baseEnd_5938141 < baseStart_5938141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938200 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 9]
def baseStart_5938200 : Nat := 118140960795 + 5938200 * 2 ^ 59
def prefixEnd_5938200 : Nat := 4983230072969 + 3 ^ 40 * 5938200 * 2
def baseEnd_5938200 : Nat := 338794535836530222098969

theorem tailTrace_5938200 : CollatzResearch.WordTrace tailWord_5938200 prefixEnd_5938200 338794535836530222098969 := by
  unfold tailWord_5938200
  simp only [CollatzResearch.WordTrace]
  refine ⟨108291973543461519331702027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144389298057948692442269369 108291973543461519331702027)
  ·
    refine ⟨162437960315192278997553041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108291973543461519331702027 162437960315192278997553041)
    ·
      refine ⟨121828470236394209248164781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162437960315192278997553041 121828470236394209248164781)
      ·
        refine ⟨45685676338647828468061793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121828470236394209248164781 45685676338647828468061793)
        ·
          refine ⟨34264257253985871351046345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45685676338647828468061793 34264257253985871351046345)
          ·
            refine ⟨25698192940489403513284759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34264257253985871351046345 25698192940489403513284759)
            ·
              refine ⟨38547289410734105269927139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25698192940489403513284759 38547289410734105269927139)
              ·
                refine ⟨57820934116101157904890709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38547289410734105269927139 57820934116101157904890709)
                ·
                  refine ⟨338794535836530222098969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57820934116101157904890709 338794535836530222098969)
                  ·
                    rfl

theorem cell23_5938200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_5938200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938200 prefixEnd_5938200 := by exact prefixLift 5938200
  have htrace : WordTrace (prefixWord ++ tailWord_5938200) baseStart_5938200 baseEnd_5938200 := by
    simpa [prefixWord, tailWord_5938200, baseEnd_5938200] using wordTrace_append hprefix tailTrace_5938200
  have hstable : (prefixWord ++ tailWord_5938200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938200).length < 2 ^ (prefixWord ++ tailWord_5938200).sum := by decide
  have hdescent : baseEnd_5938200 < baseStart_5938200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938215 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5938215 : Nat := 118140960795 + 5938215 * 2 ^ 59
def prefixEnd_5938215 : Nat := 4983230072969 + 3 ^ 40 * 5938215 * 2
def baseEnd_5938215 : Nat := 3049158524738589440203153

theorem tailTrace_5938215 : CollatzResearch.WordTrace tailWord_5938215 prefixEnd_5938215 3049158524738589440203153 := by
  unfold tailWord_5938215
  simp only [CollatzResearch.WordTrace]
  refine ⟨216584494181868696225200099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144389662787912464150133399 216584494181868696225200099)
  ·
    refine ⟨324876741272803044337800149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216584494181868696225200099 324876741272803044337800149)
    ·
      refine ⟨7614298623581321351667191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 324876741272803044337800149 7614298623581321351667191)
      ·
        refine ⟨11421447935371982027500787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7614298623581321351667191 11421447935371982027500787)
        ·
          refine ⟨17132171903057973041251181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11421447935371982027500787 17132171903057973041251181)
          ·
            refine ⟨6424564463646739890469193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17132171903057973041251181 6424564463646739890469193)
            ·
              refine ⟨4818423347735054917851895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424564463646739890469193 4818423347735054917851895)
              ·
                refine ⟨7227635021602582376777843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818423347735054917851895 7227635021602582376777843)
                ·
                  refine ⟨10841452532403873565166765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227635021602582376777843 10841452532403873565166765)
                  ·
                    refine ⟨4065544699651452586937537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10841452532403873565166765 4065544699651452586937537)
                    ·
                      refine ⟨3049158524738589440203153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065544699651452586937537 3049158524738589440203153)
                      ·
                        rfl

theorem cell23_5938215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5938215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938215 prefixEnd_5938215 := by exact prefixLift 5938215
  have htrace : WordTrace (prefixWord ++ tailWord_5938215) baseStart_5938215 baseEnd_5938215 := by
    simpa [prefixWord, tailWord_5938215, baseEnd_5938215] using wordTrace_append hprefix tailTrace_5938215
  have hstable : (prefixWord ++ tailWord_5938215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938215).length < 2 ^ (prefixWord ++ tailWord_5938215).sum := by decide
  have hdescent : baseEnd_5938215 < baseStart_5938215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938228 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5938228 : Nat := 118140960795 + 5938228 * 2 ^ 59
def prefixEnd_5938228 : Nat := 4983230072969 + 3 ^ 40 * 5938228 * 2
def baseEnd_5938228 : Nat := 3049165199987097889340593

theorem tailTrace_5938228 : CollatzResearch.WordTrace tailWord_5938228 prefixEnd_5938228 3049165199987097889340593 := by
  unfold tailWord_5938228
  simp only [CollatzResearch.WordTrace]
  refine ⟨108292484165410799722711669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144389978887214399630282225 108292484165410799722711669)
  ·
    refine ⟨10152420390507262474004219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108292484165410799722711669 10152420390507262474004219)
    ·
      refine ⟨15228630585760893711006329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10152420390507262474004219 15228630585760893711006329)
      ·
        refine ⟨11421472939320670283254747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15228630585760893711006329 11421472939320670283254747)
        ·
          refine ⟨17132209408981005424882121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11421472939320670283254747 17132209408981005424882121)
          ·
            refine ⟨12849157056735754068661591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17132209408981005424882121 12849157056735754068661591)
            ·
              refine ⟨19273735585103631102992387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12849157056735754068661591 19273735585103631102992387)
              ·
                refine ⟨28910603377655446654488581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19273735585103631102992387 28910603377655446654488581)
                ·
                  refine ⟨5420738133310396247716609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28910603377655446654488581 5420738133310396247716609)
                  ·
                    refine ⟨4065553599982797185787457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5420738133310396247716609 4065553599982797185787457)
                    ·
                      refine ⟨3049165199987097889340593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065553599982797185787457 3049165199987097889340593)
                      ·
                        rfl

theorem cell23_5938228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5938228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938228 prefixEnd_5938228 := by exact prefixLift 5938228
  have htrace : WordTrace (prefixWord ++ tailWord_5938228) baseStart_5938228 baseEnd_5938228 := by
    simpa [prefixWord, tailWord_5938228, baseEnd_5938228] using wordTrace_append hprefix tailTrace_5938228
  have hstable : (prefixWord ++ tailWord_5938228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938228).length < 2 ^ (prefixWord ++ tailWord_5938228).sum := by decide
  have hdescent : baseEnd_5938228 < baseStart_5938228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938240 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_5938240 : Nat := 118140960795 + 5938240 * 2 ^ 59
def prefixEnd_5938240 : Nat := 4983230072969 + 3 ^ 40 * 5938240 * 2
def baseEnd_5938240 : Nat := 3049171361754951842390537

theorem tailTrace_5938240 : CollatzResearch.WordTrace tailWord_5938240 prefixEnd_5938240 3049171361754951842390537 := by
  unfold tailWord_5938240
  simp only [CollatzResearch.WordTrace]
  refine ⟨108292703003389062747430087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144390270671185416996573449 108292703003389062747430087)
  ·
    refine ⟨162439054505083594121145131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108292703003389062747430087 162439054505083594121145131)
    ·
      refine ⟨243658581757625391181717697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162439054505083594121145131 243658581757625391181717697)
      ·
        refine ⟨182743936318219043386288273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243658581757625391181717697 182743936318219043386288273)
        ·
          refine ⟨137057952238664282539716205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182743936318219043386288273 137057952238664282539716205)
          ·
            refine ⟨51396732089499105952393577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137057952238664282539716205 51396732089499105952393577)
            ·
              refine ⟨38547549067124329464295183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51396732089499105952393577 38547549067124329464295183)
              ·
                refine ⟨57821323600686494196442775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38547549067124329464295183 57821323600686494196442775)
                ·
                  refine ⟨86731985401029741294664163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57821323600686494196442775 86731985401029741294664163)
                  ·
                    refine ⟨130097978101544611941996245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86731985401029741294664163 130097978101544611941996245)
                    ·
                      refine ⟨3049171361754951842390537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130097978101544611941996245 3049171361754951842390537)
                      ·
                        rfl

theorem cell23_5938240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_5938240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938240 prefixEnd_5938240 := by exact prefixLift 5938240
  have htrace : WordTrace (prefixWord ++ tailWord_5938240) baseStart_5938240 baseEnd_5938240 := by
    simpa [prefixWord, tailWord_5938240, baseEnd_5938240] using wordTrace_append hprefix tailTrace_5938240
  have hstable : (prefixWord ++ tailWord_5938240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938240).length < 2 ^ (prefixWord ++ tailWord_5938240).sum := by decide
  have hdescent : baseEnd_5938240 < baseStart_5938240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938307 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 6]
def baseStart_5938307 : Nat := 118140960795 + 5938307 * 2 ^ 59
def prefixEnd_5938307 : Nat := 4983230072969 + 3 ^ 40 * 5938307 * 2
def baseEnd_5938307 : Nat := 338800640550978120028081

theorem tailTrace_5938307 : CollatzResearch.WordTrace tailWord_5938307 prefixEnd_5938307 338800640550978120028081 := by
  unfold tailWord_5938307
  simp only [CollatzResearch.WordTrace]
  refine ⟨216587849697535395937549175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144391899798356930625032783 216587849697535395937549175)
  ·
    refine ⟨324881774546303093906323763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216587849697535395937549175 324881774546303093906323763)
    ·
      refine ⟨487322661819454640859485645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324881774546303093906323763 487322661819454640859485645)
      ·
        refine ⟨182745998182295490322307117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487322661819454640859485645 182745998182295490322307117)
        ·
          refine ⟨68529749318360808870865169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182745998182295490322307117 68529749318360808870865169)
          ·
            refine ⟨51397311988770606653148877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68529749318360808870865169 51397311988770606653148877)
            ·
              refine ⟨19273991995788977494930829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51397311988770606653148877 19273991995788977494930829)
              ·
                refine ⟨7227746998420866560599061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19273991995788977494930829 7227746998420866560599061)
                ·
                  refine ⟨338800640550978120028081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7227746998420866560599061 338800640550978120028081)
                  ·
                    rfl

theorem cell23_5938307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 6].length) (baseStart_5938307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938307 prefixEnd_5938307 := by exact prefixLift 5938307
  have htrace : WordTrace (prefixWord ++ tailWord_5938307) baseStart_5938307 baseEnd_5938307 := by
    simpa [prefixWord, tailWord_5938307, baseEnd_5938307] using wordTrace_append hprefix tailTrace_5938307
  have hstable : (prefixWord ++ tailWord_5938307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938307).length < 2 ^ (prefixWord ++ tailWord_5938307).sum := by decide
  have hdescent : baseEnd_5938307 < baseStart_5938307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938367 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 1, 6]
def baseStart_5938367 : Nat := 118140960795 + 5938367 * 2 ^ 59
def prefixEnd_5938367 : Nat := 4983230072969 + 3 ^ 40 * 5938367 * 2
def baseEnd_5938367 : Nat := 1016412191266024281834151

theorem tailTrace_5938367 : CollatzResearch.WordTrace tailWord_5938367 prefixEnd_5938367 1016412191266024281834151 := by
  unfold tailWord_5938367
  simp only [CollatzResearch.WordTrace]
  refine ⟨216590038077318026184733355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144393358718212017456488903 216590038077318026184733355)
  ·
    refine ⟨324885057115977039277100033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216590038077318026184733355 324885057115977039277100033)
    ·
      refine ⟨243663792836982779457825025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324885057115977039277100033 243663792836982779457825025)
      ·
        refine ⟨182747844627737084593368769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243663792836982779457825025 182747844627737084593368769)
        ·
          refine ⟨137060883470802813445026577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182747844627737084593368769 137060883470802813445026577)
          ·
            refine ⟨102795662603102110083769933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137060883470802813445026577 102795662603102110083769933)
            ·
              refine ⟨38548373476163291281413725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102795662603102110083769933 38548373476163291281413725)
              ·
                refine ⟨14455640053561234230530147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38548373476163291281413725 14455640053561234230530147)
                ·
                  refine ⟨21683460080341851345795221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14455640053561234230530147 21683460080341851345795221)
                  ·
                    refine ⟨1016412191266024281834151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21683460080341851345795221 1016412191266024281834151)
                    ·
                      rfl

theorem cell23_5938367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_5938367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938367 prefixEnd_5938367 := by exact prefixLift 5938367
  have htrace : WordTrace (prefixWord ++ tailWord_5938367) baseStart_5938367 baseEnd_5938367 := by
    simpa [prefixWord, tailWord_5938367, baseEnd_5938367] using wordTrace_append hprefix tailTrace_5938367
  have hstable : (prefixWord ++ tailWord_5938367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938367).length < 2 ^ (prefixWord ++ tailWord_5938367).sum := by decide
  have hdescent : baseEnd_5938367 < baseStart_5938367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938378 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_5938378 : Nat := 118140960795 + 5938378 * 2 ^ 59
def prefixEnd_5938378 : Nat := 4983230072969 + 3 ^ 40 * 5938378 * 2
def baseEnd_5938378 : Nat := 3049242222085272302464903

theorem tailTrace_5938378 : CollatzResearch.WordTrace tailWord_5938378 prefixEnd_5938378 3049242222085272302464903 := by
  unfold tailWord_5938378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54147609820069543765845947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144393626186852116708922525 54147609820069543765845947)
  ·
    refine ⟨81221414730104315648768921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54147609820069543765845947 81221414730104315648768921)
    ·
      refine ⟨60916061047578236736576691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81221414730104315648768921 60916061047578236736576691)
      ·
        refine ⟨91374091571367355104865037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60916061047578236736576691 91374091571367355104865037)
        ·
          refine ⟨34265284339262758164324389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91374091571367355104865037 34265284339262758164324389)
          ·
            refine ⟨6424740813611767155810823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34265284339262758164324389 6424740813611767155810823)
            ·
              refine ⟨9637111220417650733716235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424740813611767155810823 9637111220417650733716235)
              ·
                refine ⟨14455666830626476100574353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637111220417650733716235 14455666830626476100574353)
                ·
                  refine ⟨10841750122969857075430765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14455666830626476100574353 10841750122969857075430765)
                  ·
                    refine ⟨4065656296113696403286537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10841750122969857075430765 4065656296113696403286537)
                    ·
                      refine ⟨3049242222085272302464903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065656296113696403286537 3049242222085272302464903)
                      ·
                        rfl

theorem cell23_5938378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_5938378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938378 prefixEnd_5938378 := by exact prefixLift 5938378
  have htrace : WordTrace (prefixWord ++ tailWord_5938378) baseStart_5938378 baseEnd_5938378 := by
    simpa [prefixWord, tailWord_5938378, baseEnd_5938378] using wordTrace_append hprefix tailTrace_5938378
  have hstable : (prefixWord ++ tailWord_5938378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938378).length < 2 ^ (prefixWord ++ tailWord_5938378).sum := by decide
  have hdescent : baseEnd_5938378 < baseStart_5938378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938388 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_5938388 : Nat := 118140960795 + 5938388 * 2 ^ 59
def prefixEnd_5938388 : Nat := 4983230072969 + 3 ^ 40 * 5938388 * 2
def baseEnd_5938388 : Nat := 1016415785630605754446619

theorem tailTrace_5938388 : CollatzResearch.WordTrace tailWord_5938388 prefixEnd_5938388 1016415785630605754446619 := by
  unfold tailWord_5938388
  simp only [CollatzResearch.WordTrace]
  refine ⟨108295402005120973385623909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144393869340161297847498545 108295402005120973385623909)
  ·
    refine ⟨20305387875960182509804483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108295402005120973385623909 20305387875960182509804483)
    ·
      refine ⟨30458081813940273764706725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20305387875960182509804483 30458081813940273764706725)
      ·
        refine ⟨5710890340113801330882511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30458081813940273764706725 5710890340113801330882511)
        ·
          refine ⟨8566335510170701996323767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710890340113801330882511 8566335510170701996323767)
          ·
            refine ⟨12849503265256052994485651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566335510170701996323767 12849503265256052994485651)
            ·
              refine ⟨19274254897884079491728477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12849503265256052994485651 19274254897884079491728477)
              ·
                refine ⟨7227845586706529809398179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19274254897884079491728477 7227845586706529809398179)
                ·
                  refine ⟨10841768380059794714097269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227845586706529809398179 10841768380059794714097269)
                  ·
                    refine ⟨1016415785630605754446619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10841768380059794714097269 1016415785630605754446619)
                    ·
                      rfl

theorem cell23_5938388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_5938388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938388 prefixEnd_5938388 := by exact prefixLift 5938388
  have htrace : WordTrace (prefixWord ++ tailWord_5938388) baseStart_5938388 baseEnd_5938388 := by
    simpa [prefixWord, tailWord_5938388, baseEnd_5938388] using wordTrace_append hprefix tailTrace_5938388
  have hstable : (prefixWord ++ tailWord_5938388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938388).length < 2 ^ (prefixWord ++ tailWord_5938388).sum := by decide
  have hdescent : baseEnd_5938388 < baseStart_5938388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938391 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_5938391 : Nat := 118140960795 + 5938391 * 2 ^ 59
def prefixEnd_5938391 : Nat := 4983230072969 + 3 ^ 40 * 5938391 * 2
def baseEnd_5938391 : Nat := 3049248897333780751602343

theorem tailTrace_5938391 : CollatzResearch.WordTrace tailWord_5938391 prefixEnd_5938391 3049248897333780751602343 := by
  unfold tailWord_5938391
  simp only [CollatzResearch.WordTrace]
  refine ⟨216590913429231078283607027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144393942286154052189071351 216590913429231078283607027)
  ·
    refine ⟨324886370143846617425410541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216590913429231078283607027 324886370143846617425410541)
    ·
      refine ⟨121832388803942481534528953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324886370143846617425410541 121832388803942481534528953)
      ·
        refine ⟨91374291602956861150896715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121832388803942481534528953 91374291602956861150896715)
        ·
          refine ⟨137061437404435291726345073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91374291602956861150896715 137061437404435291726345073)
          ·
            refine ⟨102796078053326468794758805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137061437404435291726345073 102796078053326468794758805)
            ·
              refine ⟨4818566158749678224754319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102796078053326468794758805 4818566158749678224754319)
              ·
                refine ⟨7227849238124517337131479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818566158749678224754319 7227849238124517337131479)
                ·
                  refine ⟨10841773857186776005697219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227849238124517337131479 10841773857186776005697219)
                  ·
                    refine ⟨16262660785780164008545829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10841773857186776005697219 16262660785780164008545829)
                    ·
                      refine ⟨3049248897333780751602343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16262660785780164008545829 3049248897333780751602343)
                      ·
                        rfl

theorem cell23_5938391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_5938391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938391 prefixEnd_5938391 := by exact prefixLift 5938391
  have htrace : WordTrace (prefixWord ++ tailWord_5938391) baseStart_5938391 baseEnd_5938391 := by
    simpa [prefixWord, tailWord_5938391, baseEnd_5938391] using wordTrace_append hprefix tailTrace_5938391
  have hstable : (prefixWord ++ tailWord_5938391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938391).length < 2 ^ (prefixWord ++ tailWord_5938391).sum := by decide
  have hdescent : baseEnd_5938391 < baseStart_5938391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938401 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_5938401 : Nat := 118140960795 + 5938401 * 2 ^ 59
def prefixEnd_5938401 : Nat := 4983230072969 + 3 ^ 40 * 5938401 * 2
def baseEnd_5938401 : Nat := 1016418010713441904159099

theorem tailTrace_5938401 : CollatzResearch.WordTrace tailWord_5938401 prefixEnd_5938401 1016418010713441904159099 := by
  unfold tailWord_5938401
  simp only [CollatzResearch.WordTrace]
  refine ⟨216591278159194849991471057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144394185439463233327647371 216591278159194849991471057)
  ·
    refine ⟨162443458619396137493603293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216591278159194849991471057 162443458619396137493603293)
    ·
      refine ⟨60916296982273551560101235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162443458619396137493603293 60916296982273551560101235)
      ·
        refine ⟨91374445473410327340151853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60916296982273551560101235 91374445473410327340151853)
        ·
          refine ⟨34265417052528872752556945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91374445473410327340151853 34265417052528872752556945)
          ·
            refine ⟨25699062789396654564417709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34265417052528872752556945 25699062789396654564417709)
            ·
              refine ⟨9637148546023745461656641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25699062789396654564417709 9637148546023745461656641)
              ·
                refine ⟨7227861409517809096242481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9637148546023745461656641 7227861409517809096242481)
                ·
                  refine ⟨5420896057138356822181861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7227861409517809096242481 5420896057138356822181861)
                  ·
                    refine ⟨1016418010713441904159099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5420896057138356822181861 1016418010713441904159099)
                    ·
                      rfl

theorem cell23_5938401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_5938401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938401 prefixEnd_5938401 := by exact prefixLift 5938401
  have htrace : WordTrace (prefixWord ++ tailWord_5938401) baseStart_5938401 baseEnd_5938401 := by
    simpa [prefixWord, tailWord_5938401, baseEnd_5938401] using wordTrace_append hprefix tailTrace_5938401
  have hstable : (prefixWord ++ tailWord_5938401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938401).length < 2 ^ (prefixWord ++ tailWord_5938401).sum := by decide
  have hdescent : baseEnd_5938401 < baseStart_5938401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938408 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5938408 : Nat := 118140960795 + 5938408 * 2 ^ 59
def prefixEnd_5938408 : Nat := 4983230072969 + 3 ^ 40 * 5938408 * 2
def baseEnd_5938408 : Nat := 3049257626504907185089765

theorem tailTrace_5938408 : CollatzResearch.WordTrace tailWord_5938408 prefixEnd_5938408 3049257626504907185089765 := by
  unfold tailWord_5938408
  simp only [CollatzResearch.WordTrace]
  refine ⟨108295766735084745093487939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144394355646779660124650585 108295766735084745093487939)
  ·
    refine ⟨162443650102627117640231909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108295766735084745093487939 162443650102627117640231909)
    ·
      refine ⟨30458184394242584557543483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162443650102627117640231909 30458184394242584557543483)
      ·
        refine ⟨45687276591363876836315225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30458184394242584557543483 45687276591363876836315225)
        ·
          refine ⟨34265457443522907627236419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45687276591363876836315225 34265457443522907627236419)
          ·
            refine ⟨51398186165284361440854629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34265457443522907627236419 51398186165284361440854629)
            ·
              refine ⟨9637159905990817770160243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51398186165284361440854629 9637159905990817770160243)
              ·
                refine ⟨14455739858986226655240365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637159905990817770160243 14455739858986226655240365)
                ·
                  refine ⟨5420902447119834995715137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14455739858986226655240365 5420902447119834995715137)
                  ·
                    refine ⟨4065676835339876246786353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5420902447119834995715137 4065676835339876246786353)
                    ·
                      refine ⟨3049257626504907185089765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065676835339876246786353 3049257626504907185089765)
                      ·
                        rfl

theorem cell23_5938408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5938408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938408 prefixEnd_5938408 := by exact prefixLift 5938408
  have htrace : WordTrace (prefixWord ++ tailWord_5938408) baseStart_5938408 baseEnd_5938408 := by
    simpa [prefixWord, tailWord_5938408, baseEnd_5938408] using wordTrace_append hprefix tailTrace_5938408
  have hstable : (prefixWord ++ tailWord_5938408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938408).length < 2 ^ (prefixWord ++ tailWord_5938408).sum := by decide
  have hdescent : baseEnd_5938408 < baseStart_5938408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938418 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_5938418 : Nat := 118140960795 + 5938418 * 2 ^ 59
def prefixEnd_5938418 : Nat := 4983230072969 + 3 ^ 40 * 5938418 * 2
def baseEnd_5938418 : Nat := 1016420920437150715321573

theorem tailTrace_5938418 : CollatzResearch.WordTrace tailWord_5938418 prefixEnd_5938418 1016420920437150715321573 := by
  unfold tailWord_5938418
  simp only [CollatzResearch.WordTrace]
  refine ⟨54147974550033315473709977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144394598800088841263226605 54147974550033315473709977)
  ·
    refine ⟨40610980912524986605282483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54147974550033315473709977 40610980912524986605282483)
    ·
      refine ⟨60916471368787479907923725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40610980912524986605282483 60916471368787479907923725)
      ·
        refine ⟨22843676763295304965471397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60916471368787479907923725 22843676763295304965471397)
        ·
          refine ⟨4283189393117869681025887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22843676763295304965471397 4283189393117869681025887)
          ·
            refine ⟨6424784089676804521538831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283189393117869681025887 6424784089676804521538831)
            ·
              refine ⟨9637176134515206782308247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424784089676804521538831 9637176134515206782308247)
              ·
                refine ⟨14455764201772810173462371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637176134515206782308247 14455764201772810173462371)
                ·
                  refine ⟨21683646302659215260193557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14455764201772810173462371 21683646302659215260193557)
                  ·
                    refine ⟨1016420920437150715321573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21683646302659215260193557 1016420920437150715321573)
                    ·
                      rfl

theorem cell23_5938418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_5938418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938418 prefixEnd_5938418 := by exact prefixLift 5938418
  have htrace : WordTrace (prefixWord ++ tailWord_5938418) baseStart_5938418 baseEnd_5938418 := by
    simpa [prefixWord, tailWord_5938418, baseEnd_5938418] using wordTrace_append hprefix tailTrace_5938418
  have hstable : (prefixWord ++ tailWord_5938418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938418).length < 2 ^ (prefixWord ++ tailWord_5938418).sum := by decide
  have hdescent : baseEnd_5938418 < baseStart_5938418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938428 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_5938428 : Nat := 118140960795 + 5938428 * 2 ^ 59
def prefixEnd_5938428 : Nat := 4983230072969 + 3 ^ 40 * 5938428 * 2
def baseEnd_5938428 : Nat := 3049267896117997106839673

theorem tailTrace_5938428 : CollatzResearch.WordTrace tailWord_5938428 prefixEnd_5938428 3049267896117997106839673 := by
  unfold tailWord_5938428
  simp only [CollatzResearch.WordTrace]
  refine ⟨108296131465048516801351969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144394841953398022401802625 108296131465048516801351969)
  ·
    refine ⟨81222098598786387601013977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108296131465048516801351969 81222098598786387601013977)
    ·
      refine ⟨60916573949089790700760483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81222098598786387601013977 60916573949089790700760483)
      ·
        refine ⟨91374860923634686051140725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60916573949089790700760483 91374860923634686051140725)
        ·
          refine ⟨8566393211590751817294443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91374860923634686051140725 8566393211590751817294443)
          ·
            refine ⟨12849589817386127725941665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566393211590751817294443 12849589817386127725941665)
            ·
              refine ⟨9637192363039595794456249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12849589817386127725941665 9637192363039595794456249)
              ·
                refine ⟨7227894272279696845842187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9637192363039595794456249 7227894272279696845842187)
                ·
                  refine ⟨10841841408419545268763281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227894272279696845842187 10841841408419545268763281)
                  ·
                    refine ⟨8131381056314658951572461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10841841408419545268763281 8131381056314658951572461)
                    ·
                      refine ⟨3049267896117997106839673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8131381056314658951572461 3049267896117997106839673)
                      ·
                        rfl

theorem cell23_5938428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_5938428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938428 prefixEnd_5938428 := by exact prefixLift 5938428
  have htrace : WordTrace (prefixWord ++ tailWord_5938428) baseStart_5938428 baseEnd_5938428 := by
    simpa [prefixWord, tailWord_5938428, baseEnd_5938428] using wordTrace_append hprefix tailTrace_5938428
  have hstable : (prefixWord ++ tailWord_5938428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938428).length < 2 ^ (prefixWord ++ tailWord_5938428).sum := by decide
  have hdescent : baseEnd_5938428 < baseStart_5938428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938437 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_5938437 : Nat := 118140960795 + 5938437 * 2 ^ 59
def prefixEnd_5938437 : Nat := 4983230072969 + 3 ^ 40 * 5938437 * 2
def baseEnd_5938437 : Nat := 3049272517443887571627131

theorem tailTrace_5938437 : CollatzResearch.WordTrace tailWord_5938437 prefixEnd_5938437 3049272517443887571627131 := by
  unfold tailWord_5938437
  simp only [CollatzResearch.WordTrace]
  refine ⟨216592591187064428139781565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144395060791376285426521043 216592591187064428139781565)
  ·
    refine ⟨81222221695149160552418087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216592591187064428139781565 81222221695149160552418087)
    ·
      refine ⟨121833332542723740828627131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81222221695149160552418087 121833332542723740828627131)
      ·
        refine ⟨182749998814085611242940697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121833332542723740828627131 182749998814085611242940697)
        ·
          refine ⟨137062499110564208432205523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182749998814085611242940697 137062499110564208432205523)
          ·
            refine ⟨205593748665846312648308285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137062499110564208432205523 205593748665846312648308285)
            ·
              refine ⟨77097655749692367243115607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205593748665846312648308285 77097655749692367243115607)
              ·
                refine ⟨115646483624538550864673411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77097655749692367243115607 115646483624538550864673411)
                ·
                  refine ⟨173469725436807826297010117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115646483624538550864673411 173469725436807826297010117)
                  ·
                    refine ⟨32525573519401467430689397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173469725436807826297010117 32525573519401467430689397)
                    ·
                      refine ⟨3049272517443887571627131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32525573519401467430689397 3049272517443887571627131)
                      ·
                        rfl

theorem cell23_5938437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_5938437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938437 prefixEnd_5938437 := by exact prefixLift 5938437
  have htrace : WordTrace (prefixWord ++ tailWord_5938437) baseStart_5938437 baseEnd_5938437 := by
    simpa [prefixWord, tailWord_5938437, baseEnd_5938437] using wordTrace_append hprefix tailTrace_5938437
  have hstable : (prefixWord ++ tailWord_5938437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938437).length < 2 ^ (prefixWord ++ tailWord_5938437).sum := by decide
  have hdescent : baseEnd_5938437 < baseStart_5938437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938447 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_5938447 : Nat := 118140960795 + 5938447 * 2 ^ 59
def prefixEnd_5938447 : Nat := 4983230072969 + 3 ^ 40 * 5938447 * 2
def baseEnd_5938447 : Nat := 3049277652250432532502085

theorem tailTrace_5938447 : CollatzResearch.WordTrace tailWord_5938447 prefixEnd_5938447 3049277652250432532502085 := by
  unfold tailWord_5938447
  simp only [CollatzResearch.WordTrace]
  refine ⟨216592955917028199847645595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144395303944685466565097063 216592955917028199847645595)
  ·
    refine ⟨324889433875542299771468393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216592955917028199847645595 324889433875542299771468393)
    ·
      refine ⟨243667075406656724828601295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324889433875542299771468393 243667075406656724828601295)
      ·
        refine ⟨365500613109985087242901943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243667075406656724828601295 365500613109985087242901943)
        ·
          refine ⟨548250919664977630864352915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365500613109985087242901943 548250919664977630864352915)
          ·
            refine ⟨822376379497466446296529373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548250919664977630864352915 822376379497466446296529373)
            ·
              refine ⟨308391142311549917361198515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822376379497466446296529373 308391142311549917361198515)
              ·
                refine ⟨462586713467324876041797773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308391142311549917361198515 462586713467324876041797773)
                ·
                  refine ⟨173470017550246828515674165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462586713467324876041797773 173470017550246828515674165)
                  ·
                    refine ⟨16262814145335640173344453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173470017550246828515674165 16262814145335640173344453)
                    ·
                      refine ⟨3049277652250432532502085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16262814145335640173344453 3049277652250432532502085)
                      ·
                        rfl

theorem cell23_5938447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_5938447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938447 prefixEnd_5938447 := by exact prefixLift 5938447
  have htrace : WordTrace (prefixWord ++ tailWord_5938447) baseStart_5938447 baseEnd_5938447 := by
    simpa [prefixWord, tailWord_5938447, baseEnd_5938447] using wordTrace_append hprefix tailTrace_5938447
  have hstable : (prefixWord ++ tailWord_5938447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938447).length < 2 ^ (prefixWord ++ tailWord_5938447).sum := by decide
  have hdescent : baseEnd_5938447 < baseStart_5938447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938485 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_5938485 : Nat := 118140960795 + 5938485 * 2 ^ 59
def prefixEnd_5938485 : Nat := 4983230072969 + 3 ^ 40 * 5938485 * 2
def baseEnd_5938485 : Nat := 3049297164515303383826911

theorem tailTrace_5938485 : CollatzResearch.WordTrace tailWord_5938485 prefixEnd_5938485 3049297164515303383826911 := by
  unfold tailWord_5938485
  simp only [CollatzResearch.WordTrace]
  refine ⟨216594341890890532337528909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144396227927260354891685939 216594341890890532337528909)
  ·
    refine ⟨81222878209083949626573341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216594341890890532337528909 81222878209083949626573341)
    ·
      refine ⟨30458579328406481109965003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81222878209083949626573341 30458579328406481109965003)
      ·
        refine ⟨45687868992609721664947505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30458579328406481109965003 45687868992609721664947505)
        ·
          refine ⟨34265901744457291248710629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45687868992609721664947505 34265901744457291248710629)
          ·
            refine ⟨6424856577085742109133243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34265901744457291248710629 6424856577085742109133243)
            ·
              refine ⟨9637284865628613163699865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424856577085742109133243 9637284865628613163699865)
              ·
                refine ⟨7227963649221459872774899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9637284865628613163699865 7227963649221459872774899)
                ·
                  refine ⟨10841945473832189809162349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227963649221459872774899 10841945473832189809162349)
                  ·
                    refine ⟨4065729552687071178435881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10841945473832189809162349 4065729552687071178435881)
                    ·
                      refine ⟨3049297164515303383826911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065729552687071178435881 3049297164515303383826911)
                      ·
                        rfl

theorem cell23_5938485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_5938485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938485 prefixEnd_5938485 := by exact prefixLift 5938485
  have htrace : WordTrace (prefixWord ++ tailWord_5938485) baseStart_5938485 baseEnd_5938485 := by
    simpa [prefixWord, tailWord_5938485, baseEnd_5938485] using wordTrace_append hprefix tailTrace_5938485
  have hstable : (prefixWord ++ tailWord_5938485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938485).length < 2 ^ (prefixWord ++ tailWord_5938485).sum := by decide
  have hdescent : baseEnd_5938485 < baseStart_5938485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938507 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_5938507 : Nat := 118140960795 + 5938507 * 2 ^ 59
def prefixEnd_5938507 : Nat := 4983230072969 + 3 ^ 40 * 5938507 * 2
def baseEnd_5938507 : Nat := 3049308461089702297751809

theorem tailTrace_5938507 : CollatzResearch.WordTrace tailWord_5938507 prefixEnd_5938507 3049308461089702297751809 := by
  unfold tailWord_5938507
  simp only [CollatzResearch.WordTrace]
  refine ⟨216595144296810830094829775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144396762864540553396553183 216595144296810830094829775)
  ·
    refine ⟨324892716445216245142244663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216595144296810830094829775 324892716445216245142244663)
    ·
      refine ⟨487339074667824367713366995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324892716445216245142244663 487339074667824367713366995)
      ·
        refine ⟨731008612001736551570050493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487339074667824367713366995 731008612001736551570050493)
        ·
          refine ⟨274128229500651206838768935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731008612001736551570050493 274128229500651206838768935)
          ·
            refine ⟨411192344250976810258153403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274128229500651206838768935 411192344250976810258153403)
            ·
              refine ⟨616788516376465215387230105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411192344250976810258153403 616788516376465215387230105)
              ·
                refine ⟨462591387282348911540422579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616788516376465215387230105 462591387282348911540422579)
                ·
                  refine ⟨693887080923523367310633869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462591387282348911540422579 693887080923523367310633869)
                  ·
                    refine ⟨260207655346321262741487701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693887080923523367310633869 260207655346321262741487701)
                    ·
                      refine ⟨3049308461089702297751809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 260207655346321262741487701 3049308461089702297751809)
                      ·
                        rfl

theorem cell23_5938507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_5938507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938507 prefixEnd_5938507 := by exact prefixLift 5938507
  have htrace : WordTrace (prefixWord ++ tailWord_5938507) baseStart_5938507 baseEnd_5938507 := by
    simpa [prefixWord, tailWord_5938507, baseEnd_5938507] using wordTrace_append hprefix tailTrace_5938507
  have hstable : (prefixWord ++ tailWord_5938507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938507).length < 2 ^ (prefixWord ++ tailWord_5938507).sum := by decide
  have hdescent : baseEnd_5938507 < baseStart_5938507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938525 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5938525 : Nat := 118140960795 + 5938525 * 2 ^ 59
def prefixEnd_5938525 : Nat := 4983230072969 + 3 ^ 40 * 5938525 * 2
def baseEnd_5938525 : Nat := 1016439234580494409108909

theorem tailTrace_5938525 : CollatzResearch.WordTrace tailWord_5938525 prefixEnd_5938525 1016439234580494409108909 := by
  unfold tailWord_5938525
  simp only [CollatzResearch.WordTrace]
  refine ⟨216595800810745619168985029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144397200540497079445990019 216595800810745619168985029)
  ·
    refine ⟨40611712652014803594184693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216595800810745619168985029 40611712652014803594184693)
    ·
      refine ⟨3807348061126387836954815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40611712652014803594184693 3807348061126387836954815)
      ·
        refine ⟨5711022091689581755432223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807348061126387836954815 5711022091689581755432223)
        ·
          refine ⟨8566533137534372633148335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711022091689581755432223 8566533137534372633148335)
          ·
            refine ⟨12849799706301558949722503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566533137534372633148335 12849799706301558949722503)
            ·
              refine ⟨19274699559452338424583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12849799706301558949722503 19274699559452338424583755)
              ·
                refine ⟨28912049339178507636875633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19274699559452338424583755 28912049339178507636875633)
                ·
                  refine ⟨21684037004383880727656725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28912049339178507636875633 21684037004383880727656725)
                  ·
                    refine ⟨1016439234580494409108909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21684037004383880727656725 1016439234580494409108909)
                    ·
                      rfl

theorem cell23_5938525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5938525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938525 prefixEnd_5938525 := by exact prefixLift 5938525
  have htrace : WordTrace (prefixWord ++ tailWord_5938525) baseStart_5938525 baseEnd_5938525 := by
    simpa [prefixWord, tailWord_5938525, baseEnd_5938525] using wordTrace_append hprefix tailTrace_5938525
  have hstable : (prefixWord ++ tailWord_5938525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938525).length < 2 ^ (prefixWord ++ tailWord_5938525).sum := by decide
  have hdescent : baseEnd_5938525 < baseStart_5938525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938531 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5938531 : Nat := 118140960795 + 5938531 * 2 ^ 59
def prefixEnd_5938531 : Nat := 4983230072969 + 3 ^ 40 * 5938531 * 2
def baseEnd_5938531 : Nat := 3049320784625410203851699

theorem tailTrace_5938531 : CollatzResearch.WordTrace tailWord_5938531 prefixEnd_5938531 3049320784625410203851699 := by
  unfold tailWord_5938531
  simp only [CollatzResearch.WordTrace]
  refine ⟨216596019648723882193703447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144397346432482588129135631 216596019648723882193703447)
  ·
    refine ⟨324894029473085823290555171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216596019648723882193703447 324894029473085823290555171)
    ·
      refine ⟨487341044209628734935832757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324894029473085823290555171 487341044209628734935832757)
      ·
        refine ⟨45688222894652693900234321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 487341044209628734935832757 45688222894652693900234321)
        ·
          refine ⟨34266167170989520425175741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45688222894652693900234321 34266167170989520425175741)
          ·
            refine ⟨12849812689121070159440903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34266167170989520425175741 12849812689121070159440903)
            ·
              refine ⟨19274719033681605239161355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12849812689121070159440903 19274719033681605239161355)
              ·
                refine ⟨28912078550522407858742033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19274719033681605239161355 28912078550522407858742033)
                ·
                  refine ⟨21684058912891805894056525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28912078550522407858742033 21684058912891805894056525)
                  ·
                    refine ⟨8131522092334427210271197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21684058912891805894056525 8131522092334427210271197)
                    ·
                      refine ⟨3049320784625410203851699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8131522092334427210271197 3049320784625410203851699)
                      ·
                        rfl

theorem cell23_5938531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5938531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938531 prefixEnd_5938531 := by exact prefixLift 5938531
  have htrace : WordTrace (prefixWord ++ tailWord_5938531) baseStart_5938531 baseEnd_5938531 := by
    simpa [prefixWord, tailWord_5938531, baseEnd_5938531] using wordTrace_append hprefix tailTrace_5938531
  have hstable : (prefixWord ++ tailWord_5938531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938531).length < 2 ^ (prefixWord ++ tailWord_5938531).sum := by decide
  have hdescent : baseEnd_5938531 < baseStart_5938531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938554 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_5938554 : Nat := 118140960795 + 5938554 * 2 ^ 59
def prefixEnd_5938554 : Nat := 4983230072969 + 3 ^ 40 * 5938554 * 2
def baseEnd_5938554 : Nat := 3049332594680463613864093

theorem tailTrace_5938554 : CollatzResearch.WordTrace tailWord_5938554 prefixEnd_5938554 3049332594680463613864093 := by
  unfold tailWord_5938554
  simp only [CollatzResearch.WordTrace]
  refine ⟨54149214631910139280447679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144397905685093704747860477 54149214631910139280447679)
  ·
    refine ⟨81223821947865208920671519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54149214631910139280447679 81223821947865208920671519)
    ·
      refine ⟨121835732921797813381007279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81223821947865208920671519 121835732921797813381007279)
      ·
        refine ⟨182753599382696720071510919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121835732921797813381007279 182753599382696720071510919)
        ·
          refine ⟨274130399074045080107266379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182753599382696720071510919 274130399074045080107266379)
          ·
            refine ⟨411195598611067620160899569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274130399074045080107266379 411195598611067620160899569)
            ·
              refine ⟨308396698958300715120674677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411195598611067620160899569 308396698958300715120674677)
              ·
                refine ⟨28912190527340692042563251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308396698958300715120674677 28912190527340692042563251)
                ·
                  refine ⟨43368285791011038063844877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28912190527340692042563251 43368285791011038063844877)
                  ·
                    refine ⟨16263107171629139273941829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43368285791011038063844877 16263107171629139273941829)
                    ·
                      refine ⟨3049332594680463613864093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16263107171629139273941829 3049332594680463613864093)
                      ·
                        rfl

theorem cell23_5938554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_5938554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938554 prefixEnd_5938554 := by exact prefixLift 5938554
  have htrace : WordTrace (prefixWord ++ tailWord_5938554) baseStart_5938554 baseEnd_5938554 := by
    simpa [prefixWord, tailWord_5938554, baseEnd_5938554] using wordTrace_append hprefix tailTrace_5938554
  have hstable : (prefixWord ++ tailWord_5938554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938554).length < 2 ^ (prefixWord ++ tailWord_5938554).sum := by decide
  have hdescent : baseEnd_5938554 < baseStart_5938554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938571 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 2]
def baseStart_5938571 : Nat := 118140960795 + 5938571 * 2 ^ 59
def prefixEnd_5938571 : Nat := 4983230072969 + 3 ^ 40 * 5938571 * 2
def baseEnd_5938571 : Nat := 3049341323851590047351515

theorem tailTrace_5938571 : CollatzResearch.WordTrace tailWord_5938571 prefixEnd_5938571 3049341323851590047351515 := by
  unfold tailWord_5938571
  simp only [CollatzResearch.WordTrace]
  refine ⟨216597478568578969025159567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144398319045719312683439711 216597478568578969025159567)
  ·
    refine ⟨324896217852868453537739351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216597478568578969025159567 324896217852868453537739351)
    ·
      refine ⟨487344326779302680306609027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324896217852868453537739351 487344326779302680306609027)
      ·
        refine ⟨731016490168954020459913541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487344326779302680306609027 731016490168954020459913541)
        ·
          refine ⟨137065591906678878836233789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 731016490168954020459913541 137065591906678878836233789)
          ·
            refine ⟨51399596965004579563587671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137065591906678878836233789 51399596965004579563587671)
            ·
              refine ⟨77099395447506869345381507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51399596965004579563587671 77099395447506869345381507)
              ·
                refine ⟨115649093171260304018072261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77099395447506869345381507 115649093171260304018072261)
                ·
                  refine ⟨21684204969611307003388549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115649093171260304018072261 21684204969611307003388549)
                  ·
                    refine ⟨4065788431802120063135353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21684204969611307003388549 4065788431802120063135353)
                    ·
                      refine ⟨3049341323851590047351515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065788431802120063135353 3049341323851590047351515)
                      ·
                        rfl

theorem cell23_5938571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4, 2].length) (baseStart_5938571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938571 prefixEnd_5938571 := by exact prefixLift 5938571
  have htrace : WordTrace (prefixWord ++ tailWord_5938571) baseStart_5938571 baseEnd_5938571 := by
    simpa [prefixWord, tailWord_5938571, baseEnd_5938571] using wordTrace_append hprefix tailTrace_5938571
  have hstable : (prefixWord ++ tailWord_5938571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938571).length < 2 ^ (prefixWord ++ tailWord_5938571).sum := by decide
  have hdescent : baseEnd_5938571 < baseStart_5938571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938581 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_5938581 : Nat := 118140960795 + 5938581 * 2 ^ 59
def prefixEnd_5938581 : Nat := 4983230072969 + 3 ^ 40 * 5938581 * 2
def baseEnd_5938581 : Nat := 1016448819552711669408823

theorem tailTrace_5938581 : CollatzResearch.WordTrace tailWord_5938581 prefixEnd_5938581 1016448819552711669408823 := by
  unfold tailWord_5938581
  simp only [CollatzResearch.WordTrace]
  refine ⟨216597843298542740733023597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144398562199028493822015731 216597843298542740733023597)
  ·
    refine ⟨81224191236953527774883849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216597843298542740733023597 81224191236953527774883849)
    ·
      refine ⟨60918143427715145831162887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81224191236953527774883849 60918143427715145831162887)
      ·
        refine ⟨91377215141572718746744331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60918143427715145831162887 91377215141572718746744331)
        ·
          refine ⟨137065822712359078120116497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91377215141572718746744331 137065822712359078120116497)
          ·
            refine ⟨102799367034269308590087373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137065822712359078120116497 102799367034269308590087373)
            ·
              refine ⟨38549762637850990721282765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102799367034269308590087373 38549762637850990721282765)
              ·
                refine ⟨14456160989194121520481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38549762637850990721282765 14456160989194121520481037)
                ·
                  refine ⟨5421060370947795570180389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14456160989194121520481037 5421060370947795570180389)
                  ·
                    refine ⟨1016448819552711669408823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421060370947795570180389 1016448819552711669408823)
                    ·
                      rfl

theorem cell23_5938581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_5938581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938581 prefixEnd_5938581 := by exact prefixLift 5938581
  have htrace : WordTrace (prefixWord ++ tailWord_5938581) baseStart_5938581 baseEnd_5938581 := by
    simpa [prefixWord, tailWord_5938581, baseEnd_5938581] using wordTrace_append hprefix tailTrace_5938581
  have hstable : (prefixWord ++ tailWord_5938581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938581).length < 2 ^ (prefixWord ++ tailWord_5938581).sum := by decide
  have hdescent : baseEnd_5938581 < baseStart_5938581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938591 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_5938591 : Nat := 118140960795 + 5938591 * 2 ^ 59
def prefixEnd_5938591 : Nat := 4983230072969 + 3 ^ 40 * 5938591 * 2
def baseEnd_5938591 : Nat := 3049351593464679969101423

theorem tailTrace_5938591 : CollatzResearch.WordTrace tailWord_5938591 prefixEnd_5938591 3049351593464679969101423 := by
  unfold tailWord_5938591
  simp only [CollatzResearch.WordTrace]
  refine ⟨216598208028506512440887627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144398805352337674960591751 216598208028506512440887627)
  ·
    refine ⟨324897312042759768661331441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216598208028506512440887627 324897312042759768661331441)
    ·
      refine ⟨243672984032069826495998581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324897312042759768661331441 243672984032069826495998581)
      ·
        refine ⟨22844342253006546233999867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243672984032069826495998581 22844342253006546233999867)
        ·
          refine ⟨34266513379509819350999801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22844342253006546233999867 34266513379509819350999801)
          ·
            refine ⟨25699885034632364513249851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34266513379509819350999801 25699885034632364513249851)
            ·
              refine ⟨38549827551948546769874777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25699885034632364513249851 38549827551948546769874777)
              ·
                refine ⟨28912370663961410077406083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38549827551948546769874777 28912370663961410077406083)
                ·
                  refine ⟨43368555995942115116109125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28912370663961410077406083 43368555995942115116109125)
                  ·
                    refine ⟨8131604249239146584270461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43368555995942115116109125 8131604249239146584270461)
                    ·
                      refine ⟨3049351593464679969101423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8131604249239146584270461 3049351593464679969101423)
                      ·
                        rfl

theorem cell23_5938591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_5938591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938591 prefixEnd_5938591 := by exact prefixLift 5938591
  have htrace : WordTrace (prefixWord ++ tailWord_5938591) baseStart_5938591 baseEnd_5938591 := by
    simpa [prefixWord, tailWord_5938591, baseEnd_5938591] using wordTrace_append hprefix tailTrace_5938591
  have hstable : (prefixWord ++ tailWord_5938591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938591).length < 2 ^ (prefixWord ++ tailWord_5938591).sum := by decide
  have hdescent : baseEnd_5938591 < baseStart_5938591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938671 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 6, 4]
def baseStart_5938671 : Nat := 118140960795 + 5938671 * 2 ^ 59
def prefixEnd_5938671 : Nat := 4983230072969 + 3 ^ 40 * 5938671 * 2
def baseEnd_5938671 : Nat := 1016464223972346552033685

theorem tailTrace_5938671 : CollatzResearch.WordTrace tailWord_5938671 prefixEnd_5938671 1016464223972346552033685 := by
  unfold tailWord_5938671
  simp only [CollatzResearch.WordTrace]
  refine ⟨216601125868216686103799867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144400750578811124069199911 216601125868216686103799867)
  ·
    refine ⟨324901688802325029155699801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216601125868216686103799867 324901688802325029155699801)
    ·
      refine ⟨243676266601743771866774851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324901688802325029155699801 243676266601743771866774851)
      ·
        refine ⟨365514399902615657800162277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243676266601743771866774851 365514399902615657800162277)
        ·
          refine ⟨68533949981740435837530427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365514399902615657800162277 68533949981740435837530427)
          ·
            refine ⟨102800924972610653756295641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68533949981740435837530427 102800924972610653756295641)
            ·
              refine ⟨77100693729457990317221731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102800924972610653756295641 77100693729457990317221731)
              ·
                refine ⟨115651040594186985475832597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77100693729457990317221731 115651040594186985475832597)
                ·
                  refine ⟨5421142527852514944179653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115651040594186985475832597 5421142527852514944179653)
                  ·
                    refine ⟨1016464223972346552033685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421142527852514944179653 1016464223972346552033685)
                    ·
                      rfl

theorem cell23_5938671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_5938671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938671 prefixEnd_5938671 := by exact prefixLift 5938671
  have htrace : WordTrace (prefixWord ++ tailWord_5938671) baseStart_5938671 baseEnd_5938671 := by
    simpa [prefixWord, tailWord_5938671, baseEnd_5938671] using wordTrace_append hprefix tailTrace_5938671
  have hstable : (prefixWord ++ tailWord_5938671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938671).length < 2 ^ (prefixWord ++ tailWord_5938671).sum := by decide
  have hdescent : baseEnd_5938671 < baseStart_5938671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938698 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_5938698 : Nat := 118140960795 + 5938698 * 2 ^ 59
def prefixEnd_5938698 : Nat := 4983230072969 + 3 ^ 40 * 5938698 * 2
def baseEnd_5938698 : Nat := 3049406535894711050463431

theorem tailTrace_5938698 : CollatzResearch.WordTrace tailWord_5938698 prefixEnd_5938698 3049406535894711050463431 := by
  unfold tailWord_5938698
  simp only [CollatzResearch.WordTrace]
  refine ⟨54150527659779717428758187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144401407092745913143355165 54150527659779717428758187)
  ·
    refine ⟨81225791489669576143137281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54150527659779717428758187 81225791489669576143137281)
    ·
      refine ⟨60919343617252182107352961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81225791489669576143137281 60919343617252182107352961)
      ·
        refine ⟨45689507712939136580514721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60919343617252182107352961 45689507712939136580514721)
        ·
          refine ⟨34267130784704352435386041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45689507712939136580514721 34267130784704352435386041)
          ·
            refine ⟨25700348088528264326539531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34267130784704352435386041 25700348088528264326539531)
            ·
              refine ⟨38550522132792396489809297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25700348088528264326539531 38550522132792396489809297)
              ·
                refine ⟨28912891599594297367356973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38550522132792396489809297 28912891599594297367356973)
                ·
                  refine ⟨10842334349847861512758865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28912891599594297367356973 10842334349847861512758865)
                  ·
                    refine ⟨8131750762385896134569149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10842334349847861512758865 8131750762385896134569149)
                    ·
                      refine ⟨3049406535894711050463431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8131750762385896134569149 3049406535894711050463431)
                      ·
                        rfl

theorem cell23_5938698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_5938698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938698 prefixEnd_5938698 := by exact prefixLift 5938698
  have htrace : WordTrace (prefixWord ++ tailWord_5938698) baseStart_5938698 baseEnd_5938698 := by
    simpa [prefixWord, tailWord_5938698, baseEnd_5938698] using wordTrace_append hprefix tailTrace_5938698
  have hstable : (prefixWord ++ tailWord_5938698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938698).length < 2 ^ (prefixWord ++ tailWord_5938698).sum := by decide
  have hdescent : baseEnd_5938698 < baseStart_5938698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938712 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_5938712 : Nat := 118140960795 + 5938712 * 2 ^ 59
def prefixEnd_5938712 : Nat := 4983230072969 + 3 ^ 40 * 5938712 * 2
def baseEnd_5938712 : Nat := 3049413724623873995688367

theorem tailTrace_5938712 : CollatzResearch.WordTrace tailWord_5938712 prefixEnd_5938712 3049413724623873995688367 := by
  unfold tailWord_5938712
  simp only [CollatzResearch.WordTrace]
  refine ⟨108301310630534075053021195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144401747507378766737361593 108301310630534075053021195)
  ·
    refine ⟨162451965945801112579531793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108301310630534075053021195 162451965945801112579531793)
    ·
      refine ⟨121838974459350834434648845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162451965945801112579531793 121838974459350834434648845)
      ·
        refine ⟨45689615422256562912993317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121838974459350834434648845 45689615422256562912993317)
        ·
          refine ⟨8566802891673105546186247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45689615422256562912993317 8566802891673105546186247)
          ·
            refine ⟨12850204337509658319279371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566802891673105546186247 12850204337509658319279371)
            ·
              refine ⟨19275306506264487478919057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850204337509658319279371 19275306506264487478919057)
              ·
                refine ⟨14456479879698365609189293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19275306506264487478919057 14456479879698365609189293)
                ·
                  refine ⟨5421179954886887103445985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14456479879698365609189293 5421179954886887103445985)
                  ·
                    refine ⟨4065884966165165327584489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5421179954886887103445985 4065884966165165327584489)
                    ·
                      refine ⟨3049413724623873995688367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065884966165165327584489 3049413724623873995688367)
                      ·
                        rfl

theorem cell23_5938712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_5938712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938712 prefixEnd_5938712 := by exact prefixLift 5938712
  have htrace : WordTrace (prefixWord ++ tailWord_5938712) baseStart_5938712 baseEnd_5938712 := by
    simpa [prefixWord, tailWord_5938712, baseEnd_5938712] using wordTrace_append hprefix tailTrace_5938712
  have hstable : (prefixWord ++ tailWord_5938712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938712).length < 2 ^ (prefixWord ++ tailWord_5938712).sum := by decide
  have hdescent : baseEnd_5938712 < baseStart_5938712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938745 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5938745 : Nat := 118140960795 + 5938745 * 2 ^ 59
def prefixEnd_5938745 : Nat := 4983230072969 + 3 ^ 40 * 5938745 * 2
def baseEnd_5938745 : Nat := 3049430669485472366575715

theorem tailTrace_5938745 : CollatzResearch.WordTrace tailWord_5938745 prefixEnd_5938745 3049430669485472366575715 := by
  unfold tailWord_5938745
  simp only [CollatzResearch.WordTrace]
  refine ⟨216603824869948596741993689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144402549913299064494662459 216603824869948596741993689)
  ·
    refine ⟨162452868652461447556495267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216603824869948596741993689 162452868652461447556495267)
    ·
      refine ⟨243679302978692171334742901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162452868652461447556495267 243679302978692171334742901)
      ·
        refine ⟨22844934654252391062632147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243679302978692171334742901 22844934654252391062632147)
        ·
          refine ⟨34267401981378586593948221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22844934654252391062632147 34267401981378586593948221)
          ·
            refine ⟨12850275743016969972730583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34267401981378586593948221 12850275743016969972730583)
            ·
              refine ⟨19275413614525454959095875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850275743016969972730583 19275413614525454959095875)
              ·
                refine ⟨28913120421788182438643813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19275413614525454959095875 28913120421788182438643813)
                ·
                  refine ⟨5421210079085284207245715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28913120421788182438643813 5421210079085284207245715)
                  ·
                    refine ⟨8131815118627926310868573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5421210079085284207245715 8131815118627926310868573)
                    ·
                      refine ⟨3049430669485472366575715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8131815118627926310868573 3049430669485472366575715)
                      ·
                        rfl

theorem cell23_5938745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5938745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938745 prefixEnd_5938745 := by exact prefixLift 5938745
  have htrace : WordTrace (prefixWord ++ tailWord_5938745) baseStart_5938745 baseEnd_5938745 := by
    simpa [prefixWord, tailWord_5938745, baseEnd_5938745] using wordTrace_append hprefix tailTrace_5938745
  have hstable : (prefixWord ++ tailWord_5938745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938745).length < 2 ^ (prefixWord ++ tailWord_5938745).sum := by decide
  have hdescent : baseEnd_5938745 < baseStart_5938745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938762 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_5938762 : Nat := 118140960795 + 5938762 * 2 ^ 59
def prefixEnd_5938762 : Nat := 4983230072969 + 3 ^ 40 * 5938762 * 2
def baseEnd_5938762 : Nat := 3049439398656598800063137

theorem tailTrace_5938762 : CollatzResearch.WordTrace tailWord_5938762 prefixEnd_5938762 3049439398656598800063137 := by
  unfold tailWord_5938762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54151111227721752161340635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144402963273924672430241693 54151111227721752161340635)
  ·
    refine ⟨81226666841582628242010953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54151111227721752161340635 81226666841582628242010953)
    ·
      refine ⟨60920000131186971181508215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81226666841582628242010953 60920000131186971181508215)
      ·
        refine ⟨91380000196780456772262323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60920000131186971181508215 91380000196780456772262323)
        ·
          refine ⟨137070000295170685158393485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91380000196780456772262323 137070000295170685158393485)
          ·
            refine ⟨51401250110689006934397557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137070000295170685158393485 51401250110689006934397557)
            ·
              refine ⟨4818867197877094400099771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51401250110689006934397557 4818867197877094400099771)
              ·
                refine ⟨7228300796815641600149657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818867197877094400099771 7228300796815641600149657)
                ·
                  refine ⟨5421225597611731200112243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7228300796815641600149657 5421225597611731200112243)
                  ·
                    refine ⟨8131838396417596800168365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5421225597611731200112243 8131838396417596800168365)
                    ·
                      refine ⟨3049439398656598800063137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8131838396417596800168365 3049439398656598800063137)
                      ·
                        rfl

theorem cell23_5938762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_5938762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938762 prefixEnd_5938762 := by exact prefixLift 5938762
  have htrace : WordTrace (prefixWord ++ tailWord_5938762) baseStart_5938762 baseEnd_5938762 := by
    simpa [prefixWord, tailWord_5938762, baseEnd_5938762] using wordTrace_append hprefix tailTrace_5938762
  have hstable : (prefixWord ++ tailWord_5938762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938762).length < 2 ^ (prefixWord ++ tailWord_5938762).sum := by decide
  have hdescent : baseEnd_5938762 < baseStart_5938762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938772 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_5938772 : Nat := 118140960795 + 5938772 * 2 ^ 59
def prefixEnd_5938772 : Nat := 4983230072969 + 3 ^ 40 * 5938772 * 2
def baseEnd_5938772 : Nat := 3049444533463143760938091

theorem tailTrace_5938772 : CollatzResearch.WordTrace tailWord_5938772 prefixEnd_5938772 3049444533463143760938091 := by
  unfold tailWord_5938772
  simp only [CollatzResearch.WordTrace]
  refine ⟨108302404820425390176613285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144403206427233853568817713 108302404820425390176613285)
  ·
    refine ⟨20306700903829760658114991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108302404820425390176613285 20306700903829760658114991)
    ·
      refine ⟨30460051355744640987172487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306700903829760658114991 30460051355744640987172487)
      ·
        refine ⟨45690077033616961480758731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30460051355744640987172487 45690077033616961480758731)
        ·
          refine ⟨68535115550425442221138097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45690077033616961480758731 68535115550425442221138097)
          ·
            refine ⟨51401336662819081665853573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68535115550425442221138097 51401336662819081665853573)
            ·
              refine ⟨9637750624278577812347545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51401336662819081665853573 9637750624278577812347545)
              ·
                refine ⟨7228312968208933359260659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9637750624278577812347545 7228312968208933359260659)
                ·
                  refine ⟨10842469452313400038890989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228312968208933359260659 10842469452313400038890989)
                  ·
                    refine ⟨4065926044617525014584121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10842469452313400038890989 4065926044617525014584121)
                    ·
                      refine ⟨3049444533463143760938091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065926044617525014584121 3049444533463143760938091)
                      ·
                        rfl

theorem cell23_5938772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_5938772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938772 prefixEnd_5938772 := by exact prefixLift 5938772
  have htrace : WordTrace (prefixWord ++ tailWord_5938772) baseStart_5938772 baseEnd_5938772 := by
    simpa [prefixWord, tailWord_5938772, baseEnd_5938772] using wordTrace_append hprefix tailTrace_5938772
  have hstable : (prefixWord ++ tailWord_5938772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938772).length < 2 ^ (prefixWord ++ tailWord_5938772).sum := by decide
  have hdescent : baseEnd_5938772 < baseStart_5938772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938785 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_5938785 : Nat := 118140960795 + 5938785 * 2 ^ 59
def prefixEnd_5938785 : Nat := 4983230072969 + 3 ^ 40 * 5938785 * 2
def baseEnd_5938785 : Nat := 3049451208711652210075531

theorem tailTrace_5938785 : CollatzResearch.WordTrace tailWord_5938785 prefixEnd_5938785 3049451208711652210075531 := by
  unfold tailWord_5938785
  simp only [CollatzResearch.WordTrace]
  refine ⟨216605283789803683573449809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144403522526535789048966539 216605283789803683573449809)
  ·
    refine ⟨162453962842352762680087357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216605283789803683573449809 162453962842352762680087357)
    ·
      refine ⟨60920236065882286005032759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162453962842352762680087357 60920236065882286005032759)
      ·
        refine ⟨91380354098823429007549139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60920236065882286005032759 91380354098823429007549139)
        ·
          refine ⟨137070531148235143511323709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91380354098823429007549139 137070531148235143511323709)
          ·
            refine ⟨51401449180588178816746391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137070531148235143511323709 51401449180588178816746391)
            ·
              refine ⟨77102173770882268225119587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51401449180588178816746391 77102173770882268225119587)
              ·
                refine ⟨115653260656323402337679381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77102173770882268225119587 115653260656323402337679381)
                ·
                  refine ⟨5421246593265159484578721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115653260656323402337679381 5421246593265159484578721)
                  ·
                    refine ⟨4065934944948869613434041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5421246593265159484578721 4065934944948869613434041)
                    ·
                      refine ⟨3049451208711652210075531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065934944948869613434041 3049451208711652210075531)
                      ·
                        rfl

theorem cell23_5938785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_5938785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938785 prefixEnd_5938785 := by exact prefixLift 5938785
  have htrace : WordTrace (prefixWord ++ tailWord_5938785) baseStart_5938785 baseEnd_5938785 := by
    simpa [prefixWord, tailWord_5938785, baseEnd_5938785] using wordTrace_append hprefix tailTrace_5938785
  have hstable : (prefixWord ++ tailWord_5938785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938785).length < 2 ^ (prefixWord ++ tailWord_5938785).sum := by decide
  have hdescent : baseEnd_5938785 < baseStart_5938785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938788 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_5938788 : Nat := 118140960795 + 5938788 * 2 ^ 59
def prefixEnd_5938788 : Nat := 4983230072969 + 3 ^ 40 * 5938788 * 2
def baseEnd_5938788 : Nat := 3049452749153615698338017

theorem tailTrace_5938788 : CollatzResearch.WordTrace tailWord_5938788 prefixEnd_5938788 3049452749153615698338017 := by
  unfold tailWord_5938788
  simp only [CollatzResearch.WordTrace]
  refine ⟨108302696604396407542904509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144403595472528543390539345 108302696604396407542904509)
  ·
    refine ⟨40613511226648652828589191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108302696604396407542904509 40613511226648652828589191)
    ·
      refine ⟨60920266839972979242883787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40613511226648652828589191 60920266839972979242883787)
      ·
        refine ⟨91380400259959468864325681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60920266839972979242883787 91380400259959468864325681)
        ·
          refine ⟨68535300194969601648244261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91380400259959468864325681 68535300194969601648244261)
          ·
            refine ⟨12850368786556800309045799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68535300194969601648244261 12850368786556800309045799)
            ·
              refine ⟨19275553179835200463568699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850368786556800309045799 19275553179835200463568699)
              ·
                refine ⟨28913329769752800695353049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19275553179835200463568699 28913329769752800695353049)
                ·
                  refine ⟨21684997327314600521514787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28913329769752800695353049 21684997327314600521514787)
                  ·
                    refine ⟨32527495990971900782272181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21684997327314600521514787 32527495990971900782272181)
                    ·
                      refine ⟨3049452749153615698338017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32527495990971900782272181 3049452749153615698338017)
                      ·
                        rfl

theorem cell23_5938788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_5938788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938788 prefixEnd_5938788 := by exact prefixLift 5938788
  have htrace : WordTrace (prefixWord ++ tailWord_5938788) baseStart_5938788 baseEnd_5938788 := by
    simpa [prefixWord, tailWord_5938788, baseEnd_5938788] using wordTrace_append hprefix tailTrace_5938788
  have hstable : (prefixWord ++ tailWord_5938788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938788).length < 2 ^ (prefixWord ++ tailWord_5938788).sum := by decide
  have hdescent : baseEnd_5938788 < baseStart_5938788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938791 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 9]
def baseStart_5938791 : Nat := 118140960795 + 5938791 * 2 ^ 59
def prefixEnd_5938791 : Nat := 4983230072969 + 3 ^ 40 * 5938791 * 2
def baseEnd_5938791 : Nat := 338828254399508798511167

theorem tailTrace_5938791 : CollatzResearch.WordTrace tailWord_5938791 prefixEnd_5938791 338828254399508798511167 := by
  unfold tailWord_5938791
  simp only [CollatzResearch.WordTrace]
  refine ⟨216605502627781946598168227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144403668418521297732112151 216605502627781946598168227)
  ·
    refine ⟨324908253941672919897252341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216605502627781946598168227 324908253941672919897252341)
    ·
      refine ⟨30460148807031836240367407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324908253941672919897252341 30460148807031836240367407)
      ·
        refine ⟨45690223210547754360551111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30460148807031836240367407 45690223210547754360551111)
        ·
          refine ⟨68535334815821631540826667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45690223210547754360551111 68535334815821631540826667)
          ·
            refine ⟨102803002223732447311240001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68535334815821631540826667 102803002223732447311240001)
            ·
              refine ⟨77102251667799335483430001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102803002223732447311240001 77102251667799335483430001)
              ·
                refine ⟨57826688750849501612572501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77102251667799335483430001 57826688750849501612572501)
                ·
                  refine ⟨338828254399508798511167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57826688750849501612572501 338828254399508798511167)
                  ·
                    rfl

theorem cell23_5938791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 9].length) (baseStart_5938791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938791 prefixEnd_5938791 := by exact prefixLift 5938791
  have htrace : WordTrace (prefixWord ++ tailWord_5938791) baseStart_5938791 baseEnd_5938791 := by
    simpa [prefixWord, tailWord_5938791, baseEnd_5938791] using wordTrace_append hprefix tailTrace_5938791
  have hstable : (prefixWord ++ tailWord_5938791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938791).length < 2 ^ (prefixWord ++ tailWord_5938791).sum := by decide
  have hdescent : baseEnd_5938791 < baseStart_5938791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938802 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_5938802 : Nat := 118140960795 + 5938802 * 2 ^ 59
def prefixEnd_5938802 : Nat := 4983230072969 + 3 ^ 40 * 5938802 * 2
def baseEnd_5938802 : Nat := 3049459937882778643562953

theorem tailTrace_5938802 : CollatzResearch.WordTrace tailWord_5938802 prefixEnd_5938802 3049459937882778643562953 := by
  unfold tailWord_5938802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54151475957685523869204665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144403935887161396984545773 54151475957685523869204665)
  ·
    refine ⟨40613606968264142901903499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54151475957685523869204665 40613606968264142901903499)
    ·
      refine ⟨60920410452396214352855249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40613606968264142901903499 60920410452396214352855249)
      ·
        refine ⟨45690307839297160764641437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60920410452396214352855249 45690307839297160764641437)
        ·
          refine ⟨17133865439736435286740539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45690307839297160764641437 17133865439736435286740539)
          ·
            refine ⟨25700798159604652930110809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17133865439736435286740539 25700798159604652930110809)
            ·
              refine ⟨19275598619703489697583107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25700798159604652930110809 19275598619703489697583107)
              ·
                refine ⟨28913397929555234546374661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19275598619703489697583107 28913397929555234546374661)
                ·
                  refine ⟨5421262111791606477445249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28913397929555234546374661 5421262111791606477445249)
                  ·
                    refine ⟨4065946583843704858083937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5421262111791606477445249 4065946583843704858083937)
                    ·
                      refine ⟨3049459937882778643562953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4065946583843704858083937 3049459937882778643562953)
                      ·
                        rfl

theorem cell23_5938802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_5938802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938802 prefixEnd_5938802 := by exact prefixLift 5938802
  have htrace : WordTrace (prefixWord ++ tailWord_5938802) baseStart_5938802 baseEnd_5938802 := by
    simpa [prefixWord, tailWord_5938802, baseEnd_5938802] using wordTrace_append hprefix tailTrace_5938802
  have hstable : (prefixWord ++ tailWord_5938802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938802).length < 2 ^ (prefixWord ++ tailWord_5938802).sum := by decide
  have hdescent : baseEnd_5938802 < baseStart_5938802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938831 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_5938831 : Nat := 118140960795 + 5938831 * 2 ^ 59
def prefixEnd_5938831 : Nat := 4983230072969 + 3 ^ 40 * 5938831 * 2
def baseEnd_5938831 : Nat := 3049474828821759030100319

theorem tailTrace_5938831 : CollatzResearch.WordTrace tailWord_5938831 prefixEnd_5938831 3049474828821759030100319 := by
  unfold tailWord_5938831
  simp only [CollatzResearch.WordTrace]
  refine ⟨216606961547637033429624347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144404641031758022286416231 216606961547637033429624347)
  ·
    refine ⟨324910442321455550144436521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216606961547637033429624347 324910442321455550144436521)
    ·
      refine ⟨243682831741091662608327391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324910442321455550144436521 243682831741091662608327391)
      ·
        refine ⟨365524247611637493912491087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243682831741091662608327391 365524247611637493912491087)
        ·
          refine ⟨548286371417456240868736631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365524247611637493912491087 548286371417456240868736631)
          ·
            refine ⟨822429557126184361303104947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548286371417456240868736631 822429557126184361303104947)
            ·
              refine ⟨1233644335689276541954657421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822429557126184361303104947 1233644335689276541954657421)
              ·
                refine ⟨462616625883478703232996533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1233644335689276541954657421 462616625883478703232996533)
                ·
                  refine ⟨43370308676576128428093425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 462616625883478703232996533 43370308676576128428093425)
                  ·
                    refine ⟨32527731507432096321070069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43370308676576128428093425 32527731507432096321070069)
                    ·
                      refine ⟨3049474828821759030100319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32527731507432096321070069 3049474828821759030100319)
                      ·
                        rfl

theorem cell23_5938831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_5938831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938831 prefixEnd_5938831 := by exact prefixLift 5938831
  have htrace : WordTrace (prefixWord ++ tailWord_5938831) baseStart_5938831 baseEnd_5938831 := by
    simpa [prefixWord, tailWord_5938831, baseEnd_5938831] using wordTrace_append hprefix tailTrace_5938831
  have hstable : (prefixWord ++ tailWord_5938831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938831).length < 2 ^ (prefixWord ++ tailWord_5938831).sum := by decide
  have hdescent : baseEnd_5938831 < baseStart_5938831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938848 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5938848 : Nat := 118140960795 + 5938848 * 2 ^ 59
def prefixEnd_5938848 : Nat := 4983230072969 + 3 ^ 40 * 5938848 * 2
def baseEnd_5938848 : Nat := 3049483557992885463587741

theorem tailTrace_5938848 : CollatzResearch.WordTrace tailWord_5938848 prefixEnd_5938848 3049483557992885463587741 := by
  unfold tailWord_5938848
  simp only [CollatzResearch.WordTrace]
  refine ⟨108303790794287722666496599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144405054392383630221995465 108303790794287722666496599)
  ·
    refine ⟨162455686191431583999744899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108303790794287722666496599 162455686191431583999744899)
    ·
      refine ⟨243683529287147375999617349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162455686191431583999744899 243683529287147375999617349)
      ·
        refine ⟨45690661741340132999928253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243683529287147375999617349 45690661741340132999928253)
        ·
          refine ⟨17133998153002549874973095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45690661741340132999928253 17133998153002549874973095)
          ·
            refine ⟨25700997229503824812459643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17133998153002549874973095 25700997229503824812459643)
            ·
              refine ⟨38551495844255737218689465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25700997229503824812459643 38551495844255737218689465)
              ·
                refine ⟨28913621883191802914017099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38551495844255737218689465 28913621883191802914017099)
                ·
                  refine ⟨43370432824787704371025649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28913621883191802914017099 43370432824787704371025649)
                  ·
                    refine ⟨32527824618590778278269237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43370432824787704371025649 32527824618590778278269237)
                    ·
                      refine ⟨3049483557992885463587741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32527824618590778278269237 3049483557992885463587741)
                      ·
                        rfl

theorem cell23_5938848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5938848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938848 prefixEnd_5938848 := by exact prefixLift 5938848
  have htrace : WordTrace (prefixWord ++ tailWord_5938848) baseStart_5938848 baseEnd_5938848 := by
    simpa [prefixWord, tailWord_5938848, baseEnd_5938848] using wordTrace_append hprefix tailTrace_5938848
  have hstable : (prefixWord ++ tailWord_5938848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938848).length < 2 ^ (prefixWord ++ tailWord_5938848).sum := by decide
  have hdescent : baseEnd_5938848 < baseStart_5938848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938915 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 8]
def baseStart_5938915 : Nat := 118140960795 + 5938915 * 2 ^ 59
def prefixEnd_5938915 : Nat := 4983230072969 + 3 ^ 40 * 5938915 * 2
def baseEnd_5938915 : Nat := 338835329021859633494437

theorem tailTrace_5938915 : CollatzResearch.WordTrace tailWord_5938915 prefixEnd_5938915 338835329021859633494437 := by
  unfold tailWord_5938915
  simp only [CollatzResearch.WordTrace]
  refine ⟨216610025279332715775682199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144406683519555143850454799 216610025279332715775682199)
  ·
    refine ⟨324915037918999073663523299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216610025279332715775682199 324915037918999073663523299)
    ·
      refine ⟨487372556878498610495284949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324915037918999073663523299 487372556878498610495284949)
      ·
        refine ⟨11422794301839811183483241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 487372556878498610495284949 11422794301839811183483241)
        ·
          refine ⟨8567095726379858387612431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11422794301839811183483241 8567095726379858387612431)
          ·
            refine ⟨12850643589569787581418647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567095726379858387612431 12850643589569787581418647)
            ·
              refine ⟨19275965384354681372127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850643589569787581418647 19275965384354681372127971)
              ·
                refine ⟨28913948076532022058191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19275965384354681372127971 28913948076532022058191957)
                ·
                  refine ⟨338835329021859633494437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28913948076532022058191957 338835329021859633494437)
                  ·
                    rfl

theorem cell23_5938915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 8].length) (baseStart_5938915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938915 prefixEnd_5938915 := by exact prefixLift 5938915
  have htrace : WordTrace (prefixWord ++ tailWord_5938915) baseStart_5938915 baseEnd_5938915 := by
    simpa [prefixWord, tailWord_5938915, baseEnd_5938915] using wordTrace_append hprefix tailTrace_5938915
  have hstable : (prefixWord ++ tailWord_5938915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938915).length < 2 ^ (prefixWord ++ tailWord_5938915).sum := by decide
  have hdescent : baseEnd_5938915 < baseStart_5938915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938919 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5938919 : Nat := 118140960795 + 5938919 * 2 ^ 59
def prefixEnd_5938919 : Nat := 4983230072969 + 3 ^ 40 * 5938919 * 2
def baseEnd_5938919 : Nat := 1016506671706451561933305

theorem tailTrace_5938919 : CollatzResearch.WordTrace tailWord_5938919 prefixEnd_5938919 1016506671706451561933305 := by
  unfold tailWord_5938919
  simp only [CollatzResearch.WordTrace]
  refine ⟨216610171171318224458827811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144406780780878816305885207 216610171171318224458827811)
  ·
    refine ⟨324915256756977336688241717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216610171171318224458827811 324915256756977336688241717)
    ·
      refine ⟨30460805320966625314522661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324915256756977336688241717 30460805320966625314522661)
      ·
        refine ⟨5711400997681242246472999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30460805320966625314522661 5711400997681242246472999)
        ·
          refine ⟨8567101496521863369709499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711400997681242246472999 8567101496521863369709499)
          ·
            refine ⟨12850652244782795054564249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567101496521863369709499 12850652244782795054564249)
            ·
              refine ⟨9637989183587096290923187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12850652244782795054564249 9637989183587096290923187)
              ·
                refine ⟨14456983775380644436384781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9637989183587096290923187 14456983775380644436384781)
                ·
                  refine ⟨5421368915767741663644293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14456983775380644436384781 5421368915767741663644293)
                  ·
                    refine ⟨1016506671706451561933305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421368915767741663644293 1016506671706451561933305)
                    ·
                      rfl

theorem cell23_5938919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5938919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938919 prefixEnd_5938919 := by exact prefixLift 5938919
  have htrace : WordTrace (prefixWord ++ tailWord_5938919) baseStart_5938919 baseEnd_5938919 := by
    simpa [prefixWord, tailWord_5938919, baseEnd_5938919] using wordTrace_append hprefix tailTrace_5938919
  have hstable : (prefixWord ++ tailWord_5938919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938919).length < 2 ^ (prefixWord ++ tailWord_5938919).sum := by decide
  have hdescent : baseEnd_5938919 < baseStart_5938919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938928 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_5938928 : Nat := 118140960795 + 5938928 * 2 ^ 59
def prefixEnd_5938928 : Nat := 4983230072969 + 3 ^ 40 * 5938928 * 2
def baseEnd_5938928 : Nat := 1016508212148415050195791

theorem tailTrace_5938928 : CollatzResearch.WordTrace tailWord_5938928 prefixEnd_5938928 1016508212148415050195791 := by
  unfold tailWord_5938928
  simp only [CollatzResearch.WordTrace]
  refine ⟨108305249714142809497952719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144406999618857079330603625 108305249714142809497952719)
  ·
    refine ⟨162457874571214214246929079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108305249714142809497952719 162457874571214214246929079)
    ·
      refine ⟨243686811856821321370393619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162457874571214214246929079 243686811856821321370393619)
      ·
        refine ⟨365530217785231982055590429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243686811856821321370393619 365530217785231982055590429)
        ·
          refine ⟨137073831669461993270846411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365530217785231982055590429 137073831669461993270846411)
          ·
            refine ⟨205610747504192989906269617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137073831669461993270846411 205610747504192989906269617)
            ·
              refine ⟨154208060628144742429702213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205610747504192989906269617 154208060628144742429702213)
              ·
                refine ⟨28914011367777139205569165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154208060628144742429702213 28914011367777139205569165)
                ·
                  refine ⟨10842754262916427202088437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28914011367777139205569165 10842754262916427202088437)
                  ·
                    refine ⟨1016508212148415050195791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10842754262916427202088437 1016508212148415050195791)
                    ·
                      rfl

theorem cell23_5938928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_5938928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938928 prefixEnd_5938928 := by exact prefixLift 5938928
  have htrace : WordTrace (prefixWord ++ tailWord_5938928) baseStart_5938928 baseEnd_5938928 := by
    simpa [prefixWord, tailWord_5938928, baseEnd_5938928] using wordTrace_append hprefix tailTrace_5938928
  have hstable : (prefixWord ++ tailWord_5938928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938928).length < 2 ^ (prefixWord ++ tailWord_5938928).sum := by decide
  have hdescent : baseEnd_5938928 < baseStart_5938928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938935 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_5938935 : Nat := 118140960795 + 5938935 * 2 ^ 59
def prefixEnd_5938935 : Nat := 4983230072969 + 3 ^ 40 * 5938935 * 2
def baseEnd_5938935 : Nat := 3049528230809826623199841

theorem tailTrace_5938935 : CollatzResearch.WordTrace tailWord_5938935 prefixEnd_5938935 3049528230809826623199841 := by
  unfold tailWord_5938935
  simp only [CollatzResearch.WordTrace]
  refine ⟨216610754739260259191410259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144407169826173506127606839 216610754739260259191410259)
  ·
    refine ⟨324916132108890388787115389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216610754739260259191410259 324916132108890388787115389)
    ·
      refine ⟨121843549540833895795168271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324916132108890388787115389 121843549540833895795168271)
      ·
        refine ⟨182765324311250843692752407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121843549540833895795168271 182765324311250843692752407)
        ·
          refine ⟨274147986466876265539128611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182765324311250843692752407 274147986466876265539128611)
          ·
            refine ⟨411221979700314398308692917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274147986466876265539128611 411221979700314398308692917)
            ·
              refine ⟨38552060596904474841439961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411221979700314398308692917 38552060596904474841439961)
              ·
                refine ⟨28914045447678356131079971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38552060596904474841439961 28914045447678356131079971)
                ·
                  refine ⟨43371068171517534196619957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28914045447678356131079971 43371068171517534196619957)
                  ·
                    refine ⟨4066037641079768830933121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43371068171517534196619957 4066037641079768830933121)
                    ·
                      refine ⟨3049528230809826623199841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066037641079768830933121 3049528230809826623199841)
                      ·
                        rfl

theorem cell23_5938935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_5938935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938935 prefixEnd_5938935 := by exact prefixLift 5938935
  have htrace : WordTrace (prefixWord ++ tailWord_5938935) baseStart_5938935 baseEnd_5938935 := by
    simpa [prefixWord, tailWord_5938935, baseEnd_5938935] using wordTrace_append hprefix tailTrace_5938935
  have hstable : (prefixWord ++ tailWord_5938935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938935).length < 2 ^ (prefixWord ++ tailWord_5938935).sum := by decide
  have hdescent : baseEnd_5938935 < baseStart_5938935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938945 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_5938945 : Nat := 118140960795 + 5938945 * 2 ^ 59
def prefixEnd_5938945 : Nat := 4983230072969 + 3 ^ 40 * 5938945 * 2
def baseEnd_5938945 : Nat := 1016511121872123861358265

theorem tailTrace_5938945 : CollatzResearch.WordTrace tailWord_5938945 prefixEnd_5938945 1016511121872123861358265 := by
  unfold tailWord_5938945
  simp only [CollatzResearch.WordTrace]
  refine ⟨216611119469224030899274289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144407412979482687266182859 216611119469224030899274289)
  ·
    refine ⟨162458339601918023174455717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216611119469224030899274289 162458339601918023174455717)
    ·
      refine ⟨30460938675359629345210447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162458339601918023174455717 30460938675359629345210447)
      ·
        refine ⟨45691408013039444017815671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30460938675359629345210447 45691408013039444017815671)
        ·
          refine ⟨68537112019559166026723507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45691408013039444017815671 68537112019559166026723507)
          ·
            refine ⟨102805668029338749040085261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68537112019559166026723507 102805668029338749040085261)
            ·
              refine ⟨38552125511002030890031973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102805668029338749040085261 38552125511002030890031973)
              ·
                refine ⟨7228523533312880791880995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38552125511002030890031973 7228523533312880791880995)
                ·
                  refine ⟨10842785299969321187821493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228523533312880791880995 10842785299969321187821493)
                  ·
                    refine ⟨1016511121872123861358265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10842785299969321187821493 1016511121872123861358265)
                    ·
                      rfl

theorem cell23_5938945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_5938945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938945 prefixEnd_5938945 := by exact prefixLift 5938945
  have htrace : WordTrace (prefixWord ++ tailWord_5938945) baseStart_5938945 baseEnd_5938945 := by
    simpa [prefixWord, tailWord_5938945, baseEnd_5938945] using wordTrace_append hprefix tailTrace_5938945
  have hstable : (prefixWord ++ tailWord_5938945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938945).length < 2 ^ (prefixWord ++ tailWord_5938945).sum := by decide
  have hdescent : baseEnd_5938945 < baseStart_5938945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938952 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_5938952 : Nat := 118140960795 + 5938952 * 2 ^ 59
def prefixEnd_5938952 : Nat := 4983230072969 + 3 ^ 40 * 5938952 * 2
def baseEnd_5938952 : Nat := 3049536959980953056687263

theorem tailTrace_5938952 : CollatzResearch.WordTrace tailWord_5938952 prefixEnd_5938952 3049536959980953056687263 := by
  unfold tailWord_5938952
  simp only [CollatzResearch.WordTrace]
  refine ⟨108305687390099335547389555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144407583186799114063186073 108305687390099335547389555)
  ·
    refine ⟨162458531085149003321084333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108305687390099335547389555 162458531085149003321084333)
    ·
      refine ⟨60921949156930876245406625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162458531085149003321084333 60921949156930876245406625)
      ·
        refine ⟨45691461867698157184054969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60921949156930876245406625 45691461867698157184054969)
        ·
          refine ⟨34268596400773617888041227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45691461867698157184054969 34268596400773617888041227)
          ·
            refine ⟨51402894601160426832061841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34268596400773617888041227 51402894601160426832061841)
            ·
              refine ⟨38552170950870320124046381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51402894601160426832061841 38552170950870320124046381)
              ·
                refine ⟨14457064106576370046517393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38552170950870320124046381 14457064106576370046517393)
                ·
                  refine ⟨10842798079932277534888045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14457064106576370046517393 10842798079932277534888045)
                  ·
                    refine ⟨4066049279974604075583017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10842798079932277534888045 4066049279974604075583017)
                    ·
                      refine ⟨3049536959980953056687263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066049279974604075583017 3049536959980953056687263)
                      ·
                        rfl

theorem cell23_5938952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_5938952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938952 prefixEnd_5938952 := by exact prefixLift 5938952
  have htrace : WordTrace (prefixWord ++ tailWord_5938952) baseStart_5938952 baseEnd_5938952 := by
    simpa [prefixWord, tailWord_5938952, baseEnd_5938952] using wordTrace_append hprefix tailTrace_5938952
  have hstable : (prefixWord ++ tailWord_5938952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938952).length < 2 ^ (prefixWord ++ tailWord_5938952).sum := by decide
  have hdescent : baseEnd_5938952 < baseStart_5938952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938975 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 4, 4]
def baseStart_5938975 : Nat := 118140960795 + 5938975 * 2 ^ 59
def prefixEnd_5938975 : Nat := 4983230072969 + 3 ^ 40 * 5938975 * 2
def baseEnd_5938975 : Nat := 1016516256678668822233219

theorem tailTrace_5938975 : CollatzResearch.WordTrace tailWord_5938975 prefixEnd_5938975 1016516256678668822233219 := by
  unfold tailWord_5938975
  simp only [CollatzResearch.WordTrace]
  refine ⟨216612213659115346022866379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144408142439410230681910919 216612213659115346022866379)
  ·
    refine ⟨324918320488673019034299569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216612213659115346022866379 324918320488673019034299569)
    ·
      refine ⟨243688740366504764275724677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324918320488673019034299569 243688740366504764275724677)
      ·
        refine ⟨45691638818719643301698377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243688740366504764275724677 45691638818719643301698377)
        ·
          refine ⟨34268729114039732476273783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45691638818719643301698377 34268729114039732476273783)
          ·
            refine ⟨51403093671059598714410675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34268729114039732476273783 51403093671059598714410675)
            ·
              refine ⟨77104640506589398071616013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51403093671059598714410675 77104640506589398071616013)
              ·
                refine ⟨28914240189971024276856005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77104640506589398071616013 28914240189971024276856005)
                ·
                  refine ⟨5421420035619567051910501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28914240189971024276856005 5421420035619567051910501)
                  ·
                    refine ⟨1016516256678668822233219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421420035619567051910501 1016516256678668822233219)
                    ·
                      rfl

theorem cell23_5938975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_5938975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938975 prefixEnd_5938975 := by exact prefixLift 5938975
  have htrace : WordTrace (prefixWord ++ tailWord_5938975) baseStart_5938975 baseEnd_5938975 := by
    simpa [prefixWord, tailWord_5938975, baseEnd_5938975] using wordTrace_append hprefix tailTrace_5938975
  have hstable : (prefixWord ++ tailWord_5938975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938975).length < 2 ^ (prefixWord ++ tailWord_5938975).sum := by decide
  have hdescent : baseEnd_5938975 < baseStart_5938975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938976 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5938976 : Nat := 118140960795 + 5938976 * 2 ^ 59
def prefixEnd_5938976 : Nat := 4983230072969 + 3 ^ 40 * 5938976 * 2
def baseEnd_5938976 : Nat := 3049549283516660962787153

theorem tailTrace_5938976 : CollatzResearch.WordTrace tailWord_5938976 prefixEnd_5938976 3049549283516660962787153 := by
  unfold tailWord_5938976
  simp only [CollatzResearch.WordTrace]
  refine ⟨108306125066055861596826391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144408166754741148795768521 108306125066055861596826391)
  ·
    refine ⟨162459187599083792395239587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108306125066055861596826391 162459187599083792395239587)
    ·
      refine ⟨243688781398625688592859381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162459187599083792395239587 243688781398625688592859381)
      ·
        refine ⟨22845823256121158305580567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243688781398625688592859381 22845823256121158305580567)
        ·
          refine ⟨34268734884181737458370851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22845823256121158305580567 34268734884181737458370851)
          ·
            refine ⟨51403102326272606187556277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34268734884181737458370851 51403102326272606187556277)
            ·
              refine ⟨4819040843088056830083401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51403102326272606187556277 4819040843088056830083401)
              ·
                refine ⟨3614280632316042622562551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819040843088056830083401 3614280632316042622562551)
                ·
                  refine ⟨5421420948474063933843827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614280632316042622562551 5421420948474063933843827)
                  ·
                    refine ⟨8132131422711095900765741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5421420948474063933843827 8132131422711095900765741)
                    ·
                      refine ⟨3049549283516660962787153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8132131422711095900765741 3049549283516660962787153)
                      ·
                        rfl

theorem cell23_5938976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5938976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938976 prefixEnd_5938976 := by exact prefixLift 5938976
  have htrace : WordTrace (prefixWord ++ tailWord_5938976) baseStart_5938976 baseEnd_5938976 := by
    simpa [prefixWord, tailWord_5938976, baseEnd_5938976] using wordTrace_append hprefix tailTrace_5938976
  have hstable : (prefixWord ++ tailWord_5938976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938976).length < 2 ^ (prefixWord ++ tailWord_5938976).sum := by decide
  have hdescent : baseEnd_5938976 < baseStart_5938976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5938988 : List Nat := [2, 2, 1, 1, 1, 5, 1, 10]
def baseStart_5938988 : Nat := 118140960795 + 5938988 * 2 ^ 59
def prefixEnd_5938988 : Nat := 4983230072969 + 3 ^ 40 * 5938988 * 2
def baseEnd_5938988 : Nat := 112946497973500552438411

theorem tailTrace_5938988 : CollatzResearch.WordTrace tailWord_5938988 prefixEnd_5938988 112946497973500552438411 := by
  unfold tailWord_5938988
  simp only [CollatzResearch.WordTrace]
  refine ⟨108306343904034124621544809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144408458538712166162059745 108306343904034124621544809)
  ·
    refine ⟨81229757928025593466158607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108306343904034124621544809 81229757928025593466158607)
    ·
      refine ⟨121844636892038390199237911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81229757928025593466158607 121844636892038390199237911)
      ·
        refine ⟨182766955338057585298856867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121844636892038390199237911 182766955338057585298856867)
        ·
          refine ⟨274150433007086377948285301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182766955338057585298856867 274150433007086377948285301)
          ·
            refine ⟨25701603094414347932651747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274150433007086377948285301 25701603094414347932651747)
            ·
              refine ⟨38552404641621521898977621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25701603094414347932651747 38552404641621521898977621)
              ·
                refine ⟨112946497973500552438411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38552404641621521898977621 112946497973500552438411)
                ·
                  rfl

theorem cell23_5938988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 10].length) (baseStart_5938988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5938988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5938988 prefixEnd_5938988 := by exact prefixLift 5938988
  have htrace : WordTrace (prefixWord ++ tailWord_5938988) baseStart_5938988 baseEnd_5938988 := by
    simpa [prefixWord, tailWord_5938988, baseEnd_5938988] using wordTrace_append hprefix tailTrace_5938988
  have hstable : (prefixWord ++ tailWord_5938988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5938988).length < 2 ^ (prefixWord ++ tailWord_5938988).sum := by decide
  have hdescent : baseEnd_5938988 < baseStart_5938988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5938988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939002 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_5939002 : Nat := 118140960795 + 5939002 * 2 ^ 59
def prefixEnd_5939002 : Nat := 4983230072969 + 3 ^ 40 * 5939002 * 2
def baseEnd_5939002 : Nat := 3049562634013677861062033

theorem tailTrace_5939002 : CollatzResearch.WordTrace tailWord_5939002 prefixEnd_5939002 3049562634013677861062033 := by
  unfold tailWord_5939002
  simp only [CollatzResearch.WordTrace]
  refine ⟨54153299607504382408524815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144408798953345019756066173 54153299607504382408524815)
  ·
    refine ⟨81229949411256573612787223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54153299607504382408524815 81229949411256573612787223)
    ·
      refine ⟨121844924116884860419180835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81229949411256573612787223 121844924116884860419180835)
      ·
        refine ⟨182767386175327290628771253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121844924116884860419180835 182767386175327290628771253)
        ·
          refine ⟨17134442453936933496447305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182767386175327290628771253 17134442453936933496447305)
          ·
            refine ⟨12850831840452700122335479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17134442453936933496447305 12850831840452700122335479)
            ·
              refine ⟨19276247760679050183503219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850831840452700122335479 19276247760679050183503219)
              ·
                refine ⟨28914371641018575275254829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19276247760679050183503219 28914371641018575275254829)
                ·
                  refine ⟨10842889365381965728220561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28914371641018575275254829 10842889365381965728220561)
                  ·
                    refine ⟨8132167024036474296165421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10842889365381965728220561 8132167024036474296165421)
                    ·
                      refine ⟨3049562634013677861062033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8132167024036474296165421 3049562634013677861062033)
                      ·
                        rfl

theorem cell23_5939002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_5939002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939002 prefixEnd_5939002 := by exact prefixLift 5939002
  have htrace : WordTrace (prefixWord ++ tailWord_5939002) baseStart_5939002 baseEnd_5939002 := by
    simpa [prefixWord, tailWord_5939002, baseEnd_5939002] using wordTrace_append hprefix tailTrace_5939002
  have hstable : (prefixWord ++ tailWord_5939002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939002).length < 2 ^ (prefixWord ++ tailWord_5939002).sum := by decide
  have hdescent : baseEnd_5939002 < baseStart_5939002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939005 : List Nat := [1, 4, 1, 4, 1, 1, 2, 9]
def baseStart_5939005 : Nat := 118140960795 + 5939005 * 2 ^ 59
def prefixEnd_5939005 : Nat := 4983230072969 + 3 ^ 40 * 5939005 * 2
def baseEnd_5939005 : Nat := 112946821276134864789797

theorem tailTrace_5939005 : CollatzResearch.WordTrace tailWord_5939005 prefixEnd_5939005 112946821276134864789797 := by
  unfold tailWord_5939005
  simp only [CollatzResearch.WordTrace]
  refine ⟨216613307849006661146458469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144408871899337774097638979 216613307849006661146458469)
  ·
    refine ⟨40614995221688748964960963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216613307849006661146458469 40614995221688748964960963)
    ·
      refine ⟨60922492832533123447441445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40614995221688748964960963 60922492832533123447441445)
      ·
        refine ⟨11422967406099960646395271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60922492832533123447441445 11422967406099960646395271)
        ·
          refine ⟨17134451109149940969592907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11422967406099960646395271 17134451109149940969592907)
          ·
            refine ⟨25701676663724911454389361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17134451109149940969592907 25701676663724911454389361)
            ·
              refine ⟨19276257497793683590792021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25701676663724911454389361 19276257497793683590792021)
              ·
                refine ⟨112946821276134864789797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19276257497793683590792021 112946821276134864789797)
                ·
                  rfl

theorem cell23_5939005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 9].length) (baseStart_5939005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939005 prefixEnd_5939005 := by exact prefixLift 5939005
  have htrace : WordTrace (prefixWord ++ tailWord_5939005) baseStart_5939005 baseEnd_5939005 := by
    simpa [prefixWord, tailWord_5939005, baseEnd_5939005] using wordTrace_append hprefix tailTrace_5939005
  have hstable : (prefixWord ++ tailWord_5939005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939005).length < 2 ^ (prefixWord ++ tailWord_5939005).sum := by decide
  have hdescent : baseEnd_5939005 < baseStart_5939005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939015 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_5939015 : Nat := 118140960795 + 5939015 * 2 ^ 59
def prefixEnd_5939015 : Nat := 4983230072969 + 3 ^ 40 * 5939015 * 2
def baseEnd_5939015 : Nat := 3049569309262186310199473

theorem tailTrace_5939015 : CollatzResearch.WordTrace tailWord_5939015 prefixEnd_5939015 3049569309262186310199473 := by
  unfold tailWord_5939015
  simp only [CollatzResearch.WordTrace]
  refine ⟨216613672578970432854322499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144409115052646955236214999 216613672578970432854322499)
  ·
    refine ⟨324920508868455649281483749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216613672578970432854322499 324920508868455649281483749)
    ·
      refine ⟨60922595412835434240278203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324920508868455649281483749 60922595412835434240278203)
      ·
        refine ⟨91383893119253151360417305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60922595412835434240278203 91383893119253151360417305)
        ·
          refine ⟨68537919839439863520312979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91383893119253151360417305 68537919839439863520312979)
          ·
            refine ⟨102806879759159795280469469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68537919839439863520312979 102806879759159795280469469)
            ·
              refine ⟨38552579909684923230176051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102806879759159795280469469 38552579909684923230176051)
              ·
                refine ⟨57828869864527384845264077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38552579909684923230176051 57828869864527384845264077)
                ·
                  refine ⟨21685826199197769316974029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57828869864527384845264077 21685826199197769316974029)
                  ·
                    refine ⟨8132184824699163493865261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21685826199197769316974029 8132184824699163493865261)
                    ·
                      refine ⟨3049569309262186310199473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8132184824699163493865261 3049569309262186310199473)
                      ·
                        rfl

theorem cell23_5939015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_5939015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939015 prefixEnd_5939015 := by exact prefixLift 5939015
  have htrace : WordTrace (prefixWord ++ tailWord_5939015) baseStart_5939015 baseEnd_5939015 := by
    simpa [prefixWord, tailWord_5939015, baseEnd_5939015] using wordTrace_append hprefix tailTrace_5939015
  have hstable : (prefixWord ++ tailWord_5939015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939015).length < 2 ^ (prefixWord ++ tailWord_5939015).sum := by decide
  have hdescent : baseEnd_5939015 < baseStart_5939015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939072 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2]
def baseStart_5939072 : Nat := 118140960795 + 5939072 * 2 ^ 59
def prefixEnd_5939072 : Nat := 4983230072969 + 3 ^ 40 * 5939072 * 2
def baseEnd_5939072 : Nat := 3049598577659492587186711

theorem tailTrace_5939072 : CollatzResearch.WordTrace tailWord_5939072 prefixEnd_5939072 3049598577659492587186711 := by
  unfold tailWord_5939072
  simp only [CollatzResearch.WordTrace]
  refine ⟨108307875769881965794573735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144410501026509287726098313 108307875769881965794573735)
  ·
    refine ⟨162461813654822948691860603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108307875769881965794573735 162461813654822948691860603)
    ·
      refine ⟨243692720482234423037790905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162461813654822948691860603 243692720482234423037790905)
      ·
        refine ⟨182769540361675817278343179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243692720482234423037790905 182769540361675817278343179)
        ·
          refine ⟨274154310542513725917514769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182769540361675817278343179 274154310542513725917514769)
          ·
            refine ⟨205615732906885294438136077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274154310542513725917514769 205615732906885294438136077)
            ·
              refine ⟨77105899840081985414301029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205615732906885294438136077 77105899840081985414301029)
              ·
                refine ⟨14457356220015372265181443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77105899840081985414301029 14457356220015372265181443)
                ·
                  refine ⟨21686034330023058397772165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14457356220015372265181443 21686034330023058397772165)
                  ·
                    refine ⟨4066131436879323449582281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21686034330023058397772165 4066131436879323449582281)
                    ·
                      refine ⟨3049598577659492587186711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066131436879323449582281 3049598577659492587186711)
                      ·
                        rfl

theorem cell23_5939072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_5939072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939072 prefixEnd_5939072 := by exact prefixLift 5939072
  have htrace : WordTrace (prefixWord ++ tailWord_5939072) baseStart_5939072 baseEnd_5939072 := by
    simpa [prefixWord, tailWord_5939072, baseEnd_5939072] using wordTrace_append hprefix tailTrace_5939072
  have hstable : (prefixWord ++ tailWord_5939072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939072).length < 2 ^ (prefixWord ++ tailWord_5939072).sum := by decide
  have hdescent : baseEnd_5939072 < baseStart_5939072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939076 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_5939076 : Nat := 118140960795 + 5939076 * 2 ^ 59
def prefixEnd_5939076 : Nat := 4983230072969 + 3 ^ 40 * 5939076 * 2
def baseEnd_5939076 : Nat := 3049600631582110571536693

theorem tailTrace_5939076 : CollatzResearch.WordTrace tailWord_5939076 prefixEnd_5939076 3049600631582110571536693 := by
  unfold tailWord_5939076
  simp only [CollatzResearch.WordTrace]
  refine ⟨108307948715874720136146541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144410598287832960181528721 108307948715874720136146541)
  ·
    refine ⟨40615480768453020051054953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108307948715874720136146541 40615480768453020051054953)
    ·
      refine ⟨30461610576339765038291215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40615480768453020051054953 30461610576339765038291215)
      ·
        refine ⟨45692415864509647557436823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30461610576339765038291215 45692415864509647557436823)
        ·
          refine ⟨68538623796764471336155235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45692415864509647557436823 68538623796764471336155235)
          ·
            refine ⟨102807935695146707004232853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68538623796764471336155235 102807935695146707004232853)
            ·
              refine ⟨4819121985710001890823415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102807935695146707004232853 4819121985710001890823415)
              ·
                refine ⟨7228682978565002836235123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819121985710001890823415 7228682978565002836235123)
                ·
                  refine ⟨10843024467847504254352685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228682978565002836235123 10843024467847504254352685)
                  ·
                    refine ⟨4066134175442814095382257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10843024467847504254352685 4066134175442814095382257)
                    ·
                      refine ⟨3049600631582110571536693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4066134175442814095382257 3049600631582110571536693)
                      ·
                        rfl

theorem cell23_5939076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_5939076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939076 prefixEnd_5939076 := by exact prefixLift 5939076
  have htrace : WordTrace (prefixWord ++ tailWord_5939076) baseStart_5939076 baseEnd_5939076 := by
    simpa [prefixWord, tailWord_5939076, baseEnd_5939076] using wordTrace_append hprefix tailTrace_5939076
  have hstable : (prefixWord ++ tailWord_5939076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939076).length < 2 ^ (prefixWord ++ tailWord_5939076).sum := by decide
  have hdescent : baseEnd_5939076 < baseStart_5939076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939095 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 7]
def baseStart_5939095 : Nat := 118140960795 + 5939095 * 2 ^ 59
def prefixEnd_5939095 : Nat := 4983230072969 + 3 ^ 40 * 5939095 * 2
def baseEnd_5939095 : Nat := 338845598634949555244345

theorem tailTrace_5939095 : CollatzResearch.WordTrace tailWord_5939095 prefixEnd_5939095 338845598634949555244345 := by
  unfold tailWord_5939095
  simp only [CollatzResearch.WordTrace]
  refine ⟨216616590418680606517234739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144411060279120404344823159 216616590418680606517234739)
  ·
    refine ⟨324924885628020909775852109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216616590418680606517234739 324924885628020909775852109)
    ·
      refine ⟨121846832110507841165944541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324924885628020909775852109 121846832110507841165944541)
      ·
        refine ⟨45692562041440440437229203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121846832110507841165944541 45692562041440440437229203)
        ·
          refine ⟨68538843062160660655843805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45692562041440440437229203 68538843062160660655843805)
          ·
            refine ⟨25702066148310247745941427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68538843062160660655843805 25702066148310247745941427)
            ·
              refine ⟨38553099222465371618912141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25702066148310247745941427 38553099222465371618912141)
              ·
                refine ⟨14457412208424514357092053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38553099222465371618912141 14457412208424514357092053)
                ·
                  refine ⟨338845598634949555244345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14457412208424514357092053 338845598634949555244345)
                  ·
                    rfl

theorem cell23_5939095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 7].length) (baseStart_5939095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939095 prefixEnd_5939095 := by exact prefixLift 5939095
  have htrace : WordTrace (prefixWord ++ tailWord_5939095) baseStart_5939095 baseEnd_5939095 := by
    simpa [prefixWord, tailWord_5939095, baseEnd_5939095] using wordTrace_append hprefix tailTrace_5939095
  have hstable : (prefixWord ++ tailWord_5939095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939095).length < 2 ^ (prefixWord ++ tailWord_5939095).sum := by decide
  have hdescent : baseEnd_5939095 < baseStart_5939095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939135 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_5939135 : Nat := 118140960795 + 5939135 * 2 ^ 59
def prefixEnd_5939135 : Nat := 4983230072969 + 3 ^ 40 * 5939135 * 2
def baseEnd_5939135 : Nat := 3049630926940725840698921

theorem tailTrace_5939135 : CollatzResearch.WordTrace tailWord_5939135 prefixEnd_5939135 3049630926940725840698921 := by
  unfold tailWord_5939135
  simp only [CollatzResearch.WordTrace]
  refine ⟨216618049338535693348690859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144412032892357128899127239 216618049338535693348690859)
  ·
    refine ⟨324927074007803540023036289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216618049338535693348690859 324927074007803540023036289)
    ·
      refine ⟨243695305505852655017277217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324927074007803540023036289 243695305505852655017277217)
      ·
        refine ⟨182771479129389491262957913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243695305505852655017277217 182771479129389491262957913)
        ·
          refine ⟨137078609347042118447218435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182771479129389491262957913 137078609347042118447218435)
          ·
            refine ⟨205617914020563177670827653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137078609347042118447218435 205617914020563177670827653)
            ·
              refine ⟨38553358878855595813280185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205617914020563177670827653 38553358878855595813280185)
              ·
                refine ⟨28915019159141696859960139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38553358878855595813280185 28915019159141696859960139)
                ·
                  refine ⟨43372528738712545289940209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28915019159141696859960139 43372528738712545289940209)
                  ·
                    refine ⟨32529396554034408967455157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43372528738712545289940209 32529396554034408967455157)
                    ·
                      refine ⟨3049630926940725840698921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32529396554034408967455157 3049630926940725840698921)
                      ·
                        rfl

theorem cell23_5939135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_5939135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939135 prefixEnd_5939135 := by exact prefixLift 5939135
  have htrace : WordTrace (prefixWord ++ tailWord_5939135) baseStart_5939135 baseEnd_5939135 := by
    simpa [prefixWord, tailWord_5939135, baseEnd_5939135] using wordTrace_append hprefix tailTrace_5939135
  have hstable : (prefixWord ++ tailWord_5939135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939135).length < 2 ^ (prefixWord ++ tailWord_5939135).sum := by decide
  have hdescent : baseEnd_5939135 < baseStart_5939135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5939172 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_5939172 : Nat := 118140960795 + 5939172 * 2 ^ 59
def prefixEnd_5939172 : Nat := 4983230072969 + 3 ^ 40 * 5939172 * 2
def baseEnd_5939172 : Nat := 1016549975241647398645417

theorem tailTrace_5939172 : CollatzResearch.WordTrace tailWord_5939172 prefixEnd_5939172 1016549975241647398645417 := by
  unfold tailWord_5939172
  simp only [CollatzResearch.WordTrace]
  refine ⟨108309699419700824333893885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144412932559601099111858513 108309699419700824333893885)
  ·
    refine ⟨40616137282387809125210207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108309699419700824333893885 40616137282387809125210207)
    ·
      refine ⟨60924205923581713687815311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40616137282387809125210207 60924205923581713687815311)
      ·
        refine ⟨91386308885372570531722967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60924205923581713687815311 91386308885372570531722967)
        ·
          refine ⟨137079463328058855797584451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91386308885372570531722967 137079463328058855797584451)
          ·
            refine ⟨205619194992088283696376677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137079463328058855797584451 205619194992088283696376677)
            ·
              refine ⟨38553599061016553193070627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205619194992088283696376677 38553599061016553193070627)
              ·
                refine ⟨57830398591524829789605941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38553599061016553193070627 57830398591524829789605941)
                ·
                  refine ⟨5421599867955452792775557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57830398591524829789605941 5421599867955452792775557)
                  ·
                    refine ⟨1016549975241647398645417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5421599867955452792775557 1016549975241647398645417)
                    ·
                      rfl

theorem cell23_5939172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_5939172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5939172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5939172 prefixEnd_5939172 := by exact prefixLift 5939172
  have htrace : WordTrace (prefixWord ++ tailWord_5939172) baseStart_5939172 baseEnd_5939172 := by
    simpa [prefixWord, tailWord_5939172, baseEnd_5939172] using wordTrace_append hprefix tailTrace_5939172
  have hstable : (prefixWord ++ tailWord_5939172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5939172).length < 2 ^ (prefixWord ++ tailWord_5939172).sum := by decide
  have hdescent : baseEnd_5939172 < baseStart_5939172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5939172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
