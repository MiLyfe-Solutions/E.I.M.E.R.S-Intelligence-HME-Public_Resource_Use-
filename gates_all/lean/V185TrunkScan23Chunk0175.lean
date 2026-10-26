import V185TrunkScan23Chunk0174

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1036059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_1036059 : Nat := 118140960795 + 1036059 * 2 ^ 59
def prefixEnd_1036059 : Nat := 4983230072969 + 3 ^ 40 * 1036059 * 2
def baseEnd_1036059 : Nat := 531996253416667148097757

theorem tailTrace_1036059 : CollatzResearch.WordTrace tailWord_1036059 prefixEnd_1036059 531996253416667148097757 := by
  unfold tailWord_1036059
  simp only [CollatzResearch.WordTrace]
  refine ⟨37788176153542662635015231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25192117435695108423343487 37788176153542662635015231)
  ·
    refine ⟨56682264230313993952522847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37788176153542662635015231 56682264230313993952522847)
    ·
      refine ⟨85023396345470990928784271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56682264230313993952522847 85023396345470990928784271)
      ·
        refine ⟨127535094518206486393176407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85023396345470990928784271 127535094518206486393176407)
        ·
          refine ⟨191302641777309729589764611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127535094518206486393176407 191302641777309729589764611)
          ·
            refine ⟨286953962665964594384646917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191302641777309729589764611 286953962665964594384646917)
            ·
              refine ⟨53803867999868361447121297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286953962665964594384646917 53803867999868361447121297)
              ·
                refine ⟨40352900999901271085340973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53803867999868361447121297 40352900999901271085340973)
                ·
                  refine ⟨15132337874962976657002865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40352900999901271085340973 15132337874962976657002865)
                  ·
                    refine ⟨11349253406222232492752149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15132337874962976657002865 11349253406222232492752149)
                    ·
                      refine ⟨531996253416667148097757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11349253406222232492752149 531996253416667148097757)
                      ·
                        rfl

theorem cell23_1036059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_1036059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036059 prefixEnd_1036059 := by exact prefixLift 1036059
  have htrace : WordTrace (prefixWord ++ tailWord_1036059) baseStart_1036059 baseEnd_1036059 := by
    simpa [prefixWord, tailWord_1036059, baseEnd_1036059] using wordTrace_append hprefix tailTrace_1036059
  have hstable : (prefixWord ++ tailWord_1036059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036059).length < 2 ^ (prefixWord ++ tailWord_1036059).sum := by decide
  have hdescent : baseEnd_1036059 < baseStart_1036059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036090 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_1036090 : Nat := 118140960795 + 1036090 * 2 ^ 59
def prefixEnd_1036090 : Nat := 4983230072969 + 3 ^ 40 * 1036090 * 2
def baseEnd_1036090 : Nat := 59112463479661836312235

theorem tailTrace_1036090 : CollatzResearch.WordTrace tailWord_1036090 prefixEnd_1036090 59112463479661836312235 := by
  unfold tailWord_1036090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447326704107588732348431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25192871210953569952929149 9447326704107588732348431)
  ·
    refine ⟨14170990056161383098522647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9447326704107588732348431 14170990056161383098522647)
    ·
      refine ⟨21256485084242074647783971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14170990056161383098522647 21256485084242074647783971)
      ·
        refine ⟨31884727626363111971675957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21256485084242074647783971 31884727626363111971675957)
        ·
          refine ⟨2989193214971541747344621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31884727626363111971675957 2989193214971541747344621)
          ·
            refine ⟨1120947455614328155254233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2989193214971541747344621 1120947455614328155254233)
            ·
              refine ⟨840710591710746116440675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120947455614328155254233 840710591710746116440675)
              ·
                refine ⟨1261065887566119174661013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840710591710746116440675 1261065887566119174661013)
                ·
                  refine ⟨59112463479661836312235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1261065887566119174661013 59112463479661836312235)
                  ·
                    rfl

theorem cell23_1036090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_1036090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036090 prefixEnd_1036090 := by exact prefixLift 1036090
  have htrace : WordTrace (prefixWord ++ tailWord_1036090) baseStart_1036090 baseEnd_1036090 := by
    simpa [prefixWord, tailWord_1036090, baseEnd_1036090] using wordTrace_append hprefix tailTrace_1036090
  have hstable : (prefixWord ++ tailWord_1036090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036090).length < 2 ^ (prefixWord ++ tailWord_1036090).sum := by decide
  have hdescent : baseEnd_1036090 < baseStart_1036090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036103 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 1, 5]
def baseStart_1036103 : Nat := 118140960795 + 1036103 * 2 ^ 59
def prefixEnd_1036103 : Nat := 4983230072969 + 3 ^ 40 * 1036103 * 2
def baseEnd_1036103 : Nat := 177339615521821658649185

theorem tailTrace_1036103 : CollatzResearch.WordTrace tailWord_1036103 prefixEnd_1036103 177339615521821658649185 := by
  unfold tailWord_1036103
  simp only [CollatzResearch.WordTrace]
  refine ⟨37789780965383258149616963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25193187310255505433077975 37789780965383258149616963)
  ·
    refine ⟨56684671448074887224425445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37789780965383258149616963 56684671448074887224425445)
    ·
      refine ⟨10628375896514041354579771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56684671448074887224425445 10628375896514041354579771)
      ·
        refine ⟨15942563844771062031869657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628375896514041354579771 15942563844771062031869657)
        ·
          refine ⟨11956922883578296523902243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15942563844771062031869657 11956922883578296523902243)
          ·
            refine ⟨17935384325367444785853365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956922883578296523902243 17935384325367444785853365)
            ·
              refine ⟨1681442280503197948673753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17935384325367444785853365 1681442280503197948673753)
              ·
                refine ⟨1261081710377398461505315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681442280503197948673753 1261081710377398461505315)
                ·
                  refine ⟨1891622565566097692257973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261081710377398461505315 1891622565566097692257973)
                  ·
                    refine ⟨177339615521821658649185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891622565566097692257973 177339615521821658649185)
                    ·
                      rfl

theorem cell23_1036103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_1036103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036103 prefixEnd_1036103 := by exact prefixLift 1036103
  have htrace : WordTrace (prefixWord ++ tailWord_1036103) baseStart_1036103 baseEnd_1036103 := by
    simpa [prefixWord, tailWord_1036103, baseEnd_1036103] using wordTrace_append hprefix tailTrace_1036103
  have hstable : (prefixWord ++ tailWord_1036103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036103).length < 2 ^ (prefixWord ++ tailWord_1036103).sum := by decide
  have hdescent : baseEnd_1036103 < baseStart_1036103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036153 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_1036153 : Nat := 118140960795 + 1036153 * 2 ^ 59
def prefixEnd_1036153 : Nat := 4983230072969 + 3 ^ 40 * 1036153 * 2
def baseEnd_1036153 : Nat := 532044520598189780322325

theorem tailTrace_1036153 : CollatzResearch.WordTrace tailWord_1036153 prefixEnd_1036153 532044520598189780322325 := by
  unfold tailWord_1036153
  simp only [CollatzResearch.WordTrace]
  refine ⟨37791604615202116688937113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25194403076801411125958075 37791604615202116688937113)
  ·
    refine ⟨28343703461401587516702835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37791604615202116688937113 28343703461401587516702835)
    ·
      refine ⟨42515555192102381275054253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28343703461401587516702835 42515555192102381275054253)
      ·
        refine ⟨15943333197038392978145345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42515555192102381275054253 15943333197038392978145345)
        ·
          refine ⟨11957499897778794733609009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15943333197038392978145345 11957499897778794733609009)
          ·
            refine ⟨8968124923334096050206757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11957499897778794733609009 8968124923334096050206757)
            ·
              refine ⟨1681523423125143009413767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8968124923334096050206757 1681523423125143009413767)
              ·
                refine ⟨2522285134687714514120651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681523423125143009413767 2522285134687714514120651)
                ·
                  refine ⟨3783427702031571771180977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522285134687714514120651 3783427702031571771180977)
                  ·
                    refine ⟨2837570776523678828385733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3783427702031571771180977 2837570776523678828385733)
                    ·
                      refine ⟨532044520598189780322325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2837570776523678828385733 532044520598189780322325)
                      ·
                        rfl

theorem cell23_1036153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_1036153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036153 prefixEnd_1036153 := by exact prefixLift 1036153
  have htrace : WordTrace (prefixWord ++ tailWord_1036153) baseStart_1036153 baseEnd_1036153 := by
    simpa [prefixWord, tailWord_1036153, baseEnd_1036153] using wordTrace_append hprefix tailTrace_1036153
  have hstable : (prefixWord ++ tailWord_1036153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036153).length < 2 ^ (prefixWord ++ tailWord_1036153).sum := by decide
  have hdescent : baseEnd_1036153 < baseStart_1036153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036161 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1036161 : Nat := 118140960795 + 1036161 * 2 ^ 59
def prefixEnd_1036161 : Nat := 4983230072969 + 3 ^ 40 * 1036161 * 2
def baseEnd_1036161 : Nat := 532048628443425749022289

theorem tailTrace_1036161 : CollatzResearch.WordTrace tailWord_1036161 prefixEnd_1036161 532048628443425749022289 := by
  unfold tailWord_1036161
  simp only [CollatzResearch.WordTrace]
  refine ⟨37791896399173134055228337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25194597599448756036818891 37791896399173134055228337)
  ·
    refine ⟨28343922299379850541421253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37791896399173134055228337 28343922299379850541421253)
    ·
      refine ⟨5314485431133721976516485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28343922299379850541421253 5314485431133721976516485)
      ·
        refine ⟨996466018337572870596841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5314485431133721976516485 996466018337572870596841)
        ·
          refine ⟨747349513753179652947631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996466018337572870596841 747349513753179652947631)
          ·
            refine ⟨1121024270629769479421447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747349513753179652947631 1121024270629769479421447)
            ·
              refine ⟨1681536405944654219132171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121024270629769479421447 1681536405944654219132171)
              ·
                refine ⟨2522304608916981328698257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681536405944654219132171 2522304608916981328698257)
                ·
                  refine ⟨1891728456687735996523693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522304608916981328698257 1891728456687735996523693)
                  ·
                    refine ⟨709398171257900998696385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891728456687735996523693 709398171257900998696385)
                    ·
                      refine ⟨532048628443425749022289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709398171257900998696385 532048628443425749022289)
                      ·
                        rfl

theorem cell23_1036161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1036161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036161 prefixEnd_1036161 := by exact prefixLift 1036161
  have htrace : WordTrace (prefixWord ++ tailWord_1036161) baseStart_1036161 baseEnd_1036161 := by
    simpa [prefixWord, tailWord_1036161, baseEnd_1036161] using wordTrace_append hprefix tailTrace_1036161
  have hstable : (prefixWord ++ tailWord_1036161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036161).length < 2 ^ (prefixWord ++ tailWord_1036161).sum := by decide
  have hdescent : baseEnd_1036161 < baseStart_1036161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036163 : List Nat := [1, 1, 1, 3, 4, 3, 3, 7]
def baseStart_1036163 : Nat := 118140960795 + 1036163 * 2 ^ 59
def prefixEnd_1036163 : Nat := 4983230072969 + 3 ^ 40 * 1036163 * 2
def baseEnd_1036163 : Nat := 19705542792767953377677

theorem tailTrace_1036163 : CollatzResearch.WordTrace tailWord_1036163 prefixEnd_1036163 19705542792767953377677 := by
  unfold tailWord_1036163
  simp only [CollatzResearch.WordTrace]
  refine ⟨37791969345165888396801143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25194646230110592264534095 37791969345165888396801143)
  ·
    refine ⟨56687954017748832595201715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37791969345165888396801143 56687954017748832595201715)
    ·
      refine ⟨85031931026623248892802573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56687954017748832595201715 85031931026623248892802573)
      ·
        refine ⟨31886974134983718334800965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85031931026623248892802573 31886974134983718334800965)
        ·
          refine ⟨5978807650309447187775181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31886974134983718334800965 5978807650309447187775181)
          ·
            refine ⟨2242052868866042695415693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5978807650309447187775181 2242052868866042695415693)
            ·
              refine ⟨840769825824766010780885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2242052868866042695415693 840769825824766010780885)
              ·
                refine ⟨19705542792767953377677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 840769825824766010780885 19705542792767953377677)
                ·
                  rfl

theorem cell23_1036163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 7].length) (baseStart_1036163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036163 prefixEnd_1036163 := by exact prefixLift 1036163
  have htrace : WordTrace (prefixWord ++ tailWord_1036163) baseStart_1036163 baseEnd_1036163 := by
    simpa [prefixWord, tailWord_1036163, baseEnd_1036163] using wordTrace_append hprefix tailTrace_1036163
  have hstable : (prefixWord ++ tailWord_1036163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036163).length < 2 ^ (prefixWord ++ tailWord_1036163).sum := by decide
  have hdescent : baseEnd_1036163 < baseStart_1036163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036184 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_1036184 : Nat := 118140960795 + 1036184 * 2 ^ 59
def prefixEnd_1036184 : Nat := 4983230072969 + 3 ^ 40 * 1036184 * 2
def baseEnd_1036184 : Nat := 177353479499493053011561

theorem tailTrace_1036184 : CollatzResearch.WordTrace tailWord_1036184 prefixEnd_1036184 177353479499493053011561 := by
  unfold tailWord_1036184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896367639044904491657803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25195156852059872655543737 18896367639044904491657803)
  ·
    refine ⟨28344551458567356737486705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18896367639044904491657803 28344551458567356737486705)
    ·
      refine ⟨21258413593925517553115029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28344551458567356737486705 21258413593925517553115029)
      ·
        refine ⟨996488137215258635302267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21258413593925517553115029 996488137215258635302267)
        ·
          refine ⟨1494732205822887952953401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996488137215258635302267 1494732205822887952953401)
          ·
            refine ⟨1121049154367165964715051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494732205822887952953401 1121049154367165964715051)
            ·
              refine ⟨1681573731550748947072577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121049154367165964715051 1681573731550748947072577)
              ·
                refine ⟨1261180298663061710304433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681573731550748947072577 1261180298663061710304433)
                ·
                  refine ⟨945885223997296282728325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261180298663061710304433 945885223997296282728325)
                  ·
                    refine ⟨177353479499493053011561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 945885223997296282728325 177353479499493053011561)
                    ·
                      rfl

theorem cell23_1036184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_1036184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036184 prefixEnd_1036184 := by exact prefixLift 1036184
  have htrace : WordTrace (prefixWord ++ tailWord_1036184) baseStart_1036184 baseEnd_1036184 := by
    simpa [prefixWord, tailWord_1036184, baseEnd_1036184] using wordTrace_append hprefix tailTrace_1036184
  have hstable : (prefixWord ++ tailWord_1036184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036184).length < 2 ^ (prefixWord ++ tailWord_1036184).sum := by decide
  have hdescent : baseEnd_1036184 < baseStart_1036184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036207 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 2, 1, 3]
def baseStart_1036207 : Nat := 118140960795 + 1036207 * 2 ^ 59
def prefixEnd_1036207 : Nat := 4983230072969 + 3 ^ 40 * 1036207 * 2
def baseEnd_1036207 : Nat := 532072248553532569047077

theorem tailTrace_1036207 : CollatzResearch.WordTrace tailWord_1036207 prefixEnd_1036207 532072248553532569047077 := by
  unfold tailWord_1036207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793574157006483911402875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25195716104670989274268583 37793574157006483911402875)
  ·
    refine ⟨56690361235509725867104313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37793574157006483911402875 56690361235509725867104313)
    ·
      refine ⟨42517770926632294400328235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56690361235509725867104313 42517770926632294400328235)
      ·
        refine ⟨63776656389948441600492353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42517770926632294400328235 63776656389948441600492353)
        ·
          refine ⟨47832492292461331200369265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63776656389948441600492353 47832492292461331200369265)
          ·
            refine ⟨35874369219345998400276949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47832492292461331200369265 35874369219345998400276949)
            ·
              refine ⟨840805528578421837506491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35874369219345998400276949 840805528578421837506491)
              ·
                refine ⟨1261208292867632756259737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840805528578421837506491 1261208292867632756259737)
                ·
                  refine ⟨945906219650724567194803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261208292867632756259737 945906219650724567194803)
                  ·
                    refine ⟨1418859329476086850792205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 945906219650724567194803 1418859329476086850792205)
                    ·
                      refine ⟨532072248553532569047077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418859329476086850792205 532072248553532569047077)
                      ·
                        rfl

theorem cell23_1036207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 1, 3].length) (baseStart_1036207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036207 prefixEnd_1036207 := by exact prefixLift 1036207
  have htrace : WordTrace (prefixWord ++ tailWord_1036207) baseStart_1036207 baseEnd_1036207 := by
    simpa [prefixWord, tailWord_1036207, baseEnd_1036207] using wordTrace_append hprefix tailTrace_1036207
  have hstable : (prefixWord ++ tailWord_1036207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036207).length < 2 ^ (prefixWord ++ tailWord_1036207).sum := by decide
  have hdescent : baseEnd_1036207 < baseStart_1036207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036217 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1036217 : Nat := 118140960795 + 1036217 * 2 ^ 59
def prefixEnd_1036217 : Nat := 4983230072969 + 3 ^ 40 * 1036217 * 2
def baseEnd_1036217 : Nat := 532077383360077529922031

theorem tailTrace_1036217 : CollatzResearch.WordTrace tailWord_1036217 prefixEnd_1036217 532077383360077529922031 := by
  unfold tailWord_1036217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793938886970255619266905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25195959257980170412844603 37793938886970255619266905)
  ·
    refine ⟨28345454165227691714450179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37793938886970255619266905 28345454165227691714450179)
    ·
      refine ⟨42518181247841537571675269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28345454165227691714450179 42518181247841537571675269)
      ·
        refine ⟨7972158983970288294689113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42518181247841537571675269 7972158983970288294689113)
        ·
          refine ⟨5979119237977716221016835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972158983970288294689113 5979119237977716221016835)
          ·
            refine ⟨8968678856966574331525253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979119237977716221016835 8968678856966574331525253)
            ·
              refine ⟨1681627285681232687160985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8968678856966574331525253 1681627285681232687160985)
              ·
                refine ⟨1261220464260924515370739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681627285681232687160985 1261220464260924515370739)
                ·
                  refine ⟨1891830696391386773056109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261220464260924515370739 1891830696391386773056109)
                  ·
                    refine ⟨709436511146770039896041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1891830696391386773056109 709436511146770039896041)
                    ·
                      refine ⟨532077383360077529922031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709436511146770039896041 532077383360077529922031)
                      ·
                        rfl

theorem cell23_1036217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1036217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036217 prefixEnd_1036217 := by exact prefixLift 1036217
  have htrace : WordTrace (prefixWord ++ tailWord_1036217) baseStart_1036217 baseEnd_1036217 := by
    simpa [prefixWord, tailWord_1036217, baseEnd_1036217] using wordTrace_append hprefix tailTrace_1036217
  have hstable : (prefixWord ++ tailWord_1036217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036217).length < 2 ^ (prefixWord ++ tailWord_1036217).sum := by decide
  have hdescent : baseEnd_1036217 < baseStart_1036217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036247 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_1036247 : Nat := 118140960795 + 1036247 * 2 ^ 59
def prefixEnd_1036247 : Nat := 4983230072969 + 3 ^ 40 * 1036247 * 2
def baseEnd_1036247 : Nat := 532092787779712412546893

theorem tailTrace_1036247 : CollatzResearch.WordTrace tailWord_1036247 prefixEnd_1036247 532092787779712412546893 := by
  unfold tailWord_1036247
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795033076861570742858995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25196688717907713828572663 37795033076861570742858995)
  ·
    refine ⟨56692549615292356114288493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37795033076861570742858995 56692549615292356114288493)
    ·
      refine ⟨21259706105734633542858185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56692549615292356114288493 21259706105734633542858185)
      ·
        refine ⟨15944779579300975157143639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21259706105734633542858185 15944779579300975157143639)
        ·
          refine ⟨23917169368951462735715459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944779579300975157143639 23917169368951462735715459)
          ·
            refine ⟨35875754053427194103573189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23917169368951462735715459 35875754053427194103573189)
            ·
              refine ⟨6726703885017598894419973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35875754053427194103573189 6726703885017598894419973)
              ·
                refine ⟨1261256978440799792703745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6726703885017598894419973 1261256978440799792703745)
                ·
                  refine ⟨945942733830599844527809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261256978440799792703745 945942733830599844527809)
                  ·
                    refine ⟨709457050372949883395857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 945942733830599844527809 709457050372949883395857)
                    ·
                      refine ⟨532092787779712412546893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709457050372949883395857 532092787779712412546893)
                      ·
                        rfl

theorem cell23_1036247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_1036247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036247 prefixEnd_1036247 := by exact prefixLift 1036247
  have htrace : WordTrace (prefixWord ++ tailWord_1036247) baseStart_1036247 baseEnd_1036247 := by
    simpa [prefixWord, tailWord_1036247, baseEnd_1036247] using wordTrace_append hprefix tailTrace_1036247
  have hstable : (prefixWord ++ tailWord_1036247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036247).length < 2 ^ (prefixWord ++ tailWord_1036247).sum := by decide
  have hdescent : baseEnd_1036247 < baseStart_1036247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036258 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1036258 : Nat := 118140960795 + 1036258 * 2 ^ 59
def prefixEnd_1036258 : Nat := 4983230072969 + 3 ^ 40 * 1036258 * 2
def baseEnd_1036258 : Nat := 532098436066911869509343

theorem tailTrace_1036258 : CollatzResearch.WordTrace tailWord_1036258 prefixEnd_1036258 532098436066911869509343 := by
  unfold tailWord_1036258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448858569955429905377357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25196956186547813081006285 9448858569955429905377357)
  ·
    refine ⟨3543321963733286214516509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9448858569955429905377357 3543321963733286214516509)
    ·
      refine ⟨1328745736399982330443691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3543321963733286214516509 1328745736399982330443691)
      ·
        refine ⟨1993118604599973495665537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328745736399982330443691 1993118604599973495665537)
        ·
          refine ⟨1494838953449980121749153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1993118604599973495665537 1494838953449980121749153)
          ·
            refine ⟨1121129215087485091311865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494838953449980121749153 1121129215087485091311865)
            ·
              refine ⟨840846911315613818483899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121129215087485091311865 840846911315613818483899)
              ·
                refine ⟨1261270366973420727725849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840846911315613818483899 1261270366973420727725849)
                ·
                  refine ⟨945952775230065545794387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261270366973420727725849 945952775230065545794387)
                  ·
                    refine ⟨1418929162845098318691581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 945952775230065545794387 1418929162845098318691581)
                    ·
                      refine ⟨532098436066911869509343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1418929162845098318691581 532098436066911869509343)
                      ·
                        rfl

theorem cell23_1036258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1036258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036258 prefixEnd_1036258 := by exact prefixLift 1036258
  have htrace : WordTrace (prefixWord ++ tailWord_1036258) baseStart_1036258 baseEnd_1036258 := by
    simpa [prefixWord, tailWord_1036258, baseEnd_1036258] using wordTrace_append hprefix tailTrace_1036258
  have hstable : (prefixWord ++ tailWord_1036258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036258).length < 2 ^ (prefixWord ++ tailWord_1036258).sum := by decide
  have hdescent : baseEnd_1036258 < baseStart_1036258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036283 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 2, 5]
def baseStart_1036283 : Nat := 118140960795 + 1036283 * 2 ^ 59
def prefixEnd_1036283 : Nat := 4983230072969 + 3 ^ 40 * 1036283 * 2
def baseEnd_1036283 : Nat := 177370424361091423898909

theorem tailTrace_1036283 : CollatzResearch.WordTrace tailWord_1036283 prefixEnd_1036283 177370424361091423898909 := by
  unfold tailWord_1036283
  simp only [CollatzResearch.WordTrace]
  refine ⟨37796346104731148891169503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25197564069820765927446335 37796346104731148891169503)
  ·
    refine ⟨56694519157096723336754255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37796346104731148891169503 56694519157096723336754255)
    ·
      refine ⟨85041778735645085005131383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56694519157096723336754255 85041778735645085005131383)
      ·
        refine ⟨127562668103467627507697075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85041778735645085005131383 127562668103467627507697075)
        ·
          refine ⟨191344002155201441261545613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127562668103467627507697075 191344002155201441261545613)
          ·
            refine ⟨71754000808200540473079605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191344002155201441261545613 71754000808200540473079605)
            ·
              refine ⟨6726937575768800669351213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71754000808200540473079605 6726937575768800669351213)
              ·
                refine ⟨2522601590913300251006705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726937575768800669351213 2522601590913300251006705)
                ·
                  refine ⟨1891951193184975188255029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522601590913300251006705 1891951193184975188255029)
                  ·
                    refine ⟨177370424361091423898909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1891951193184975188255029 177370424361091423898909)
                    ·
                      rfl

theorem cell23_1036283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 5].length) (baseStart_1036283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036283 prefixEnd_1036283 := by exact prefixLift 1036283
  have htrace : WordTrace (prefixWord ++ tailWord_1036283) baseStart_1036283 baseEnd_1036283 := by
    simpa [prefixWord, tailWord_1036283, baseEnd_1036283] using wordTrace_append hprefix tailTrace_1036283
  have hstable : (prefixWord ++ tailWord_1036283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036283).length < 2 ^ (prefixWord ++ tailWord_1036283).sum := by decide
  have hdescent : baseEnd_1036283 < baseStart_1036283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036293 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_1036293 : Nat := 118140960795 + 1036293 * 2 ^ 59
def prefixEnd_1036293 : Nat := 4983230072969 + 3 ^ 40 * 1036293 * 2
def baseEnd_1036293 : Nat := 532116407889819232571681

theorem tailTrace_1036293 : CollatzResearch.WordTrace tailWord_1036293 prefixEnd_1036293 532116407889819232571681 := by
  unfold tailWord_1036293
  simp only [CollatzResearch.WordTrace]
  refine ⟨37796710834694920599033533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25197807223129947066022355 37796710834694920599033533)
  ·
    refine ⟨14173766563010595224637575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37796710834694920599033533 14173766563010595224637575)
    ·
      refine ⟨21260649844515892836956363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14173766563010595224637575 21260649844515892836956363)
      ·
        refine ⟨31890974766773839255434545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21260649844515892836956363 31890974766773839255434545)
        ·
          refine ⟨23918231075080379441575909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31890974766773839255434545 23918231075080379441575909)
          ·
            refine ⟨4484668326577571145295483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23918231075080379441575909 4484668326577571145295483)
            ·
              refine ⟨6727002489866356717943225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484668326577571145295483 6727002489866356717943225)
              ·
                refine ⟨5045251867399767538457419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727002489866356717943225 5045251867399767538457419)
                ·
                  refine ⟨7567877801099651307686129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045251867399767538457419 7567877801099651307686129)
                  ·
                    refine ⟨5675908350824738480764597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567877801099651307686129 5675908350824738480764597)
                    ·
                      refine ⟨532116407889819232571681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5675908350824738480764597 532116407889819232571681)
                      ·
                        rfl

theorem cell23_1036293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_1036293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036293 prefixEnd_1036293 := by exact prefixLift 1036293
  have htrace : WordTrace (prefixWord ++ tailWord_1036293) baseStart_1036293 baseEnd_1036293 := by
    simpa [prefixWord, tailWord_1036293, baseEnd_1036293] using wordTrace_append hprefix tailTrace_1036293
  have hstable : (prefixWord ++ tailWord_1036293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036293).length < 2 ^ (prefixWord ++ tailWord_1036293).sum := by decide
  have hdescent : baseEnd_1036293 < baseStart_1036293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036337 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1036337 : Nat := 118140960795 + 1036337 * 2 ^ 59
def prefixEnd_1036337 : Nat := 4983230072969 + 3 ^ 40 * 1036337 * 2
def baseEnd_1036337 : Nat := 532139001038617060421479

theorem tailTrace_1036337 : CollatzResearch.WordTrace tailWord_1036337 prefixEnd_1036337 532139001038617060421479 := by
  unfold tailWord_1036337
  simp only [CollatzResearch.WordTrace]
  refine ⟨37798315646535516113635265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25198877097690344075756843 37798315646535516113635265)
  ·
    refine ⟨28348736734901637085226449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37798315646535516113635265 28348736734901637085226449)
    ·
      refine ⟨21261552551176227813919837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28348736734901637085226449 21261552551176227813919837)
      ·
        refine ⟨7973082206691085430219939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21261552551176227813919837 7973082206691085430219939)
        ·
          refine ⟨11959623310036628145329909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973082206691085430219939 11959623310036628145329909)
          ·
            refine ⟨1121214685315933888624679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11959623310036628145329909 1121214685315933888624679)
            ·
              refine ⟨1681822027973900832937019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121214685315933888624679 1681822027973900832937019)
              ·
                refine ⟨2522733041960851249405529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681822027973900832937019 2522733041960851249405529)
                ·
                  refine ⟨1892049781470638437054147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522733041960851249405529 1892049781470638437054147)
                  ·
                    refine ⟨2838074672205957655581221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892049781470638437054147 2838074672205957655581221)
                    ·
                      refine ⟨532139001038617060421479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2838074672205957655581221 532139001038617060421479)
                      ·
                        rfl

theorem cell23_1036337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1036337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036337 prefixEnd_1036337 := by exact prefixLift 1036337
  have htrace : WordTrace (prefixWord ++ tailWord_1036337) baseStart_1036337 baseEnd_1036337 := by
    simpa [prefixWord, tailWord_1036337, baseEnd_1036337] using wordTrace_append hprefix tailTrace_1036337
  have hstable : (prefixWord ++ tailWord_1036337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036337).length < 2 ^ (prefixWord ++ tailWord_1036337).sum := by decide
  have hdescent : baseEnd_1036337 < baseStart_1036337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036374 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1036374 : Nat := 118140960795 + 1036374 * 2 ^ 59
def prefixEnd_1036374 : Nat := 4983230072969 + 3 ^ 40 * 1036374 * 2
def baseEnd_1036374 : Nat := 532157999822833415658809

theorem tailTrace_1036374 : CollatzResearch.WordTrace tailWord_1036374 prefixEnd_1036374 532157999822833415658809 := by
  unfold tailWord_1036374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362479071712591964545761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25199776764934314288488117 2362479071712591964545761)
  ·
    refine ⟨1771859303784443973409321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2362479071712591964545761 1771859303784443973409321)
    ·
      refine ⟨1328894477838332980056991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771859303784443973409321 1328894477838332980056991)
      ·
        refine ⟨1993341716757499470085487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328894477838332980056991 1993341716757499470085487)
        ·
          refine ⟨2990012575136249205128231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993341716757499470085487 2990012575136249205128231)
          ·
            refine ⟨4485018862704373807692347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990012575136249205128231 4485018862704373807692347)
            ·
              refine ⟨6727528294056560711538521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485018862704373807692347 6727528294056560711538521)
              ·
                refine ⟨5045646220542420533653891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727528294056560711538521 5045646220542420533653891)
                ·
                  refine ⟨7568469330813630800480837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045646220542420533653891 7568469330813630800480837)
                  ·
                    refine ⟨1419087999527555775090157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568469330813630800480837 1419087999527555775090157)
                    ·
                      refine ⟨532157999822833415658809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419087999527555775090157 532157999822833415658809)
                      ·
                        rfl

theorem cell23_1036374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1036374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036374 prefixEnd_1036374 := by exact prefixLift 1036374
  have htrace : WordTrace (prefixWord ++ tailWord_1036374) baseStart_1036374 baseEnd_1036374 := by
    simpa [prefixWord, tailWord_1036374, baseEnd_1036374] using wordTrace_append hprefix tailTrace_1036374
  have hstable : (prefixWord ++ tailWord_1036374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036374).length < 2 ^ (prefixWord ++ tailWord_1036374).sum := by decide
  have hdescent : baseEnd_1036374 < baseStart_1036374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036387 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 3]
def baseStart_1036387 : Nat := 118140960795 + 1036387 * 2 ^ 59
def prefixEnd_1036387 : Nat := 4983230072969 + 3 ^ 40 * 1036387 * 2
def baseEnd_1036387 : Nat := 532164675071341864796249

theorem tailTrace_1036387 : CollatzResearch.WordTrace tailWord_1036387 prefixEnd_1036387 532164675071341864796249 := by
  unfold tailWord_1036387
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800139296354374652955415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25200092864236249768636943 37800139296354374652955415)
  ·
    refine ⟨56700208944531561979433123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37800139296354374652955415 56700208944531561979433123)
    ·
      refine ⟨85050313416797342969149685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56700208944531561979433123 85050313416797342969149685)
      ·
        refine ⟨7973466882824750903357783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85050313416797342969149685 7973466882824750903357783)
        ·
          refine ⟨11960200324237126355036675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973466882824750903357783 11960200324237126355036675)
          ·
            refine ⟨17940300486355689532555013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11960200324237126355036675 17940300486355689532555013)
            ·
              refine ⟨3363806341191691787354065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17940300486355689532555013 3363806341191691787354065)
              ·
                refine ⟨2522854755893768840515549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363806341191691787354065 2522854755893768840515549)
                ·
                  refine ⟨946070533460163315193331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2522854755893768840515549 946070533460163315193331)
                  ·
                    refine ⟨1419105800190244972789997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946070533460163315193331 1419105800190244972789997)
                    ·
                      refine ⟨532164675071341864796249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419105800190244972789997 532164675071341864796249)
                      ·
                        rfl

theorem cell23_1036387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_1036387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036387 prefixEnd_1036387 := by exact prefixLift 1036387
  have htrace : WordTrace (prefixWord ++ tailWord_1036387) baseStart_1036387 baseEnd_1036387 := by
    simpa [prefixWord, tailWord_1036387, baseEnd_1036387] using wordTrace_append hprefix tailTrace_1036387
  have hstable : (prefixWord ++ tailWord_1036387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036387).length < 2 ^ (prefixWord ++ tailWord_1036387).sum := by decide
  have hdescent : baseEnd_1036387 < baseStart_1036387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036397 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1036397 : Nat := 118140960795 + 1036397 * 2 ^ 59
def prefixEnd_1036397 : Nat := 4983230072969 + 3 ^ 40 * 1036397 * 2
def baseEnd_1036397 : Nat := 532169809877886825671203

theorem tailTrace_1036397 : CollatzResearch.WordTrace tailWord_1036397 prefixEnd_1036397 532169809877886825671203 := by
  unfold tailWord_1036397
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800504026318146360819445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25200336017545430907212963 37800504026318146360819445)
  ·
    refine ⟨3543797252467326221326823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37800504026318146360819445 3543797252467326221326823)
    ·
      refine ⟨5315695878700989331990235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543797252467326221326823 5315695878700989331990235)
      ·
        refine ⟨7973543818051483997985353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315695878700989331990235 7973543818051483997985353)
        ·
          refine ⟨5980157863538612998489015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7973543818051483997985353 5980157863538612998489015)
          ·
            refine ⟨8970236795307919497733523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980157863538612998489015 8970236795307919497733523)
            ·
              refine ⟨13455355192961879246600285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8970236795307919497733523 13455355192961879246600285)
              ·
                refine ⟨5045758197360704717475107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13455355192961879246600285 5045758197360704717475107)
                ·
                  refine ⟨7568637296041057076212661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045758197360704717475107 7568637296041057076212661)
                  ·
                    refine ⟨709559746503849100894937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7568637296041057076212661 709559746503849100894937)
                    ·
                      refine ⟨532169809877886825671203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709559746503849100894937 532169809877886825671203)
                      ·
                        rfl

theorem cell23_1036397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1036397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036397 prefixEnd_1036397 := by exact prefixLift 1036397
  have htrace : WordTrace (prefixWord ++ tailWord_1036397) baseStart_1036397 baseEnd_1036397 := by
    simpa [prefixWord, tailWord_1036397, baseEnd_1036397] using wordTrace_append hprefix tailTrace_1036397
  have hstable : (prefixWord ++ tailWord_1036397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036397).length < 2 ^ (prefixWord ++ tailWord_1036397).sum := by decide
  have hdescent : baseEnd_1036397 < baseStart_1036397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036437 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1036437 : Nat := 118140960795 + 1036437 * 2 ^ 59
def prefixEnd_1036437 : Nat := 4983230072969 + 3 ^ 40 * 1036437 * 2
def baseEnd_1036437 : Nat := 177396783034688889723673

theorem tailTrace_1036437 : CollatzResearch.WordTrace tailWord_1036437 prefixEnd_1036437 177396783034688889723673 := by
  unfold tailWord_1036437
  simp only [CollatzResearch.WordTrace]
  refine ⟨37801962946173233192275565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25201308630782155461517043 37801962946173233192275565)
  ·
    refine ⟨14175736104814962447103337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37801962946173233192275565 14175736104814962447103337)
    ·
      refine ⟨10631802078611221835327503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14175736104814962447103337 10631802078611221835327503)
      ·
        refine ⟨15947703117916832752991255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631802078611221835327503 15947703117916832752991255)
        ·
          refine ⟨23921554676875249129486883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15947703117916832752991255 23921554676875249129486883)
          ·
            refine ⟨35882332015312873694230325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23921554676875249129486883 35882332015312873694230325)
            ·
              refine ⟨3363968626435581908834093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35882332015312873694230325 3363968626435581908834093)
              ·
                refine ⟨1261488234913343215812785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3363968626435581908834093 1261488234913343215812785)
                ·
                  refine ⟨946116176185007411859589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261488234913343215812785 946116176185007411859589)
                  ·
                    refine ⟨177396783034688889723673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946116176185007411859589 177396783034688889723673)
                    ·
                      rfl

theorem cell23_1036437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1036437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036437 prefixEnd_1036437 := by exact prefixLift 1036437
  have htrace : WordTrace (prefixWord ++ tailWord_1036437) baseStart_1036437 baseEnd_1036437 := by
    simpa [prefixWord, tailWord_1036437, baseEnd_1036437] using wordTrace_append hprefix tailTrace_1036437
  have hstable : (prefixWord ++ tailWord_1036437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036437).length < 2 ^ (prefixWord ++ tailWord_1036437).sum := by decide
  have hdescent : baseEnd_1036437 < baseStart_1036437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036443 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_1036443 : Nat := 118140960795 + 1036443 * 2 ^ 59
def prefixEnd_1036443 : Nat := 4983230072969 + 3 ^ 40 * 1036443 * 2
def baseEnd_1036443 : Nat := 532193429987993645695991

theorem tailTrace_1036443 : CollatzResearch.WordTrace tailWord_1036443 prefixEnd_1036443 532193429987993645695991 := by
  unfold tailWord_1036443
  simp only [CollatzResearch.WordTrace]
  refine ⟨37802181784151496216993983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25201454522767664144662655 37802181784151496216993983)
  ·
    refine ⟨56703272676227244325490975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37802181784151496216993983 56703272676227244325490975)
    ·
      refine ⟨85054909014340866488236463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56703272676227244325490975 85054909014340866488236463)
      ·
        refine ⟨127582363521511299732354695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85054909014340866488236463 127582363521511299732354695)
        ·
          refine ⟨191373545282266949598532043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127582363521511299732354695 191373545282266949598532043)
          ·
            refine ⟨287060317923400424397798065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191373545282266949598532043 287060317923400424397798065)
            ·
              refine ⟨215295238442550318298348549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287060317923400424397798065 215295238442550318298348549)
              ·
                refine ⟨40367857207978184680940353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215295238442550318298348549 40367857207978184680940353)
                ·
                  refine ⟨30275892905983638510705265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40367857207978184680940353 30275892905983638510705265)
                  ·
                    refine ⟨22706919679487728883028949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30275892905983638510705265 22706919679487728883028949)
                    ·
                      refine ⟨532193429987993645695991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22706919679487728883028949 532193429987993645695991)
                      ·
                        rfl

theorem cell23_1036443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_1036443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036443 prefixEnd_1036443 := by exact prefixLift 1036443
  have htrace : WordTrace (prefixWord ++ tailWord_1036443) baseStart_1036443 baseEnd_1036443 := by
    simpa [prefixWord, tailWord_1036443, baseEnd_1036443] using wordTrace_append hprefix tailTrace_1036443
  have hstable : (prefixWord ++ tailWord_1036443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036443).length < 2 ^ (prefixWord ++ tailWord_1036443).sum := by decide
  have hdescent : baseEnd_1036443 < baseStart_1036443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036444 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1036444 : Nat := 118140960795 + 1036444 * 2 ^ 59
def prefixEnd_1036444 : Nat := 4983230072969 + 3 ^ 40 * 1036444 * 2
def baseEnd_1036444 : Nat := 532193943468648141783487

theorem tailTrace_1036444 : CollatzResearch.WordTrace tailWord_1036444 prefixEnd_1036444 532193943468648141783487 := by
  unfold tailWord_1036444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901109128573936693890193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25201478838098582258520257 18901109128573936693890193)
  ·
    refine ⟨14175831846430452520417645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18901109128573936693890193 14175831846430452520417645)
    ·
      refine ⟨5315936942411419695156617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14175831846430452520417645 5315936942411419695156617)
      ·
        refine ⟨3986952706808564771367463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5315936942411419695156617 3986952706808564771367463)
        ·
          refine ⟨5980429060212847157051195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986952706808564771367463 5980429060212847157051195)
          ·
            refine ⟨8970643590319270735576793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980429060212847157051195 8970643590319270735576793)
            ·
              refine ⟨6727982692739453051682595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970643590319270735576793 6727982692739453051682595)
              ·
                refine ⟨10091974039109179577523893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727982692739453051682595 10091974039109179577523893)
                ·
                  refine ⟨946122566166485585392865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10091974039109179577523893 946122566166485585392865)
                  ·
                    refine ⟨709591924624864189044649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946122566166485585392865 709591924624864189044649)
                    ·
                      refine ⟨532193943468648141783487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709591924624864189044649 532193943468648141783487)
                      ·
                        rfl

theorem cell23_1036444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1036444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036444 prefixEnd_1036444 := by exact prefixLift 1036444
  have htrace : WordTrace (prefixWord ++ tailWord_1036444) baseStart_1036444 baseEnd_1036444 := by
    simpa [prefixWord, tailWord_1036444, baseEnd_1036444] using wordTrace_append hprefix tailTrace_1036444
  have hstable : (prefixWord ++ tailWord_1036444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036444).length < 2 ^ (prefixWord ++ tailWord_1036444).sum := by decide
  have hdescent : baseEnd_1036444 < baseStart_1036444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036461 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1036461 : Nat := 118140960795 + 1036461 * 2 ^ 59
def prefixEnd_1036461 : Nat := 4983230072969 + 3 ^ 40 * 1036461 * 2
def baseEnd_1036461 : Nat := 532202672639774575270909

theorem tailTrace_1036461 : CollatzResearch.WordTrace tailWord_1036461 prefixEnd_1036461 532202672639774575270909 := by
  unfold tailWord_1036461
  simp only [CollatzResearch.WordTrace]
  refine ⟨37802838298086285291149237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25201892198724190194099491 37802838298086285291149237)
  ·
    refine ⟨3544016090445589246045241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37802838298086285291149237 3544016090445589246045241)
    ·
      refine ⟨2658012067834191934533931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3544016090445589246045241 2658012067834191934533931)
      ·
        refine ⟨3987018101751287901800897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658012067834191934533931 3987018101751287901800897)
        ·
          refine ⟨2990263576313465926350673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3987018101751287901800897 2990263576313465926350673)
          ·
            refine ⟨2242697682235099444763005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990263576313465926350673 2242697682235099444763005)
            ·
              refine ⟨841011630838162291786127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2242697682235099444763005 841011630838162291786127)
              ·
                refine ⟨1261517446257243437679191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841011630838162291786127 1261517446257243437679191)
                ·
                  refine ⟨1892276169385865156518787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261517446257243437679191 1892276169385865156518787)
                  ·
                    refine ⟨2838414254078797734778181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892276169385865156518787 2838414254078797734778181)
                    ·
                      refine ⟨532202672639774575270909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2838414254078797734778181 532202672639774575270909)
                      ·
                        rfl

theorem cell23_1036461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1036461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036461 prefixEnd_1036461 := by exact prefixLift 1036461
  have htrace : WordTrace (prefixWord ++ tailWord_1036461) baseStart_1036461 baseEnd_1036461 := by
    simpa [prefixWord, tailWord_1036461, baseEnd_1036461] using wordTrace_append hprefix tailTrace_1036461
  have hstable : (prefixWord ++ tailWord_1036461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036461).length < 2 ^ (prefixWord ++ tailWord_1036461).sum := by decide
  have hdescent : baseEnd_1036461 < baseStart_1036461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036480 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_1036480 : Nat := 118140960795 + 1036480 * 2 ^ 59
def prefixEnd_1036480 : Nat := 4983230072969 + 3 ^ 40 * 1036480 * 2
def baseEnd_1036480 : Nat := 177404142924070000311107

theorem tailTrace_1036480 : CollatzResearch.WordTrace tailWord_1036480 prefixEnd_1036480 177404142924070000311107 := by
  unfold tailWord_1036480
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901765642508725768045447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25202354190011634357393929 18901765642508725768045447)
  ·
    refine ⟨28352648463763088652068171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18901765642508725768045447 28352648463763088652068171)
    ·
      refine ⟨42528972695644632978102257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28352648463763088652068171 42528972695644632978102257)
      ·
        refine ⟨31896729521733474733576693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42528972695644632978102257 31896729521733474733576693)
        ·
          refine ⟨2990318392662513256272815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31896729521733474733576693 2990318392662513256272815)
          ·
            refine ⟨4485477588993769884409223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990318392662513256272815 4485477588993769884409223)
            ·
              refine ⟨6728216383490654826613835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485477588993769884409223 6728216383490654826613835)
              ·
                refine ⟨10092324575235982239920753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728216383490654826613835 10092324575235982239920753)
                ·
                  refine ⟨7569243431426986679940565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092324575235982239920753 7569243431426986679940565)
                  ·
                    refine ⟨177404142924070000311107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7569243431426986679940565 177404142924070000311107)
                    ·
                      rfl

theorem cell23_1036480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_1036480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036480 prefixEnd_1036480 := by exact prefixLift 1036480
  have htrace : WordTrace (prefixWord ++ tailWord_1036480) baseStart_1036480 baseEnd_1036480 := by
    simpa [prefixWord, tailWord_1036480, baseEnd_1036480] using wordTrace_append hprefix tailTrace_1036480
  have hstable : (prefixWord ++ tailWord_1036480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036480).length < 2 ^ (prefixWord ++ tailWord_1036480).sum := by decide
  have hdescent : baseEnd_1036480 < baseStart_1036480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036494 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_1036494 : Nat := 118140960795 + 1036494 * 2 ^ 59
def prefixEnd_1036494 : Nat := 4983230072969 + 3 ^ 40 * 1036494 * 2
def baseEnd_1036494 : Nat := 532219617501372946158257

theorem tailTrace_1036494 : CollatzResearch.WordTrace tailWord_1036494 prefixEnd_1036494 532219617501372946158257 := by
  unfold tailWord_1036494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725505238370841490887567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25202694604644487951400357 4725505238370841490887567)
  ·
    refine ⟨7088257857556262236331351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725505238370841490887567 7088257857556262236331351)
    ·
      refine ⟨10632386786334393354497027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088257857556262236331351 10632386786334393354497027)
      ·
        refine ⟨15948580179501590031745541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632386786334393354497027 15948580179501590031745541)
        ·
          refine ⟨2990358783656548130952289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15948580179501590031745541 2990358783656548130952289)
          ·
            refine ⟨2242769087742411098214217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990358783656548130952289 2242769087742411098214217)
            ·
              refine ⟨1682076815806808323660663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242769087742411098214217 1682076815806808323660663)
              ·
                refine ⟨2523115223710212485490995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682076815806808323660663 2523115223710212485490995)
                ·
                  refine ⟨3784672835565318728236493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523115223710212485490995 3784672835565318728236493)
                  ·
                    refine ⟨1419252313336994523088685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784672835565318728236493 1419252313336994523088685)
                    ·
                      refine ⟨532219617501372946158257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419252313336994523088685 532219617501372946158257)
                      ·
                        rfl

theorem cell23_1036494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_1036494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036494 prefixEnd_1036494 := by exact prefixLift 1036494
  have htrace : WordTrace (prefixWord ++ tailWord_1036494) baseStart_1036494 baseEnd_1036494 := by
    simpa [prefixWord, tailWord_1036494, baseEnd_1036494] using wordTrace_append hprefix tailTrace_1036494
  have hstable : (prefixWord ++ tailWord_1036494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036494).length < 2 ^ (prefixWord ++ tailWord_1036494).sum := by decide
  have hdescent : baseEnd_1036494 < baseStart_1036494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036504 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_1036504 : Nat := 118140960795 + 1036504 * 2 ^ 59
def prefixEnd_1036504 : Nat := 4983230072969 + 3 ^ 40 * 1036504 * 2
def baseEnd_1036504 : Nat := 532224752307917907033211

theorem tailTrace_1036504 : CollatzResearch.WordTrace tailWord_1036504 prefixEnd_1036504 532224752307917907033211 := by
  unfold tailWord_1036504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18902203318465251817482283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25202937757953669089976377 18902203318465251817482283)
  ·
    refine ⟨28353304977697877726223425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18902203318465251817482283 28353304977697877726223425)
    ·
      refine ⟨21264978733273408294667569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28353304977697877726223425 21264978733273408294667569)
      ·
        refine ⟨15948734049955056221000677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21264978733273408294667569 15948734049955056221000677)
        ·
          refine ⟨2990387634366573041437627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15948734049955056221000677 2990387634366573041437627)
          ·
            refine ⟨4485581451549859562156441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990387634366573041437627 4485581451549859562156441)
            ·
              refine ⟨3364186088662394671617331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485581451549859562156441 3364186088662394671617331)
              ·
                refine ⟨5046279132993592007425997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364186088662394671617331 5046279132993592007425997)
                ·
                  refine ⟨1892354674872597002784749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5046279132993592007425997 1892354674872597002784749)
                  ·
                    refine ⟨709633003077223876044281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1892354674872597002784749 709633003077223876044281)
                    ·
                      refine ⟨532224752307917907033211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709633003077223876044281 532224752307917907033211)
                      ·
                        rfl

theorem cell23_1036504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_1036504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036504 prefixEnd_1036504 := by exact prefixLift 1036504
  have htrace : WordTrace (prefixWord ++ tailWord_1036504) baseStart_1036504 baseEnd_1036504 := by
    simpa [prefixWord, tailWord_1036504, baseEnd_1036504] using wordTrace_append hprefix tailTrace_1036504
  have hstable : (prefixWord ++ tailWord_1036504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036504).length < 2 ^ (prefixWord ++ tailWord_1036504).sum := by decide
  have hdescent : baseEnd_1036504 < baseStart_1036504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036515 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1036515 : Nat := 118140960795 + 1036515 * 2 ^ 59
def prefixEnd_1036515 : Nat := 4983230072969 + 3 ^ 40 * 1036515 * 2
def baseEnd_1036515 : Nat := 532230400595117363995661

theorem tailTrace_1036515 : CollatzResearch.WordTrace tailWord_1036515 prefixEnd_1036515 532230400595117363995661 := by
  unfold tailWord_1036515
  simp only [CollatzResearch.WordTrace]
  refine ⟨37804807839890652513614999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25203205226593768342409999 37804807839890652513614999)
  ·
    refine ⟨56707211759835978770422499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37804807839890652513614999 56707211759835978770422499)
    ·
      refine ⟨85060817639753968155633749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56707211759835978770422499 85060817639753968155633749)
      ·
        refine ⟨996806456715866814323833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 85060817639753968155633749 996806456715866814323833)
        ·
          refine ⟨747604842536900110742875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996806456715866814323833 747604842536900110742875)
          ·
            refine ⟨1121407263805350166114313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747604842536900110742875 1121407263805350166114313)
            ·
              refine ⟨841055447854012624585735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121407263805350166114313 841055447854012624585735)
              ·
                refine ⟨1261583171781018936878603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841055447854012624585735 1261583171781018936878603)
                ·
                  refine ⟨1892374757671528405317905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261583171781018936878603 1892374757671528405317905)
                  ·
                    refine ⟨1419281068253646303988429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892374757671528405317905 1419281068253646303988429)
                    ·
                      refine ⟨532230400595117363995661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419281068253646303988429 532230400595117363995661)
                      ·
                        rfl

theorem cell23_1036515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1036515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036515 prefixEnd_1036515 := by exact prefixLift 1036515
  have htrace : WordTrace (prefixWord ++ tailWord_1036515) baseStart_1036515 baseEnd_1036515 := by
    simpa [prefixWord, tailWord_1036515, baseEnd_1036515] using wordTrace_append hprefix tailTrace_1036515
  have hstable : (prefixWord ++ tailWord_1036515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036515).length < 2 ^ (prefixWord ++ tailWord_1036515).sum := by decide
  have hdescent : baseEnd_1036515 < baseStart_1036515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036534 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_1036534 : Nat := 118140960795 + 1036534 * 2 ^ 59
def prefixEnd_1036534 : Nat := 4983230072969 + 3 ^ 40 * 1036534 * 2
def baseEnd_1036534 : Nat := 532240156727552789658073

theorem tailTrace_1036534 : CollatzResearch.WordTrace tailWord_1036534 prefixEnd_1036534 532240156727552789658073 := by
  unfold tailWord_1036534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362843801676363672409791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25203667217881212505704437 2362843801676363672409791)
  ·
    refine ⟨3544265702514545508614687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2362843801676363672409791 3544265702514545508614687)
    ·
      refine ⟨5316398553771818262922031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544265702514545508614687 5316398553771818262922031)
      ·
        refine ⟨7974597830657727394383047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316398553771818262922031 7974597830657727394383047)
        ·
          refine ⟨11961896745986591091574571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974597830657727394383047 11961896745986591091574571)
          ·
            refine ⟨17942845118979886637361857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961896745986591091574571 17942845118979886637361857)
            ·
              refine ⟨13457133839234914978021393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17942845118979886637361857 13457133839234914978021393)
              ·
                refine ⟨10092850379426186233516045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13457133839234914978021393 10092850379426186233516045)
                ·
                  refine ⟨3784818892284819837568517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10092850379426186233516045 3784818892284819837568517)
                  ·
                    refine ⟨709653542303403719544097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3784818892284819837568517 709653542303403719544097)
                    ·
                      refine ⟨532240156727552789658073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709653542303403719544097 532240156727552789658073)
                      ·
                        rfl

theorem cell23_1036534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_1036534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036534 prefixEnd_1036534 := by exact prefixLift 1036534
  have htrace : WordTrace (prefixWord ++ tailWord_1036534) baseStart_1036534 baseEnd_1036534 := by
    simpa [prefixWord, tailWord_1036534, baseEnd_1036534] using wordTrace_append hprefix tailTrace_1036534
  have hstable : (prefixWord ++ tailWord_1036534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036534).length < 2 ^ (prefixWord ++ tailWord_1036534).sum := by decide
  have hdescent : baseEnd_1036534 < baseStart_1036534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036597 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1036597 : Nat := 118140960795 + 1036597 * 2 ^ 59
def prefixEnd_1036597 : Nat := 4983230072969 + 3 ^ 40 * 1036597 * 2
def baseEnd_1036597 : Nat := 532272506008786043170283

theorem tailTrace_1036597 : CollatzResearch.WordTrace tailWord_1036597 prefixEnd_1036597 532272506008786043170283 := by
  unfold tailWord_1036597
  simp only [CollatzResearch.WordTrace]
  refine ⟨37807798625593580518100045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25205199083729053678733363 37807798625593580518100045)
  ·
    refine ⟨14177924484597592694287517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37807798625593580518100045 14177924484597592694287517)
    ·
      refine ⟨5316721681724097260357819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14177924484597592694287517 5316721681724097260357819)
      ·
        refine ⟨7975082522586145890536729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316721681724097260357819 7975082522586145890536729)
        ·
          refine ⟨5981311891939609417902547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7975082522586145890536729 5981311891939609417902547)
          ·
            refine ⟨8971967837909414126853821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981311891939609417902547 8971967837909414126853821)
            ·
              refine ⟨3364487939216030297570183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8971967837909414126853821 3364487939216030297570183)
              ·
                refine ⟨5046731908824045446355275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364487939216030297570183 5046731908824045446355275)
                ·
                  refine ⟨7570097863236068169532913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046731908824045446355275 7570097863236068169532913)
                  ·
                    refine ⟨5677573397427051127149685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7570097863236068169532913 5677573397427051127149685)
                    ·
                      refine ⟨532272506008786043170283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5677573397427051127149685 532272506008786043170283)
                      ·
                        rfl

theorem cell23_1036597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1036597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036597 prefixEnd_1036597 := by exact prefixLift 1036597
  have htrace : WordTrace (prefixWord ++ tailWord_1036597) baseStart_1036597 baseEnd_1036597 := by
    simpa [prefixWord, tailWord_1036597, baseEnd_1036597] using wordTrace_append hprefix tailTrace_1036597
  have hstable : (prefixWord ++ tailWord_1036597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036597).length < 2 ^ (prefixWord ++ tailWord_1036597).sum := by decide
  have hdescent : baseEnd_1036597 < baseStart_1036597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036607 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1036607 : Nat := 118140960795 + 1036607 * 2 ^ 59
def prefixEnd_1036607 : Nat := 4983230072969 + 3 ^ 40 * 1036607 * 2
def baseEnd_1036607 : Nat := 532277640815331004045237

theorem tailTrace_1036607 : CollatzResearch.WordTrace tailWord_1036607 prefixEnd_1036607 532277640815331004045237 := by
  unfold tailWord_1036607
  simp only [CollatzResearch.WordTrace]
  refine ⟨37808163355557352225964075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25205442237038234817309383 37808163355557352225964075)
  ·
    refine ⟨56712245033336028338946113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37808163355557352225964075 56712245033336028338946113)
    ·
      refine ⟨42534183775002021254209585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56712245033336028338946113 42534183775002021254209585)
      ·
        refine ⟨31900637831251515940657189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42534183775002021254209585 31900637831251515940657189)
        ·
          refine ⟨5981369593359659238873223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31900637831251515940657189 5981369593359659238873223)
          ·
            refine ⟨8972054390039488858309835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981369593359659238873223 8972054390039488858309835)
            ·
              refine ⟨13458081585059233287464753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972054390039488858309835 13458081585059233287464753)
              ·
                refine ⟨10093561188794424965598565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13458081585059233287464753 10093561188794424965598565)
                ·
                  refine ⟨1892542722898954681049731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10093561188794424965598565 1892542722898954681049731)
                  ·
                    refine ⟨2838814084348432021574597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892542722898954681049731 2838814084348432021574597)
                    ·
                      refine ⟨532277640815331004045237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2838814084348432021574597 532277640815331004045237)
                      ·
                        rfl

theorem cell23_1036607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1036607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036607 prefixEnd_1036607 := by exact prefixLift 1036607
  have htrace : WordTrace (prefixWord ++ tailWord_1036607) baseStart_1036607 baseEnd_1036607 := by
    simpa [prefixWord, tailWord_1036607, baseEnd_1036607] using wordTrace_append hprefix tailTrace_1036607
  have hstable : (prefixWord ++ tailWord_1036607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036607).length < 2 ^ (prefixWord ++ tailWord_1036607).sum := by decide
  have hdescent : baseEnd_1036607 < baseStart_1036607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036617 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_1036617 : Nat := 118140960795 + 1036617 * 2 ^ 59
def prefixEnd_1036617 : Nat := 4983230072969 + 3 ^ 40 * 1036617 * 2
def baseEnd_1036617 : Nat := 177427591873958654973397

theorem tailTrace_1036617 : CollatzResearch.WordTrace tailWord_1036617 prefixEnd_1036617 177427591873958654973397 := by
  unfold tailWord_1036617
  simp only [CollatzResearch.WordTrace]
  refine ⟨37808528085521123933828105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25205685390347415955885403 37808528085521123933828105)
  ·
    refine ⟨28356396064140842950371079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37808528085521123933828105 28356396064140842950371079)
    ·
      refine ⟨42534594096211264425556619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28356396064140842950371079 42534594096211264425556619)
      ·
        refine ⟨63801891144316896638334929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42534594096211264425556619 63801891144316896638334929)
        ·
          refine ⟨47851418358237672478751197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63801891144316896638334929 47851418358237672478751197)
          ·
            refine ⟨17944281884339127179531699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47851418358237672478751197 17944281884339127179531699)
            ·
              refine ⟨26916422826508690769297549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944281884339127179531699 26916422826508690769297549)
              ·
                refine ⟨10093658559940759038486581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26916422826508690769297549 10093658559940759038486581)
                ·
                  refine ⟨946280489994446159858117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10093658559940759038486581 946280489994446159858117)
                  ·
                    refine ⟨177427591873958654973397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946280489994446159858117 177427591873958654973397)
                    ·
                      rfl

theorem cell23_1036617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_1036617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036617 prefixEnd_1036617 := by exact prefixLift 1036617
  have htrace : WordTrace (prefixWord ++ tailWord_1036617) baseStart_1036617 baseEnd_1036617 := by
    simpa [prefixWord, tailWord_1036617, baseEnd_1036617] using wordTrace_append hprefix tailTrace_1036617
  have hstable : (prefixWord ++ tailWord_1036617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036617).length < 2 ^ (prefixWord ++ tailWord_1036617).sum := by decide
  have hdescent : baseEnd_1036617 < baseStart_1036617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036624 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_1036624 : Nat := 118140960795 + 1036624 * 2 ^ 59
def prefixEnd_1036624 : Nat := 4983230072969 + 3 ^ 40 * 1036624 * 2
def baseEnd_1036624 : Nat := 532286369986457437532659

theorem tailTrace_1036624 : CollatzResearch.WordTrace tailWord_1036624 prefixEnd_1036624 532286369986457437532659 := by
  unfold tailWord_1036624
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904391698247882064666463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25205855597663842752888617 18904391698247882064666463)
  ·
    refine ⟨28356587547371823096999695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904391698247882064666463 28356587547371823096999695)
    ·
      refine ⟨42534881321057734645499543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28356587547371823096999695 42534881321057734645499543)
      ·
        refine ⟨63802321981586601968249315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42534881321057734645499543 63802321981586601968249315)
        ·
          refine ⟨95703482972379902952373973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63802321981586601968249315 95703482972379902952373973)
          ·
            refine ⟨2243050382165153975446265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 95703482972379902952373973 2243050382165153975446265)
            ·
              refine ⟨1682287786623865481584699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243050382165153975446265 1682287786623865481584699)
              ·
                refine ⟨2523431679935798222377049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682287786623865481584699 2523431679935798222377049)
                ·
                  refine ⟨1892573759951848666782787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523431679935798222377049 1892573759951848666782787)
                  ·
                    refine ⟨2838860639927773000174181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892573759951848666782787 2838860639927773000174181)
                    ·
                      refine ⟨532286369986457437532659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2838860639927773000174181 532286369986457437532659)
                      ·
                        rfl

theorem cell23_1036624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_1036624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036624 prefixEnd_1036624 := by exact prefixLift 1036624
  have htrace : WordTrace (prefixWord ++ tailWord_1036624) baseStart_1036624 baseEnd_1036624 := by
    simpa [prefixWord, tailWord_1036624, baseEnd_1036624] using wordTrace_append hprefix tailTrace_1036624
  have hstable : (prefixWord ++ tailWord_1036624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036624).length < 2 ^ (prefixWord ++ tailWord_1036624).sum := by decide
  have hdescent : baseEnd_1036624 < baseStart_1036624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036644 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1036644 : Nat := 118140960795 + 1036644 * 2 ^ 59
def prefixEnd_1036644 : Nat := 4983230072969 + 3 ^ 40 * 1036644 * 2
def baseEnd_1036644 : Nat := 532296639599547359282567

theorem tailTrace_1036644 : CollatzResearch.WordTrace tailWord_1036644 prefixEnd_1036644 532296639599547359282567 := by
  unfold tailWord_1036644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904756428211653772530493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25206341904282205030040657 18904756428211653772530493)
  ·
    refine ⟨7089283660579370164698935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18904756428211653772530493 7089283660579370164698935)
    ·
      refine ⟨10633925490869055247048403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089283660579370164698935 10633925490869055247048403)
      ·
        refine ⟨15950888236303582870572605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633925490869055247048403 15950888236303582870572605)
        ·
          refine ⟨5981583088613843576464727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15950888236303582870572605 5981583088613843576464727)
          ·
            refine ⟨8972374632920765364697091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981583088613843576464727 8972374632920765364697091)
            ·
              refine ⟨13458561949381148047045637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972374632920765364697091 13458561949381148047045637)
              ·
                refine ⟨2523480365508965258821057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13458561949381148047045637 2523480365508965258821057)
                ·
                  refine ⟨1892610274131723944115793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523480365508965258821057 1892610274131723944115793)
                  ·
                    refine ⟨1419457705598792958086845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892610274131723944115793 1419457705598792958086845)
                    ·
                      refine ⟨532296639599547359282567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419457705598792958086845 532296639599547359282567)
                      ·
                        rfl

theorem cell23_1036644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1036644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036644 prefixEnd_1036644 := by exact prefixLift 1036644
  have htrace : WordTrace (prefixWord ++ tailWord_1036644) baseStart_1036644 baseEnd_1036644 := by
    simpa [prefixWord, tailWord_1036644, baseEnd_1036644] using wordTrace_append hprefix tailTrace_1036644
  have hstable : (prefixWord ++ tailWord_1036644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036644).length < 2 ^ (prefixWord ++ tailWord_1036644).sum := by decide
  have hdescent : baseEnd_1036644 < baseStart_1036644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036657 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_1036657 : Nat := 118140960795 + 1036657 * 2 ^ 59
def prefixEnd_1036657 : Nat := 4983230072969 + 3 ^ 40 * 1036657 * 2
def baseEnd_1036657 : Nat := 532303314848055808420007

theorem tailTrace_1036657 : CollatzResearch.WordTrace tailWord_1036657 prefixEnd_1036657 532303314848055808420007 := by
  unfold tailWord_1036657
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809987005376210765284225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25206658003584140510189483 37809987005376210765284225)
  ·
    refine ⟨28357490254032158073963169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37809987005376210765284225 28357490254032158073963169)
    ·
      refine ⟨21268117690524118555472377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28357490254032158073963169 21268117690524118555472377)
      ·
        refine ⟨15951088267893088916604283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21268117690524118555472377 15951088267893088916604283)
        ·
          refine ⟨23926632401839633374906425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15951088267893088916604283 23926632401839633374906425)
          ·
            refine ⟨17944974301379725031179819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23926632401839633374906425 17944974301379725031179819)
            ·
              refine ⟨26917461452069587546769729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944974301379725031179819 26917461452069587546769729)
              ·
                refine ⟨20188096089052190660077297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26917461452069587546769729 20188096089052190660077297)
                ·
                  refine ⟨15141072066789142995057973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20188096089052190660077297 15141072066789142995057973)
                  ·
                    refine ⟨1419475506261482155786685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15141072066789142995057973 1419475506261482155786685)
                    ·
                      refine ⟨532303314848055808420007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419475506261482155786685 532303314848055808420007)
                      ·
                        rfl

theorem cell23_1036657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_1036657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036657 prefixEnd_1036657 := by exact prefixLift 1036657
  have htrace : WordTrace (prefixWord ++ tailWord_1036657) baseStart_1036657 baseEnd_1036657 := by
    simpa [prefixWord, tailWord_1036657, baseEnd_1036657] using wordTrace_append hprefix tailTrace_1036657
  have hstable : (prefixWord ++ tailWord_1036657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036657).length < 2 ^ (prefixWord ++ tailWord_1036657).sum := by decide
  have hdescent : baseEnd_1036657 < baseStart_1036657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036708 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_1036708 : Nat := 118140960795 + 1036708 * 2 ^ 59
def prefixEnd_1036708 : Nat := 4983230072969 + 3 ^ 40 * 1036708 * 2
def baseEnd_1036708 : Nat := 532329502361435108882273

theorem tailTrace_1036708 : CollatzResearch.WordTrace tailWord_1036708 prefixEnd_1036708 532329502361435108882273 := by
  unfold tailWord_1036708
  simp only [CollatzResearch.WordTrace]
  refine ⟨18905923564095723237695389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25207898085460964316927185 18905923564095723237695389)
  ·
    refine ⟨7089721336535896214135771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18905923564095723237695389 7089721336535896214135771)
    ·
      refine ⟨10634582004803844321203657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089721336535896214135771 10634582004803844321203657)
      ·
        refine ⟨7975936503602883240902743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634582004803844321203657 7975936503602883240902743)
        ·
          refine ⟨11963904755404324861354115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975936503602883240902743 11963904755404324861354115)
          ·
            refine ⟨17945857133106487292031173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963904755404324861354115 17945857133106487292031173)
            ·
              refine ⟨3364848212457466367255845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17945857133106487292031173 3364848212457466367255845)
              ·
                refine ⟨630909039835774943860471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3364848212457466367255845 630909039835774943860471)
                ·
                  refine ⟨946363559753662415790707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630909039835774943860471 946363559753662415790707)
                  ·
                    refine ⟨1419545339630493623686061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946363559753662415790707 1419545339630493623686061)
                    ·
                      refine ⟨532329502361435108882273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419545339630493623686061 532329502361435108882273)
                      ·
                        rfl

theorem cell23_1036708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_1036708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036708 prefixEnd_1036708 := by exact prefixLift 1036708
  have htrace : WordTrace (prefixWord ++ tailWord_1036708) baseStart_1036708 baseEnd_1036708 := by
    simpa [prefixWord, tailWord_1036708, baseEnd_1036708] using wordTrace_append hprefix tailTrace_1036708
  have hstable : (prefixWord ++ tailWord_1036708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036708).length < 2 ^ (prefixWord ++ tailWord_1036708).sum := by decide
  have hdescent : baseEnd_1036708 < baseStart_1036708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036758 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1036758 : Nat := 118140960795 + 1036758 * 2 ^ 59
def prefixEnd_1036758 : Nat := 4983230072969 + 3 ^ 40 * 1036758 * 2
def baseEnd_1036758 : Nat := 177451725464719971085681

theorem tailTrace_1036758 : CollatzResearch.WordTrace tailWord_1036758 prefixEnd_1036758 177451725464719971085681 := by
  unfold tailWord_1036758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363354423625644063419433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25209113852006870009807285 2363354423625644063419433)
  ·
    refine ⟨1772515817719233047564575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2363354423625644063419433 1772515817719233047564575)
    ·
      refine ⟨2658773726578849571346863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772515817719233047564575 2658773726578849571346863)
      ·
        refine ⟨3988160589868274357020295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658773726578849571346863 3988160589868274357020295)
        ·
          refine ⟨5982240884802411535530443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988160589868274357020295 5982240884802411535530443)
          ·
            refine ⟨8973361327203617303295665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982240884802411535530443 8973361327203617303295665)
            ·
              refine ⟨6730020995402712977471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973361327203617303295665 6730020995402712977471749)
              ·
                refine ⟨1261878936638008683275953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6730020995402712977471749 1261878936638008683275953)
                ·
                  refine ⟨946409202478506512456965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261878936638008683275953 946409202478506512456965)
                  ·
                    refine ⟨177451725464719971085681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946409202478506512456965 177451725464719971085681)
                    ·
                      rfl

theorem cell23_1036758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1036758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036758 prefixEnd_1036758 := by exact prefixLift 1036758
  have htrace : WordTrace (prefixWord ++ tailWord_1036758) baseStart_1036758 baseEnd_1036758 := by
    simpa [prefixWord, tailWord_1036758, baseEnd_1036758] using wordTrace_append hprefix tailTrace_1036758
  have hstable : (prefixWord ++ tailWord_1036758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036758).length < 2 ^ (prefixWord ++ tailWord_1036758).sum := by decide
  have hdescent : baseEnd_1036758 < baseStart_1036758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036777 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_1036777 : Nat := 118140960795 + 1036777 * 2 ^ 59
def prefixEnd_1036777 : Nat := 4983230072969 + 3 ^ 40 * 1036777 * 2
def baseEnd_1036777 : Nat := 532364932526595338919455

theorem tailTrace_1036777 : CollatzResearch.WordTrace tailWord_1036777 prefixEnd_1036777 532364932526595338919455 := by
  unfold tailWord_1036777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37814363764941471259652585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25209575843294314173101723 37814363764941471259652585)
  ·
    refine ⟨28360772823706103444739439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37814363764941471259652585 28360772823706103444739439)
    ·
      refine ⟨42541159235559155167109159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28360772823706103444739439 42541159235559155167109159)
      ·
        refine ⟨63811738853338732750663739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42541159235559155167109159 63811738853338732750663739)
        ·
          refine ⟨95717608280008099125995609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63811738853338732750663739 95717608280008099125995609)
          ·
            refine ⟨71788206210006074344496707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95717608280008099125995609 71788206210006074344496707)
            ·
              refine ⟨107682309315009111516745061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71788206210006074344496707 107682309315009111516745061)
              ·
                refine ⟨20190432996564208409389699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107682309315009111516745061 20190432996564208409389699)
                ·
                  refine ⟨30285649494846312614084549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20190432996564208409389699 30285649494846312614084549)
                  ·
                    refine ⟨5678559280283683615140853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30285649494846312614084549 5678559280283683615140853)
                    ·
                      refine ⟨532364932526595338919455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5678559280283683615140853 532364932526595338919455)
                      ·
                        rfl

theorem cell23_1036777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_1036777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036777 prefixEnd_1036777 := by exact prefixLift 1036777
  have htrace : WordTrace (prefixWord ++ tailWord_1036777) baseStart_1036777 baseEnd_1036777 := by
    simpa [prefixWord, tailWord_1036777, baseEnd_1036777] using wordTrace_append hprefix tailTrace_1036777
  have hstable : (prefixWord ++ tailWord_1036777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036777).length < 2 ^ (prefixWord ++ tailWord_1036777).sum := by decide
  have hdescent : baseEnd_1036777 < baseStart_1036777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036802 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1036802 : Nat := 118140960795 + 1036802 * 2 ^ 59
def prefixEnd_1036802 : Nat := 4983230072969 + 3 ^ 40 * 1036802 * 2
def baseEnd_1036802 : Nat := 532377769542957741106841

theorem tailTrace_1036802 : CollatzResearch.WordTrace tailWord_1036802 prefixEnd_1036802 532377769542957741106841 := by
  unfold tailWord_1036802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453818897462725132328165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25210183726567267019541773 9453818897462725132328165)
  ·
    refine ⟨1772591043274260962311531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9453818897462725132328165 1772591043274260962311531)
    ·
      refine ⟨2658886564911391443467297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772591043274260962311531 2658886564911391443467297)
      ·
        refine ⟨1994164923683543582600473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2658886564911391443467297 1994164923683543582600473)
        ·
          refine ⟨1495623692762657686950355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994164923683543582600473 1495623692762657686950355)
          ·
            refine ⟨2243435539143986530425533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495623692762657686950355 2243435539143986530425533)
            ·
              refine ⟨841288327178994948909575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2243435539143986530425533 841288327178994948909575)
              ·
                refine ⟨1261932490768492423364363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841288327178994948909575 1261932490768492423364363)
                ·
                  refine ⟨1892898736152738635046545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261932490768492423364363 1892898736152738635046545)
                  ·
                    refine ⟨1419674052114553976284909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892898736152738635046545 1419674052114553976284909)
                    ·
                      refine ⟨532377769542957741106841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419674052114553976284909 532377769542957741106841)
                      ·
                        rfl

theorem cell23_1036802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1036802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036802 prefixEnd_1036802 := by exact prefixLift 1036802
  have htrace : WordTrace (prefixWord ++ tailWord_1036802) baseStart_1036802 baseEnd_1036802 := by
    simpa [prefixWord, tailWord_1036802, baseEnd_1036802] using wordTrace_append hprefix tailTrace_1036802
  have hstable : (prefixWord ++ tailWord_1036802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036802).length < 2 ^ (prefixWord ++ tailWord_1036802).sum := by decide
  have hdescent : baseEnd_1036802 < baseStart_1036802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036821 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_1036821 : Nat := 118140960795 + 1036821 * 2 ^ 59
def prefixEnd_1036821 : Nat := 4983230072969 + 3 ^ 40 * 1036821 * 2
def baseEnd_1036821 : Nat := 532387525675393166769253

theorem tailTrace_1036821 : CollatzResearch.WordTrace tailWord_1036821 prefixEnd_1036821 532387525675393166769253 := by
  unfold tailWord_1036821
  simp only [CollatzResearch.WordTrace]
  refine ⟨37815968576782066774254317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25210645717854711182836211 37815968576782066774254317)
  ·
    refine ⟨14180988216293275040345369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37815968576782066774254317 14180988216293275040345369)
    ·
      refine ⟨10635741162219956280259027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14180988216293275040345369 10635741162219956280259027)
      ·
        refine ⟨15953611743329934420388541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635741162219956280259027 15953611743329934420388541)
        ·
          refine ⟨5982604403748725407645703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15953611743329934420388541 5982604403748725407645703)
          ·
            refine ⟨8973906605623088111468555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982604403748725407645703 8973906605623088111468555)
            ·
              refine ⟨13460859908434632167202833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973906605623088111468555 13460859908434632167202833)
              ·
                refine ⟨10095644931325974125402125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13460859908434632167202833 10095644931325974125402125)
                ·
                  refine ⟨3785866849247240297025797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10095644931325974125402125 3785866849247240297025797)
                  ·
                    refine ⟨709850034233857555692337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785866849247240297025797 709850034233857555692337)
                    ·
                      refine ⟨532387525675393166769253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709850034233857555692337 532387525675393166769253)
                      ·
                        rfl

theorem cell23_1036821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_1036821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036821 prefixEnd_1036821 := by exact prefixLift 1036821
  have htrace : WordTrace (prefixWord ++ tailWord_1036821) baseStart_1036821 baseEnd_1036821 := by
    simpa [prefixWord, tailWord_1036821, baseEnd_1036821] using wordTrace_append hprefix tailTrace_1036821
  have hstable : (prefixWord ++ tailWord_1036821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036821).length < 2 ^ (prefixWord ++ tailWord_1036821).sum := by decide
  have hdescent : baseEnd_1036821 < baseStart_1036821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036827 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 13]
def baseStart_1036827 : Nat := 118140960795 + 1036827 * 2 ^ 59
def prefixEnd_1036827 : Nat := 4983230072969 + 3 ^ 40 * 1036827 * 2
def baseEnd_1036827 : Nat := 59154511839924460366025

theorem tailTrace_1036827 : CollatzResearch.WordTrace tailWord_1036827 prefixEnd_1036827 59154511839924460366025 := by
  unfold tailWord_1036827
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816187414760329798972735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25210791609840219865981823 37816187414760329798972735)
  ·
    refine ⟨56724281122140494698459103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37816187414760329798972735 56724281122140494698459103)
    ·
      refine ⟨85086421683210742047688655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56724281122140494698459103 85086421683210742047688655)
      ·
        refine ⟨127629632524816113071532983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85086421683210742047688655 127629632524816113071532983)
        ·
          refine ⟨191444448787224169607299475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127629632524816113071532983 191444448787224169607299475)
          ·
            refine ⟨287166673180836254410949213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191444448787224169607299475 287166673180836254410949213)
            ·
              refine ⟨107687502442813595404105955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287166673180836254410949213 107687502442813595404105955)
              ·
                refine ⟨161531253664220393106158933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107687502442813595404105955 161531253664220393106158933)
                ·
                  refine ⟨59154511839924460366025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 161531253664220393106158933 59154511839924460366025)
                  ·
                    rfl

theorem cell23_1036827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 13].length) (baseStart_1036827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036827 prefixEnd_1036827 := by exact prefixLift 1036827
  have htrace : WordTrace (prefixWord ++ tailWord_1036827) baseStart_1036827 baseEnd_1036827 := by
    simpa [prefixWord, tailWord_1036827, baseEnd_1036827] using wordTrace_append hprefix tailTrace_1036827
  have hstable : (prefixWord ++ tailWord_1036827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036827).length < 2 ^ (prefixWord ++ tailWord_1036827).sum := by decide
  have hdescent : baseEnd_1036827 < baseStart_1036827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036871 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1036871 : Nat := 118140960795 + 1036871 * 2 ^ 59
def prefixEnd_1036871 : Nat := 4983230072969 + 3 ^ 40 * 1036871 * 2
def baseEnd_1036871 : Nat := 532413199708117971144023

theorem tailTrace_1036871 : CollatzResearch.WordTrace tailWord_1036871 prefixEnd_1036871 532413199708117971144023 := by
  unfold tailWord_1036871
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817792226600925313574467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25211861484400616875716311 37817792226600925313574467)
  ·
    refine ⟨56726688339901387970361701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37817792226600925313574467 56726688339901387970361701)
    ·
      refine ⟨10636254063731510244442819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56726688339901387970361701 10636254063731510244442819)
      ·
        refine ⟨15954381095597265366664229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636254063731510244442819 15954381095597265366664229)
        ·
          refine ⟨2991446455424487256249543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15954381095597265366664229 2991446455424487256249543)
          ·
            refine ⟨4487169683136730884374315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991446455424487256249543 4487169683136730884374315)
            ·
              refine ⟨6730754524705096326561473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487169683136730884374315 6730754524705096326561473)
              ·
                refine ⟨5048065893528822244921105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730754524705096326561473 5048065893528822244921105)
                ·
                  refine ⟨3786049420146616683690829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048065893528822244921105 3786049420146616683690829)
                  ·
                    refine ⟨1419768532554981256384061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786049420146616683690829 1419768532554981256384061)
                    ·
                      refine ⟨532413199708117971144023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419768532554981256384061 532413199708117971144023)
                      ·
                        rfl

theorem cell23_1036871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1036871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036871 prefixEnd_1036871 := by exact prefixLift 1036871
  have htrace : WordTrace (prefixWord ++ tailWord_1036871) baseStart_1036871 baseEnd_1036871 := by
    simpa [prefixWord, tailWord_1036871, baseEnd_1036871] using wordTrace_append hprefix tailTrace_1036871
  have hstable : (prefixWord ++ tailWord_1036871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036871).length < 2 ^ (prefixWord ++ tailWord_1036871).sum := by decide
  have hdescent : baseEnd_1036871 < baseStart_1036871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036911 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 6, 2]
def baseStart_1036911 : Nat := 118140960795 + 1036911 * 2 ^ 59
def prefixEnd_1036911 : Nat := 4983230072969 + 3 ^ 40 * 1036911 * 2
def baseEnd_1036911 : Nat := 532433738934297814643839

theorem tailTrace_1036911 : CollatzResearch.WordTrace tailWord_1036911 prefixEnd_1036911 532433738934297814643839 := by
  unfold tailWord_1036911
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819251146456012145030587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25212834097637341430020391 37819251146456012145030587)
  ·
    refine ⟨56728876719684018217545881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37819251146456012145030587 56728876719684018217545881)
    ·
      refine ⟨42546657539763013663159411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56728876719684018217545881 42546657539763013663159411)
      ·
        refine ⟨63819986309644520494739117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42546657539763013663159411 63819986309644520494739117)
        ·
          refine ⟨23932494866116695185527169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63819986309644520494739117 23932494866116695185527169)
          ·
            refine ⟨17949371149587521389145377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23932494866116695185527169 17949371149587521389145377)
            ·
              refine ⟨13462028362190641041859033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17949371149587521389145377 13462028362190641041859033)
              ·
                refine ⟨10096521271642980781394275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13462028362190641041859033 10096521271642980781394275)
                ·
                  refine ⟨15144781907464471172091413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096521271642980781394275 15144781907464471172091413)
                  ·
                    refine ⟨709911651912397086191785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15144781907464471172091413 709911651912397086191785)
                    ·
                      refine ⟨532433738934297814643839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 709911651912397086191785 532433738934297814643839)
                      ·
                        rfl

theorem cell23_1036911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6, 2].length) (baseStart_1036911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036911 prefixEnd_1036911 := by exact prefixLift 1036911
  have htrace : WordTrace (prefixWord ++ tailWord_1036911) baseStart_1036911 baseEnd_1036911 := by
    simpa [prefixWord, tailWord_1036911, baseEnd_1036911] using wordTrace_append hprefix tailTrace_1036911
  have hstable : (prefixWord ++ tailWord_1036911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036911).length < 2 ^ (prefixWord ++ tailWord_1036911).sum := by decide
  have hdescent : baseEnd_1036911 < baseStart_1036911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036924 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1036924 : Nat := 118140960795 + 1036924 * 2 ^ 59
def prefixEnd_1036924 : Nat := 4983230072969 + 3 ^ 40 * 1036924 * 2
def baseEnd_1036924 : Nat := 532440414182806263781279

theorem tailTrace_1036924 : CollatzResearch.WordTrace tailWord_1036924 prefixEnd_1036924 532440414182806263781279 := by
  unfold tailWord_1036924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909862647704457682626913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25213150196939276910169217 18909862647704457682626913)
  ·
    refine ⟨14182396985778343261970185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18909862647704457682626913 14182396985778343261970185)
    ·
      refine ⟨10636797739333757446477639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14182396985778343261970185 10636797739333757446477639)
      ·
        refine ⟨15955196609000636169716459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636797739333757446477639 15955196609000636169716459)
        ·
          refine ⟨23932794913500954254574689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15955196609000636169716459 23932794913500954254574689)
          ·
            refine ⟨17949596185125715690931017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23932794913500954254574689 17949596185125715690931017)
            ·
              refine ⟨13462197138844286768198263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17949596185125715690931017 13462197138844286768198263)
              ·
                refine ⟨20193295708266430152297395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13462197138844286768198263 20193295708266430152297395)
                ·
                  refine ⟨30289943562399645228446093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20193295708266430152297395 30289943562399645228446093)
                  ·
                    refine ⟨11358728835899866960667285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30289943562399645228446093 11358728835899866960667285)
                    ·
                      refine ⟨532440414182806263781279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11358728835899866960667285 532440414182806263781279)
                      ·
                        rfl

theorem cell23_1036924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1036924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036924 prefixEnd_1036924 := by exact prefixLift 1036924
  have htrace : WordTrace (prefixWord ++ tailWord_1036924) baseStart_1036924 baseEnd_1036924 := by
    simpa [prefixWord, tailWord_1036924, baseEnd_1036924] using wordTrace_append hprefix tailTrace_1036924
  have hstable : (prefixWord ++ tailWord_1036924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036924).length < 2 ^ (prefixWord ++ tailWord_1036924).sum := by decide
  have hdescent : baseEnd_1036924 < baseStart_1036924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036931 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3]
def baseStart_1036931 : Nat := 118140960795 + 1036931 * 2 ^ 59
def prefixEnd_1036931 : Nat := 4983230072969 + 3 ^ 40 * 1036931 * 2
def baseEnd_1036931 : Nat := 532444008547387736393747

theorem tailTrace_1036931 : CollatzResearch.WordTrace tailWord_1036931 prefixEnd_1036931 532444008547387736393747 := by
  unfold tailWord_1036931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819980606383555560758647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25213320404255703707172431 37819980606383555560758647)
  ·
    refine ⟨56729970909575333341137971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37819980606383555560758647 56729970909575333341137971)
    ·
      refine ⟨85094956364363000011706957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56729970909575333341137971 85094956364363000011706957)
      ·
        refine ⟨31910608636636125004390109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85094956364363000011706957 31910608636636125004390109)
        ·
          refine ⟨11966478238738546876646291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31910608636636125004390109 11966478238738546876646291)
          ·
            refine ⟨17949717358107820314969437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966478238738546876646291 17949717358107820314969437)
            ·
              refine ⟨6731144009290432618113539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949717358107820314969437 6731144009290432618113539)
              ·
                refine ⟨10096716013935648927170309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731144009290432618113539 10096716013935648927170309)
                ·
                  refine ⟨1893134252612934173844433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10096716013935648927170309 1893134252612934173844433)
                  ·
                    refine ⟨1419850689459700630383325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893134252612934173844433 1419850689459700630383325)
                    ·
                      refine ⟨532444008547387736393747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419850689459700630383325 532444008547387736393747)
                      ·
                        rfl

theorem cell23_1036931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_1036931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036931 prefixEnd_1036931 := by exact prefixLift 1036931
  have htrace : WordTrace (prefixWord ++ tailWord_1036931) baseStart_1036931 baseEnd_1036931 := by
    simpa [prefixWord, tailWord_1036931, baseEnd_1036931] using wordTrace_append hprefix tailTrace_1036931
  have hstable : (prefixWord ++ tailWord_1036931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036931).length < 2 ^ (prefixWord ++ tailWord_1036931).sum := by decide
  have hdescent : baseEnd_1036931 < baseStart_1036931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036951 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 6]
def baseStart_1036951 : Nat := 118140960795 + 1036951 * 2 ^ 59
def prefixEnd_1036951 : Nat := 4983230072969 + 3 ^ 40 * 1036951 * 2
def baseEnd_1036951 : Nat := 59161586462275295349295

theorem tailTrace_1036951 : CollatzResearch.WordTrace tailWord_1036951 prefixEnd_1036951 59161586462275295349295 := by
  unfold tailWord_1036951
  simp only [CollatzResearch.WordTrace]
  refine ⟨37820710066311098976486707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25213806710874065984324471 37820710066311098976486707)
  ·
    refine ⟨56731065099466648464730061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37820710066311098976486707 56731065099466648464730061)
    ·
      refine ⟨21274149412299993174273773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56731065099466648464730061 21274149412299993174273773)
      ·
        refine ⟨7977806029612497440352665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21274149412299993174273773 7977806029612497440352665)
        ·
          refine ⟨5983354522209373080264499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7977806029612497440352665 5983354522209373080264499)
          ·
            refine ⟨8975031783314059620396749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983354522209373080264499 8975031783314059620396749)
            ·
              refine ⟨3365636918742772357648781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8975031783314059620396749 3365636918742772357648781)
              ·
                refine ⟨1262113844528539634118293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3365636918742772357648781 1262113844528539634118293)
                ·
                  refine ⟨59161586462275295349295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1262113844528539634118293 59161586462275295349295)
                  ·
                    rfl

theorem cell23_1036951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 6].length) (baseStart_1036951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1036951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1036951 prefixEnd_1036951 := by exact prefixLift 1036951
  have htrace : WordTrace (prefixWord ++ tailWord_1036951) baseStart_1036951 baseEnd_1036951 := by
    simpa [prefixWord, tailWord_1036951, baseEnd_1036951] using wordTrace_append hprefix tailTrace_1036951
  have hstable : (prefixWord ++ tailWord_1036951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036951).length < 2 ^ (prefixWord ++ tailWord_1036951).sum := by decide
  have hdescent : baseEnd_1036951 < baseStart_1036951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037012 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1037012 : Nat := 118140960795 + 1037012 * 2 ^ 59
def prefixEnd_1037012 : Nat := 4983230072969 + 3 ^ 40 * 1037012 * 2
def baseEnd_1037012 : Nat := 532485600480401919480875

theorem tailTrace_1037012 : CollatzResearch.WordTrace tailWord_1037012 prefixEnd_1037012 532485600480401919480875 := by
  unfold tailWord_1037012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911467459545053197228645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25215289946060070929638193 18911467459545053197228645)
  ·
    refine ⟨3545900148664697474480371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18911467459545053197228645 3545900148664697474480371)
    ·
      refine ⟨5318850222997046211720557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545900148664697474480371 5318850222997046211720557)
      ·
        refine ⟨1994568833623892329395209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5318850222997046211720557 1994568833623892329395209)
        ·
          refine ⟨1495926625217919247046407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994568833623892329395209 1495926625217919247046407)
          ·
            refine ⟨2243889937826878870569611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495926625217919247046407 2243889937826878870569611)
            ·
              refine ⟨3365834906740318305854417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243889937826878870569611 3365834906740318305854417)
              ·
                refine ⟨2524376180055238729390813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365834906740318305854417 2524376180055238729390813)
                ·
                  refine ⟨946641067520714523521555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2524376180055238729390813 946641067520714523521555)
                  ·
                    refine ⟨1419961601281071785282333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946641067520714523521555 1419961601281071785282333)
                    ·
                      refine ⟨532485600480401919480875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1419961601281071785282333 532485600480401919480875)
                      ·
                        rfl

theorem cell23_1037012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1037012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037012 prefixEnd_1037012 := by exact prefixLift 1037012
  have htrace : WordTrace (prefixWord ++ tailWord_1037012) baseStart_1037012 baseEnd_1037012 := by
    simpa [prefixWord, tailWord_1037012, baseEnd_1037012] using wordTrace_append hprefix tailTrace_1037012
  have hstable : (prefixWord ++ tailWord_1037012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037012).length < 2 ^ (prefixWord ++ tailWord_1037012).sum := by decide
  have hdescent : baseEnd_1037012 < baseStart_1037012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037018 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_1037018 : Nat := 118140960795 + 1037018 * 2 ^ 59
def prefixEnd_1037018 : Nat := 4983230072969 + 3 ^ 40 * 1037018 * 2
def baseEnd_1037018 : Nat := 532488681364328896005847

theorem tailTrace_1037018 : CollatzResearch.WordTrace tailWord_1037018 prefixEnd_1037018 532488681364328896005847 := by
  unfold tailWord_1037018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455788439267092354793927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25215435838045579612783805 9455788439267092354793927)
  ·
    refine ⟨14183682658900638532190891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9455788439267092354793927 14183682658900638532190891)
    ·
      refine ⟨21275523988350957798286337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183682658900638532190891 21275523988350957798286337)
      ·
        refine ⟨15956642991263218348714753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21275523988350957798286337 15956642991263218348714753)
        ·
          refine ⟨11967482243447413761536065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15956642991263218348714753 11967482243447413761536065)
          ·
            refine ⟨8975611682585560321152049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967482243447413761536065 8975611682585560321152049)
            ·
              refine ⟨6731708761939170240864037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975611682585560321152049 6731708761939170240864037)
              ·
                refine ⟨1262195392863594420162007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6731708761939170240864037 1262195392863594420162007)
                ·
                  refine ⟨1893293089295391630243011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262195392863594420162007 1893293089295391630243011)
                  ·
                    refine ⟨2839939633943087445364517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1893293089295391630243011 2839939633943087445364517)
                    ·
                      refine ⟨532488681364328896005847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2839939633943087445364517 532488681364328896005847)
                      ·
                        rfl

theorem cell23_1037018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_1037018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037018 prefixEnd_1037018 := by exact prefixLift 1037018
  have htrace : WordTrace (prefixWord ++ tailWord_1037018) baseStart_1037018 baseEnd_1037018 := by
    simpa [prefixWord, tailWord_1037018, baseEnd_1037018] using wordTrace_append hprefix tailTrace_1037018
  have hstable : (prefixWord ++ tailWord_1037018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037018).length < 2 ^ (prefixWord ++ tailWord_1037018).sum := by decide
  have hdescent : baseEnd_1037018 < baseStart_1037018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037032 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1037032 : Nat := 118140960795 + 1037032 * 2 ^ 59
def prefixEnd_1037032 : Nat := 4983230072969 + 3 ^ 40 * 1037032 * 2
def baseEnd_1037032 : Nat := 177498623364497280410261

theorem tailTrace_1037032 : CollatzResearch.WordTrace tailWord_1037032 prefixEnd_1037032 177498623364497280410261 := by
  unfold tailWord_1037032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911832189508824905092675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25215776252678433206790233 18911832189508824905092675)
  ·
    refine ⟨28367748284263237357639013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18911832189508824905092675 28367748284263237357639013)
    ·
      refine ⟨5318952803299357004557315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28367748284263237357639013 5318952803299357004557315)
      ·
        refine ⟨7978429204949035506835973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318952803299357004557315 7978429204949035506835973)
        ·
          refine ⟨1495955475927944157531745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7978429204949035506835973 1495955475927944157531745)
          ·
            refine ⟨1121966606945958118148809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495955475927944157531745 1121966606945958118148809)
            ·
              refine ⟨841474955209468588611607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121966606945958118148809 841474955209468588611607)
              ·
                refine ⟨1262212432814202882917411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841474955209468588611607 1262212432814202882917411)
                ·
                  refine ⟨1893318649221304324376117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262212432814202882917411 1893318649221304324376117)
                  ·
                    refine ⟨177498623364497280410261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1893318649221304324376117 177498623364497280410261)
                    ·
                      rfl

theorem cell23_1037032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1037032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037032 prefixEnd_1037032 := by exact prefixLift 1037032
  have htrace : WordTrace (prefixWord ++ tailWord_1037032) baseStart_1037032 baseEnd_1037032 := by
    simpa [prefixWord, tailWord_1037032, baseEnd_1037032] using wordTrace_append hprefix tailTrace_1037032
  have hstable : (prefixWord ++ tailWord_1037032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037032).length < 2 ^ (prefixWord ++ tailWord_1037032).sum := by decide
  have hdescent : baseEnd_1037032 < baseStart_1037032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037052 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_1037052 : Nat := 118140960795 + 1037052 * 2 ^ 59
def prefixEnd_1037052 : Nat := 4983230072969 + 3 ^ 40 * 1037052 * 2
def baseEnd_1037052 : Nat := 532506139706581762980691

theorem tailTrace_1037052 : CollatzResearch.WordTrace tailWord_1037052 prefixEnd_1037052 532506139706581762980691 := by
  unfold tailWord_1037052
  simp only [CollatzResearch.WordTrace]
  refine ⟨18912196919472596612956705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25216262559296795483942273 18912196919472596612956705)
  ·
    refine ⟨14184147689604447459717529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18912196919472596612956705 14184147689604447459717529)
    ·
      refine ⟨10638110767203335594788147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14184147689604447459717529 10638110767203335594788147)
      ·
        refine ⟨15957166150805003392182221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638110767203335594788147 15957166150805003392182221)
        ·
          refine ⟨5983937306551876272068333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15957166150805003392182221 5983937306551876272068333)
          ·
            refine ⟨2243976489956953602025625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5983937306551876272068333 2243976489956953602025625)
            ·
              refine ⟨1682982367467715201519219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243976489956953602025625 1682982367467715201519219)
              ·
                refine ⟨2524473551201572802278829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682982367467715201519219 2524473551201572802278829)
                ·
                  refine ⟨946677581700589800854561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2524473551201572802278829 946677581700589800854561)
                  ·
                    refine ⟨710008186275442350640921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946677581700589800854561 710008186275442350640921)
                    ·
                      refine ⟨532506139706581762980691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710008186275442350640921 532506139706581762980691)
                      ·
                        rfl

theorem cell23_1037052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_1037052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037052 prefixEnd_1037052 := by exact prefixLift 1037052
  have htrace : WordTrace (prefixWord ++ tailWord_1037052) baseStart_1037052 baseEnd_1037052 := by
    simpa [prefixWord, tailWord_1037052, baseEnd_1037052] using wordTrace_append hprefix tailTrace_1037052
  have hstable : (prefixWord ++ tailWord_1037052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037052).length < 2 ^ (prefixWord ++ tailWord_1037052).sum := by decide
  have hdescent : baseEnd_1037052 < baseStart_1037052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037091 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1037091 : Nat := 118140960795 + 1037091 * 2 ^ 59
def prefixEnd_1037091 : Nat := 4983230072969 + 3 ^ 40 * 1037091 * 2
def baseEnd_1037091 : Nat := 532526165452107110393011

theorem tailTrace_1037091 : CollatzResearch.WordTrace tailWord_1037091 prefixEnd_1037091 532526165452107110393011 := by
  unfold tailWord_1037091
  simp only [CollatzResearch.WordTrace]
  refine ⟨37825816285803902886583127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25217210857202601924388751 37825816285803902886583127)
  ·
    refine ⟨56738724428705854329874691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37825816285803902886583127 56738724428705854329874691)
    ·
      refine ⟨85108086643058781494812037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56738724428705854329874691 85108086643058781494812037)
      ·
        refine ⟨15957766245573521530277257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85108086643058781494812037 15957766245573521530277257)
        ·
          refine ⟨11968324684180141147707943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15957766245573521530277257 11968324684180141147707943)
          ·
            refine ⟨17952487026270211721561915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968324684180141147707943 17952487026270211721561915)
            ·
              refine ⟨26928730539405317582342873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17952487026270211721561915 26928730539405317582342873)
              ·
                refine ⟨20196547904553988186757155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26928730539405317582342873 20196547904553988186757155)
                ·
                  refine ⟨30294821856830982280135733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20196547904553988186757155 30294821856830982280135733)
                  ·
                    refine ⟨2840139549077904588762725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30294821856830982280135733 2840139549077904588762725)
                    ·
                      refine ⟨532526165452107110393011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2840139549077904588762725 532526165452107110393011)
                      ·
                        rfl

theorem cell23_1037091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1037091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037091 prefixEnd_1037091 := by exact prefixLift 1037091
  have htrace : WordTrace (prefixWord ++ tailWord_1037091) baseStart_1037091 baseEnd_1037091 := by
    simpa [prefixWord, tailWord_1037091, baseEnd_1037091] using wordTrace_append hprefix tailTrace_1037091
  have hstable : (prefixWord ++ tailWord_1037091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037091).length < 2 ^ (prefixWord ++ tailWord_1037091).sum := by decide
  have hdescent : baseEnd_1037091 < baseStart_1037091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037102 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1037102 : Nat := 118140960795 + 1037102 * 2 ^ 59
def prefixEnd_1037102 : Nat := 4983230072969 + 3 ^ 40 * 1037102 * 2
def baseEnd_1037102 : Nat := 532531813739306567355461

theorem tailTrace_1037102 : CollatzResearch.WordTrace tailWord_1037102 prefixEnd_1037102 532531813739306567355461 := by
  unfold tailWord_1037102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728277186095506470654195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25217478325842701176822373 4728277186095506470654195)
  ·
    refine ⟨7092415779143259705981293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728277186095506470654195 7092415779143259705981293)
    ·
      refine ⟨2659655917178722389742985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7092415779143259705981293 2659655917178722389742985)
      ·
        refine ⟨1994741937884041792307239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659655917178722389742985 1994741937884041792307239)
        ·
          refine ⟨2992112906826062688460859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994741937884041792307239 2992112906826062688460859)
          ·
            refine ⟨4488169360239094032691289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992112906826062688460859 4488169360239094032691289)
            ·
              refine ⟨3366127020179320524518467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488169360239094032691289 3366127020179320524518467)
              ·
                refine ⟨5049190530268980786777701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366127020179320524518467 5049190530268980786777701)
                ·
                  refine ⟨946723224425433897520819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5049190530268980786777701 946723224425433897520819)
                  ·
                    refine ⟨1420084836638150846281229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946723224425433897520819 1420084836638150846281229)
                    ·
                      refine ⟨532531813739306567355461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1420084836638150846281229 532531813739306567355461)
                      ·
                        rfl

theorem cell23_1037102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1037102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037102 prefixEnd_1037102 := by exact prefixLift 1037102
  have htrace : WordTrace (prefixWord ++ tailWord_1037102) baseStart_1037102 baseEnd_1037102 := by
    simpa [prefixWord, tailWord_1037102, baseEnd_1037102] using wordTrace_append hprefix tailTrace_1037102
  have hstable : (prefixWord ++ tailWord_1037102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037102).length < 2 ^ (prefixWord ++ tailWord_1037102).sum := by decide
  have hdescent : baseEnd_1037102 < baseStart_1037102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037111 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1037111 : Nat := 118140960795 + 1037111 * 2 ^ 59
def prefixEnd_1037111 : Nat := 4983230072969 + 3 ^ 40 * 1037111 * 2
def baseEnd_1037111 : Nat := 532536435065197032142919

theorem tailTrace_1037111 : CollatzResearch.WordTrace tailWord_1037111 prefixEnd_1037111 532536435065197032142919 := by
  unfold tailWord_1037111
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826545745731446302311187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25217697163820964201540791 37826545745731446302311187)
  ·
    refine ⟨56739818618597169453466781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37826545745731446302311187 56739818618597169453466781)
    ·
      refine ⟨21277431981973938545050043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56739818618597169453466781 21277431981973938545050043)
      ·
        refine ⟨31916147972960907817575065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21277431981973938545050043 31916147972960907817575065)
        ·
          refine ⟨23937110979720680863181299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31916147972960907817575065 23937110979720680863181299)
          ·
            refine ⟨35905666469581021294771949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23937110979720680863181299 35905666469581021294771949)
            ·
              refine ⟨13464624926092882985539481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35905666469581021294771949 13464624926092882985539481)
              ·
                refine ⟨10098468694569662239154611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13464624926092882985539481 10098468694569662239154611)
                ·
                  refine ⟨15147703041854493358731917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10098468694569662239154611 15147703041854493358731917)
                  ·
                    refine ⟨5680388640695435009524469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15147703041854493358731917 5680388640695435009524469)
                    ·
                      refine ⟨532536435065197032142919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5680388640695435009524469 532536435065197032142919)
                      ·
                        rfl

theorem cell23_1037111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1037111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037111 prefixEnd_1037111 := by exact prefixLift 1037111
  have htrace : WordTrace (prefixWord ++ tailWord_1037111) baseStart_1037111 baseEnd_1037111 := by
    simpa [prefixWord, tailWord_1037111, baseEnd_1037111] using wordTrace_append hprefix tailTrace_1037111
  have hstable : (prefixWord ++ tailWord_1037111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037111).length < 2 ^ (prefixWord ++ tailWord_1037111).sum := by decide
  have hdescent : baseEnd_1037111 < baseStart_1037111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037119 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 2, 1, 3]
def baseStart_1037119 : Nat := 118140960795 + 1037119 * 2 ^ 59
def prefixEnd_1037119 : Nat := 4983230072969 + 3 ^ 40 * 1037119 * 2
def baseEnd_1037119 : Nat := 532540542910433000842883

theorem tailTrace_1037119 : CollatzResearch.WordTrace tailWord_1037119 prefixEnd_1037119 532540542910433000842883 := by
  unfold tailWord_1037119
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826837529702463668602411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25217891686468309112401607 37826837529702463668602411)
  ·
    refine ⟨56740256294553695502903617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37826837529702463668602411 56740256294553695502903617)
    ·
      refine ⟨42555192220915271627177713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56740256294553695502903617 42555192220915271627177713)
      ·
        refine ⟨31916394165686453720383285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42555192220915271627177713 31916394165686453720383285)
        ·
          refine ⟨2992161953033105036285933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31916394165686453720383285 2992161953033105036285933)
          ·
            refine ⟨1122060732387414388607225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2992161953033105036285933 1122060732387414388607225)
            ·
              refine ⟨841545549290560791455419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122060732387414388607225 841545549290560791455419)
              ·
                refine ⟨1262318323935841187183129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841545549290560791455419 1262318323935841187183129)
                ·
                  refine ⟨946738742951880890387347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262318323935841187183129 946738742951880890387347)
                  ·
                    refine ⟨1420108114427821335581021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946738742951880890387347 1420108114427821335581021)
                    ·
                      refine ⟨532540542910433000842883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1420108114427821335581021 532540542910433000842883)
                      ·
                        rfl

theorem cell23_1037119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_1037119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037119 prefixEnd_1037119 := by exact prefixLift 1037119
  have htrace : WordTrace (prefixWord ++ tailWord_1037119) baseStart_1037119 baseEnd_1037119 := by
    simpa [prefixWord, tailWord_1037119, baseEnd_1037119] using wordTrace_append hprefix tailTrace_1037119
  have hstable : (prefixWord ++ tailWord_1037119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037119).length < 2 ^ (prefixWord ++ tailWord_1037119).sum := by decide
  have hdescent : baseEnd_1037119 < baseStart_1037119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037125 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_1037125 : Nat := 118140960795 + 1037125 * 2 ^ 59
def prefixEnd_1037125 : Nat := 4983230072969 + 3 ^ 40 * 1037125 * 2
def baseEnd_1037125 : Nat := 532543623794359977367855

theorem tailTrace_1037125 : CollatzResearch.WordTrace tailWord_1037125 prefixEnd_1037125 532543623794359977367855 := by
  unfold tailWord_1037125
  simp only [CollatzResearch.WordTrace]
  refine ⟨37827056367680726693320829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25218037578453817795547219 37827056367680726693320829)
  ·
    refine ⟨14185146137880272509995311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37827056367680726693320829 14185146137880272509995311)
    ·
      refine ⟨21277719206820408764992967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14185146137880272509995311 21277719206820408764992967)
      ·
        refine ⟨31916578810230613147489451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21277719206820408764992967 31916578810230613147489451)
        ·
          refine ⟨47874868215345919721234177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31916578810230613147489451 47874868215345919721234177)
          ·
            refine ⟨35906151161509439790925633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47874868215345919721234177 35906151161509439790925633)
            ·
              refine ⟨26929613371132079843194225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35906151161509439790925633 26929613371132079843194225)
              ·
                refine ⟨20197210028349059882395669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26929613371132079843194225 20197210028349059882395669)
                ·
                  refine ⟨946744220078862181987297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20197210028349059882395669 946744220078862181987297)
                  ·
                    refine ⟨710058165059146636490473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946744220078862181987297 710058165059146636490473)
                    ·
                      refine ⟨532543623794359977367855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710058165059146636490473 532543623794359977367855)
                      ·
                        rfl

theorem cell23_1037125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_1037125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037125 prefixEnd_1037125 := by exact prefixLift 1037125
  have htrace : WordTrace (prefixWord ++ tailWord_1037125) baseStart_1037125 baseEnd_1037125 := by
    simpa [prefixWord, tailWord_1037125, baseEnd_1037125] using wordTrace_append hprefix tailTrace_1037125
  have hstable : (prefixWord ++ tailWord_1037125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037125).length < 2 ^ (prefixWord ++ tailWord_1037125).sum := by decide
  have hdescent : baseEnd_1037125 < baseStart_1037125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037159 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_1037159 : Nat := 118140960795 + 1037159 * 2 ^ 59
def prefixEnd_1037159 : Nat := 4983230072969 + 3 ^ 40 * 1037159 * 2
def baseEnd_1037159 : Nat := 532561082136612844342699

theorem tailTrace_1037159 : CollatzResearch.WordTrace tailWord_1037159 prefixEnd_1037159 532561082136612844342699 := by
  unfold tailWord_1037159
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828296449557550500058531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25218864299705033666705687 37828296449557550500058531)
  ·
    refine ⟨56742444674336325750087797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37828296449557550500058531 56742444674336325750087797)
    ·
      refine ⟨5319604188219030539070731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56742444674336325750087797 5319604188219030539070731)
      ·
        refine ⟨7979406282328545808606097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319604188219030539070731 7979406282328545808606097)
        ·
          refine ⟨5984554711746409356454573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979406282328545808606097 5984554711746409356454573)
          ·
            refine ⟨2244208016904903508670465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5984554711746409356454573 2244208016904903508670465)
            ·
              refine ⟨1683156012678677631502849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244208016904903508670465 1683156012678677631502849)
              ·
                refine ⟨1262367009509008223627137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683156012678677631502849 1262367009509008223627137)
                ·
                  refine ⟨946775257131756167720353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262367009509008223627137 946775257131756167720353)
                  ·
                    refine ⟨710081442848817125790265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946775257131756167720353 710081442848817125790265)
                    ·
                      refine ⟨532561082136612844342699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710081442848817125790265 532561082136612844342699)
                      ·
                        rfl

theorem cell23_1037159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_1037159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037159 prefixEnd_1037159 := by exact prefixLift 1037159
  have htrace : WordTrace (prefixWord ++ tailWord_1037159) baseStart_1037159 baseEnd_1037159 := by
    simpa [prefixWord, tailWord_1037159, baseEnd_1037159] using wordTrace_append hprefix tailTrace_1037159
  have hstable : (prefixWord ++ tailWord_1037159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037159).length < 2 ^ (prefixWord ++ tailWord_1037159).sum := by decide
  have hdescent : baseEnd_1037159 < baseStart_1037159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037161 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_1037161 : Nat := 118140960795 + 1037161 * 2 ^ 59
def prefixEnd_1037161 : Nat := 4983230072969 + 3 ^ 40 * 1037161 * 2
def baseEnd_1037161 : Nat := 177520703032640612172563

theorem tailTrace_1037161 : CollatzResearch.WordTrace tailWord_1037161 prefixEnd_1037161 177520703032640612172563 := by
  unfold tailWord_1037161
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828369395550304841631337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25218912930366869894420891 37828369395550304841631337)
  ·
    refine ⟨28371277046662728631223503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37828369395550304841631337 28371277046662728631223503)
    ·
      refine ⟨42556915569994092946835255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28371277046662728631223503 42556915569994092946835255)
      ·
        refine ⟨63835373354991139420252883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42556915569994092946835255 63835373354991139420252883)
        ·
          refine ⟨95753060032486709130379325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63835373354991139420252883 95753060032486709130379325)
          ·
            refine ⟨35907397512182515923892247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95753060032486709130379325 35907397512182515923892247)
            ·
              refine ⟨53861096268273773885838371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35907397512182515923892247 53861096268273773885838371)
              ·
                refine ⟨80791644402410660828757557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53861096268273773885838371 80791644402410660828757557)
                ·
                  refine ⟨7574216662725999452696021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80791644402410660828757557 7574216662725999452696021)
                  ·
                    refine ⟨177520703032640612172563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7574216662725999452696021 177520703032640612172563)
                    ·
                      rfl

theorem cell23_1037161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_1037161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037161 prefixEnd_1037161 := by exact prefixLift 1037161
  have htrace : WordTrace (prefixWord ++ tailWord_1037161) baseStart_1037161 baseEnd_1037161 := by
    simpa [prefixWord, tailWord_1037161, baseEnd_1037161] using wordTrace_append hprefix tailTrace_1037161
  have hstable : (prefixWord ++ tailWord_1037161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037161).length < 2 ^ (prefixWord ++ tailWord_1037161).sum := by decide
  have hdescent : baseEnd_1037161 < baseStart_1037161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037182 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1037182 : Nat := 118140960795 + 1037182 * 2 ^ 59
def prefixEnd_1037182 : Nat := 4983230072969 + 3 ^ 40 * 1037182 * 2
def baseEnd_1037182 : Nat := 59174765799074028261677

theorem tailTrace_1037182 : CollatzResearch.WordTrace tailWord_1037182 prefixEnd_1037182 59174765799074028261677 := by
  unfold tailWord_1037182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728641916059278178518225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25219423552316150285430533 4728641916059278178518225)
  ·
    refine ⟨3546481437044458633888669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4728641916059278178518225 3546481437044458633888669)
    ·
      refine ⟨1329930538891671987708251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3546481437044458633888669 1329930538891671987708251)
      ·
        refine ⟨1994895808337507981562377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329930538891671987708251 1994895808337507981562377)
        ·
          refine ⟨1496171856253130986171783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994895808337507981562377 1496171856253130986171783)
          ·
            refine ⟨2244257784379696479257675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496171856253130986171783 2244257784379696479257675)
            ·
              refine ⟨3366386676569544718886513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244257784379696479257675 3366386676569544718886513)
              ·
                refine ⟨2524790007427158539164885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366386676569544718886513 2524790007427158539164885)
                ·
                  refine ⟨59174765799074028261677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2524790007427158539164885 59174765799074028261677)
                  ·
                    rfl

theorem cell23_1037182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1037182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037182 prefixEnd_1037182 := by exact prefixLift 1037182
  have htrace : WordTrace (prefixWord ++ tailWord_1037182) baseStart_1037182 baseEnd_1037182 := by
    simpa [prefixWord, tailWord_1037182, baseEnd_1037182] using wordTrace_append hprefix tailTrace_1037182
  have hstable : (prefixWord ++ tailWord_1037182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037182).length < 2 ^ (prefixWord ++ tailWord_1037182).sum := by decide
  have hdescent : baseEnd_1037182 < baseStart_1037182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037225 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_1037225 : Nat := 118140960795 + 1037225 * 2 ^ 59
def prefixEnd_1037225 : Nat := 4983230072969 + 3 ^ 40 * 1037225 * 2
def baseEnd_1037225 : Nat := 177531657286603195372465

theorem tailTrace_1037225 : CollatzResearch.WordTrace tailWord_1037225 prefixEnd_1037225 177531657286603195372465 := by
  unfold tailWord_1037225
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830703667318443771961129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25220469111545629181307419 37830703667318443771961129)
  ·
    refine ⟨28373027750488832828970847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37830703667318443771961129 28373027750488832828970847)
    ·
      refine ⟨42559541625733249243456271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373027750488832828970847 42559541625733249243456271)
      ·
        refine ⟨63839312438599873865184407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42559541625733249243456271 63839312438599873865184407)
        ·
          refine ⟨95758968657899810797776611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63839312438599873865184407 95758968657899810797776611)
          ·
            refine ⟨143638452986849716196664917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95758968657899810797776611 143638452986849716196664917)
            ·
              refine ⟨1683263120939645111679667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 143638452986849716196664917 1683263120939645111679667)
              ·
                refine ⟨2524894681409467667519501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683263120939645111679667 2524894681409467667519501)
                ·
                  refine ⟨946835505528550375319813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2524894681409467667519501 946835505528550375319813)
                  ·
                    refine ⟨177531657286603195372465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946835505528550375319813 177531657286603195372465)
                    ·
                      rfl

theorem cell23_1037225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_1037225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037225 prefixEnd_1037225 := by exact prefixLift 1037225
  have htrace : WordTrace (prefixWord ++ tailWord_1037225) baseStart_1037225 baseEnd_1037225 := by
    simpa [prefixWord, tailWord_1037225, baseEnd_1037225] using wordTrace_append hprefix tailTrace_1037225
  have hstable : (prefixWord ++ tailWord_1037225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037225).length < 2 ^ (prefixWord ++ tailWord_1037225).sum := by decide
  have hdescent : baseEnd_1037225 < baseStart_1037225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037259 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 1, 4]
def baseStart_1037259 : Nat := 118140960795 + 1037259 * 2 ^ 59
def prefixEnd_1037259 : Nat := 4983230072969 + 3 ^ 40 * 1037259 * 2
def baseEnd_1037259 : Nat := 177537476734020817697413

theorem tailTrace_1037259 : CollatzResearch.WordTrace tailWord_1037259 prefixEnd_1037259 177537476734020817697413 := by
  unfold tailWord_1037259
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831943749195267578698831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25221295832796845052465887 37831943749195267578698831)
  ·
    refine ⟨56747915623792901368048247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37831943749195267578698831 56747915623792901368048247)
    ·
      refine ⟨85121873435689352052072371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56747915623792901368048247 85121873435689352052072371)
      ·
        refine ⟨127682810153534028078108557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85121873435689352052072371 127682810153534028078108557)
        ·
          refine ⟨47881053807575260529290709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127682810153534028078108557 47881053807575260529290709)
          ·
            refine ⟨1122212198615045168655251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47881053807575260529290709 1122212198615045168655251)
            ·
              refine ⟨1683318297922567752982877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122212198615045168655251 1683318297922567752982877)
              ·
                refine ⟨631244361720962907368579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683318297922567752982877 631244361720962907368579)
                ·
                  refine ⟨946866542581444361052869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631244361720962907368579 946866542581444361052869)
                  ·
                    refine ⟨177537476734020817697413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 946866542581444361052869 177537476734020817697413)
                    ·
                      rfl

theorem cell23_1037259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 4].length) (baseStart_1037259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037259 prefixEnd_1037259 := by exact prefixLift 1037259
  have htrace : WordTrace (prefixWord ++ tailWord_1037259) baseStart_1037259 baseEnd_1037259 := by
    simpa [prefixWord, tailWord_1037259, baseEnd_1037259] using wordTrace_append hprefix tailTrace_1037259
  have hstable : (prefixWord ++ tailWord_1037259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037259).length < 2 ^ (prefixWord ++ tailWord_1037259).sum := by decide
  have hdescent : baseEnd_1037259 < baseStart_1037259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037302 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1037302 : Nat := 118140960795 + 1037302 * 2 ^ 59
def prefixEnd_1037302 : Nat := 4983230072969 + 3 ^ 40 * 1037302 * 2
def baseEnd_1037302 : Nat := 177544836623401928284847

theorem tailTrace_1037302 : CollatzResearch.WordTrace tailWord_1037302 prefixEnd_1037302 177544836623401928284847 := by
  unfold tailWord_1037302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364594505502467870157135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25222341392026323948342773 2364594505502467870157135)
  ·
    refine ⟨3546891758253701805235703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364594505502467870157135 3546891758253701805235703)
    ·
      refine ⟨5320337637380552707853555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546891758253701805235703 5320337637380552707853555)
      ·
        refine ⟨7980506456070829061780333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320337637380552707853555 7980506456070829061780333)
        ·
          refine ⟨2992689921026560898167625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7980506456070829061780333 2992689921026560898167625)
          ·
            refine ⟨2244517440769920673625719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992689921026560898167625 2244517440769920673625719)
            ·
              refine ⟨3366776161154881010438579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244517440769920673625719 3366776161154881010438579)
              ·
                refine ⟨5050164241732321515657869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366776161154881010438579 5050164241732321515657869)
                ·
                  refine ⟨1893811590649620568371701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5050164241732321515657869 1893811590649620568371701)
                  ·
                    refine ⟨177544836623401928284847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1893811590649620568371701 177544836623401928284847)
                    ·
                      rfl

theorem cell23_1037302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1037302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037302 prefixEnd_1037302 := by exact prefixLift 1037302
  have htrace : WordTrace (prefixWord ++ tailWord_1037302) baseStart_1037302 baseEnd_1037302 := by
    simpa [prefixWord, tailWord_1037302, baseEnd_1037302] using wordTrace_append hprefix tailTrace_1037302
  have hstable : (prefixWord ++ tailWord_1037302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037302).length < 2 ^ (prefixWord ++ tailWord_1037302).sum := by decide
  have hdescent : baseEnd_1037302 < baseStart_1037302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037305 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_1037305 : Nat := 118140960795 + 1037305 * 2 ^ 59
def prefixEnd_1037305 : Nat := 4983230072969 + 3 ^ 40 * 1037305 * 2
def baseEnd_1037305 : Nat := 532636050312169273117027

theorem tailTrace_1037305 : CollatzResearch.WordTrace tailWord_1037305 prefixEnd_1037305 532636050312169273117027 := by
  unfold tailWord_1037305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37833621507028617434873369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25222414338019078289915579 37833621507028617434873369)
  ·
    refine ⟨28375216130271463076155027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37833621507028617434873369 28375216130271463076155027)
    ·
      refine ⟨42562824195407194614232541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28375216130271463076155027 42562824195407194614232541)
      ·
        refine ⟨15961059073277697980337203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42562824195407194614232541 15961059073277697980337203)
        ·
          refine ⟨23941588609916546970505805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15961059073277697980337203 23941588609916546970505805)
          ·
            refine ⟨8978095728718705113939677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23941588609916546970505805 8978095728718705113939677)
            ·
              refine ⟨3366785898269514417727379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8978095728718705113939677 3366785898269514417727379)
              ·
                refine ⟨5050178847404271626591069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366785898269514417727379 5050178847404271626591069)
                ·
                  refine ⟨1893817067776601859971651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5050178847404271626591069 1893817067776601859971651)
                  ·
                    refine ⟨2840725601664902789957477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1893817067776601859971651 2840725601664902789957477)
                    ·
                      refine ⟨532636050312169273117027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2840725601664902789957477 532636050312169273117027)
                      ·
                        rfl

theorem cell23_1037305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_1037305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037305 prefixEnd_1037305 := by exact prefixLift 1037305
  have htrace : WordTrace (prefixWord ++ tailWord_1037305) baseStart_1037305 baseEnd_1037305 := by
    simpa [prefixWord, tailWord_1037305, baseEnd_1037305] using wordTrace_append hprefix tailTrace_1037305
  have hstable : (prefixWord ++ tailWord_1037305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037305).length < 2 ^ (prefixWord ++ tailWord_1037305).sum := by decide
  have hdescent : baseEnd_1037305 < baseStart_1037305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037333 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_1037333 : Nat := 118140960795 + 1037333 * 2 ^ 59
def prefixEnd_1037333 : Nat := 4983230072969 + 3 ^ 40 * 1037333 * 2
def baseEnd_1037333 : Nat := 532650427770495163566899

theorem tailTrace_1037333 : CollatzResearch.WordTrace tailWord_1037333 prefixEnd_1037333 532650427770495163566899 := by
  unfold tailWord_1037333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834642750927178216892653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25223095167284785477928435 37834642750927178216892653)
  ·
    refine ⟨14187991031597691831334745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37834642750927178216892653 14187991031597691831334745)
    ·
      refine ⟨10640993273698268873501059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14187991031597691831334745 10640993273698268873501059)
      ·
        refine ⟨15961489910547403310251589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640993273698268873501059 15961489910547403310251589)
        ·
          refine ⟨2992779358227638120672173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15961489910547403310251589 2992779358227638120672173)
          ·
            refine ⟨1122292259335364295252065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2992779358227638120672173 1122292259335364295252065)
            ·
              refine ⟨841719194501523221439049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122292259335364295252065 841719194501523221439049)
              ·
                refine ⟨631289395876142416079287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841719194501523221439049 631289395876142416079287)
                ·
                  refine ⟨946934093814213624118931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631289395876142416079287 946934093814213624118931)
                  ·
                    refine ⟨1420401140721320436178397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 946934093814213624118931 1420401140721320436178397)
                    ·
                      refine ⟨532650427770495163566899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1420401140721320436178397 532650427770495163566899)
                      ·
                        rfl

theorem cell23_1037333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_1037333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037333 prefixEnd_1037333 := by exact prefixLift 1037333
  have htrace : WordTrace (prefixWord ++ tailWord_1037333) baseStart_1037333 baseEnd_1037333 := by
    simpa [prefixWord, tailWord_1037333, baseEnd_1037333] using wordTrace_append hprefix tailTrace_1037333
  have hstable : (prefixWord ++ tailWord_1037333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037333).length < 2 ^ (prefixWord ++ tailWord_1037333).sum := by decide
  have hdescent : baseEnd_1037333 < baseStart_1037333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037345 : List Nat := [1, 2, 3, 2, 3, 1, 3, 8]
def baseStart_1037345 : Nat := 118140960795 + 1037345 * 2 ^ 59
def prefixEnd_1037345 : Nat := 4983230072969 + 3 ^ 40 * 1037345 * 2
def baseEnd_1037345 : Nat := 19728021834753670985809

theorem tailTrace_1037345 : CollatzResearch.WordTrace tailWord_1037345 prefixEnd_1037345 19728021834753670985809 := by
  unfold tailWord_1037345
  simp only [CollatzResearch.WordTrace]
  refine ⟨37835080426883704266329489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25223386951255802844219659 37835080426883704266329489)
  ·
    refine ⟨28376310320162778199747117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37835080426883704266329489 28376310320162778199747117)
    ·
      refine ⟨10641116370061041824905169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28376310320162778199747117 10641116370061041824905169)
      ·
        refine ⟨7980837277545781368678877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10641116370061041824905169 7980837277545781368678877)
        ·
          refine ⟨2992813979079668013254579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7980837277545781368678877 2992813979079668013254579)
          ·
            refine ⟨4489220968619502019881869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992813979079668013254579 4489220968619502019881869)
            ·
              refine ⟨1683457863232313257455701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4489220968619502019881869 1683457863232313257455701)
              ·
                refine ⟨19728021834753670985809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1683457863232313257455701 19728021834753670985809)
                ·
                  rfl

theorem cell23_1037345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 8].length) (baseStart_1037345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037345 prefixEnd_1037345 := by exact prefixLift 1037345
  have htrace : WordTrace (prefixWord ++ tailWord_1037345) baseStart_1037345 baseEnd_1037345 := by
    simpa [prefixWord, tailWord_1037345, baseEnd_1037345] using wordTrace_append hprefix tailTrace_1037345
  have hstable : (prefixWord ++ tailWord_1037345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037345).length < 2 ^ (prefixWord ++ tailWord_1037345).sum := by decide
  have hdescent : baseEnd_1037345 < baseStart_1037345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037372 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_1037372 : Nat := 118140960795 + 1037372 * 2 ^ 59
def prefixEnd_1037372 : Nat := 4983230072969 + 3 ^ 40 * 1037372 * 2
def baseEnd_1037372 : Nat := 532670453516020510979219

theorem tailTrace_1037372 : CollatzResearch.WordTrace tailWord_1037372 prefixEnd_1037372 532670453516020510979219 := by
  unfold tailWord_1037372
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918032598892943938781185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25224043465190591918374913 18918032598892943938781185)
  ·
    refine ⟨14188524449169707954085889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18918032598892943938781185 14188524449169707954085889)
    ·
      refine ⟨10641393336877280965564417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14188524449169707954085889 10641393336877280965564417)
      ·
        refine ⟨7981045002657960724173313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10641393336877280965564417 7981045002657960724173313)
        ·
          refine ⟨5985783751993470543129985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7981045002657960724173313 5985783751993470543129985)
          ·
            refine ⟨4489337813995102907347489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5985783751993470543129985 4489337813995102907347489)
            ·
              refine ⟨3367003360496327180510617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489337813995102907347489 3367003360496327180510617)
              ·
                refine ⟨2525252520372245385382963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367003360496327180510617 2525252520372245385382963)
                ·
                  refine ⟨3787878780558368078074445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525252520372245385382963 3787878780558368078074445)
                  ·
                    refine ⟨1420454542709388029277917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787878780558368078074445 1420454542709388029277917)
                    ·
                      refine ⟨532670453516020510979219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1420454542709388029277917 532670453516020510979219)
                      ·
                        rfl

theorem cell23_1037372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_1037372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037372 prefixEnd_1037372 := by exact prefixLift 1037372
  have htrace : WordTrace (prefixWord ++ tailWord_1037372) baseStart_1037372 baseEnd_1037372 := by
    simpa [prefixWord, tailWord_1037372, baseEnd_1037372] using wordTrace_append hprefix tailTrace_1037372
  have hstable : (prefixWord ++ tailWord_1037372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037372).length < 2 ^ (prefixWord ++ tailWord_1037372).sum := by decide
  have hdescent : baseEnd_1037372 < baseStart_1037372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037373 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1037373 : Nat := 118140960795 + 1037373 * 2 ^ 59
def prefixEnd_1037373 : Nat := 4983230072969 + 3 ^ 40 * 1037373 * 2
def baseEnd_1037373 : Nat := 532670966996675007066715

theorem tailTrace_1037373 : CollatzResearch.WordTrace tailWord_1037373 prefixEnd_1037373 532670966996675007066715 := by
  unfold tailWord_1037373
  simp only [CollatzResearch.WordTrace]
  refine ⟨37836101670782265048348773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25224067780521510032232515 37836101670782265048348773)
  ·
    refine ⟨7094269063271674696565395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37836101670782265048348773 7094269063271674696565395)
    ·
      refine ⟨10641403594907512044848093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7094269063271674696565395 10641403594907512044848093)
      ·
        refine ⟨3990526348090317016818035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10641403594907512044848093 3990526348090317016818035)
        ·
          refine ⟨5985789522135475525227053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990526348090317016818035 5985789522135475525227053)
          ·
            refine ⟨2244671070800803321960145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5985789522135475525227053 2244671070800803321960145)
            ·
              refine ⟨1683503303100602491470109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244671070800803321960145 1683503303100602491470109)
              ·
                refine ⟨631313738662725934301291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683503303100602491470109 631313738662725934301291)
                ·
                  refine ⟨946970607994088901451937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631313738662725934301291 946970607994088901451937)
                  ·
                    refine ⟨710227955995566676088953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946970607994088901451937 710227955995566676088953)
                    ·
                      refine ⟨532670966996675007066715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710227955995566676088953 532670966996675007066715)
                      ·
                        rfl

theorem cell23_1037373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1037373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037373 prefixEnd_1037373 := by exact prefixLift 1037373
  have htrace : WordTrace (prefixWord ++ tailWord_1037373) baseStart_1037373 baseEnd_1037373 := by
    simpa [prefixWord, tailWord_1037373, baseEnd_1037373] using wordTrace_append hprefix tailTrace_1037373
  have hstable : (prefixWord ++ tailWord_1037373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037373).length < 2 ^ (prefixWord ++ tailWord_1037373).sum := by decide
  have hdescent : baseEnd_1037373 < baseStart_1037373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037425 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_1037425 : Nat := 118140960795 + 1037425 * 2 ^ 59
def prefixEnd_1037425 : Nat := 4983230072969 + 3 ^ 40 * 1037425 * 2
def baseEnd_1037425 : Nat := 532697667990708803616475

theorem tailTrace_1037425 : CollatzResearch.WordTrace tailWord_1037425 prefixEnd_1037425 532697667990708803616475 := by
  unfold tailWord_1037425
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837998266593877929241729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25225332177729251952827819 37837998266593877929241729)
  ·
    refine ⟨28378498699945408446931297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37837998266593877929241729 28378498699945408446931297)
    ·
      refine ⟨21283874024959056335198473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28378498699945408446931297 21283874024959056335198473)
      ·
        refine ⟨15962905518719292251398855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21283874024959056335198473 15962905518719292251398855)
        ·
          refine ⟨23944358278078938377098283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962905518719292251398855 23944358278078938377098283)
          ·
            refine ⟨35916537417118407565647425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23944358278078938377098283 35916537417118407565647425)
            ·
              refine ⟨26937403062838805674235569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35916537417118407565647425 26937403062838805674235569)
              ·
                refine ⟨20203052297129104255676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26937403062838805674235569 20203052297129104255676677)
                ·
                  refine ⟨3788072305711707047939377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20203052297129104255676677 3788072305711707047939377)
                  ·
                    refine ⟨2841054229283780285954533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3788072305711707047939377 2841054229283780285954533)
                    ·
                      refine ⟨532697667990708803616475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2841054229283780285954533 532697667990708803616475)
                      ·
                        rfl

theorem cell23_1037425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_1037425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037425 prefixEnd_1037425 := by exact prefixLift 1037425
  have htrace : WordTrace (prefixWord ++ tailWord_1037425) baseStart_1037425 baseEnd_1037425 := by
    simpa [prefixWord, tailWord_1037425, baseEnd_1037425] using wordTrace_append hprefix tailTrace_1037425
  have hstable : (prefixWord ++ tailWord_1037425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037425).length < 2 ^ (prefixWord ++ tailWord_1037425).sum := by decide
  have hdescent : baseEnd_1037425 < baseStart_1037425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037452 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 5]
def baseStart_1037452 : Nat := 118140960795 + 1037452 * 2 ^ 59
def prefixEnd_1037452 : Nat := 4983230072969 + 3 ^ 40 * 1037452 * 2
def baseEnd_1037452 : Nat := 59190170218708910886539

theorem tailTrace_1037452 : CollatzResearch.WordTrace tailWord_1037452 prefixEnd_1037452 59190170218708910886539 := by
  unfold tailWord_1037452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18919491518748030770237305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25225988691664041026983073 18919491518748030770237305)
  ·
    refine ⟨14189618639061023077677979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18919491518748030770237305 14189618639061023077677979)
    ·
      refine ⟨21284427958591534616516969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14189618639061023077677979 21284427958591534616516969)
      ·
        refine ⟨15963320968943650962387727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21284427958591534616516969 15963320968943650962387727)
        ·
          refine ⟨23944981453415476443581591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15963320968943650962387727 23944981453415476443581591)
          ·
            refine ⟨35917472180123214665372387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23944981453415476443581591 35917472180123214665372387)
            ·
              refine ⟨53876208270184821998058581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35917472180123214665372387 53876208270184821998058581)
              ·
                refine ⟨631361815666228382789749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 53876208270184821998058581 631361815666228382789749)
                ·
                  refine ⟨59190170218708910886539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631361815666228382789749 59190170218708910886539)
                  ·
                    rfl

theorem cell23_1037452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_1037452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037452 prefixEnd_1037452 := by exact prefixLift 1037452
  have htrace : WordTrace (prefixWord ++ tailWord_1037452) baseStart_1037452 baseEnd_1037452 := by
    simpa [prefixWord, tailWord_1037452, baseEnd_1037452] using wordTrace_append hprefix tailTrace_1037452
  have hstable : (prefixWord ++ tailWord_1037452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037452).length < 2 ^ (prefixWord ++ tailWord_1037452).sum := by decide
  have hdescent : baseEnd_1037452 < baseStart_1037452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037463 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_1037463 : Nat := 118140960795 + 1037463 * 2 ^ 59
def prefixEnd_1037463 : Nat := 4983230072969 + 3 ^ 40 * 1037463 * 2
def baseEnd_1037463 : Nat := 532717180255579654941301

theorem tailTrace_1037463 : CollatzResearch.WordTrace tailWord_1037463 prefixEnd_1037463 532717180255579654941301 := by
  unfold tailWord_1037463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839384240456210419125043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25226256160304140279416695 37839384240456210419125043)
  ·
    refine ⟨56759076360684315628687565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37839384240456210419125043 56759076360684315628687565)
    ·
      refine ⟨21284653635256618360757837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56759076360684315628687565 21284653635256618360757837)
      ·
        refine ⟨7981745113221231885284189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21284653635256618360757837 7981745113221231885284189)
        ·
          refine ⟨2993154417457961956981571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7981745113221231885284189 2993154417457961956981571)
          ·
            refine ⟨4489731626186942935472357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993154417457961956981571 4489731626186942935472357)
            ·
              refine ⟨841824679910051800401067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4489731626186942935472357 841824679910051800401067)
              ·
                refine ⟨1262737019865077700601601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841824679910051800401067 1262737019865077700601601)
                ·
                  refine ⟨947052764898808275451201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262737019865077700601601 947052764898808275451201)
                  ·
                    refine ⟨710289573674106206588401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947052764898808275451201 710289573674106206588401)
                    ·
                      refine ⟨532717180255579654941301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710289573674106206588401 532717180255579654941301)
                      ·
                        rfl

theorem cell23_1037463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_1037463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037463 prefixEnd_1037463 := by exact prefixLift 1037463
  have htrace : WordTrace (prefixWord ++ tailWord_1037463) baseStart_1037463 baseEnd_1037463 := by
    simpa [prefixWord, tailWord_1037463, baseEnd_1037463] using wordTrace_append hprefix tailTrace_1037463
  have hstable : (prefixWord ++ tailWord_1037463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037463).length < 2 ^ (prefixWord ++ tailWord_1037463).sum := by decide
  have hdescent : baseEnd_1037463 < baseStart_1037463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037515 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_1037515 : Nat := 118140960795 + 1037515 * 2 ^ 59
def prefixEnd_1037515 : Nat := 4983230072969 + 3 ^ 40 * 1037515 * 2
def baseEnd_1037515 : Nat := 532743881249613451491061

theorem tailTrace_1037515 : CollatzResearch.WordTrace tailWord_1037515 prefixEnd_1037515 532743881249613451491061 := by
  unfold tailWord_1037515
  simp only [CollatzResearch.WordTrace]
  refine ⟨37841280836267823300017999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25227520557511882200011999 37841280836267823300017999)
  ·
    refine ⟨56761921254401734950026999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37841280836267823300017999 56761921254401734950026999)
    ·
      refine ⟨85142881881602602425040499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56761921254401734950026999 85142881881602602425040499)
      ·
        refine ⟨127714322822403903637560749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85142881881602602425040499 127714322822403903637560749)
        ·
          refine ⟨47892871058401463864085281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127714322822403903637560749 47892871058401463864085281)
          ·
            refine ⟨35919653293801097898063961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47892871058401463864085281 35919653293801097898063961)
            ·
              refine ⟨26939739970350823423547971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35919653293801097898063961 26939739970350823423547971)
              ·
                refine ⟨40409609955526235135321957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26939739970350823423547971 40409609955526235135321957)
                ·
                  refine ⟨7576801866661169087872867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40409609955526235135321957 7576801866661169087872867)
                  ·
                    refine ⟨11365202799991753631809301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576801866661169087872867 11365202799991753631809301)
                    ·
                      refine ⟨532743881249613451491061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11365202799991753631809301 532743881249613451491061)
                      ·
                        rfl

theorem cell23_1037515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_1037515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037515 prefixEnd_1037515 := by exact prefixLift 1037515
  have htrace : WordTrace (prefixWord ++ tailWord_1037515) baseStart_1037515 baseEnd_1037515 := by
    simpa [prefixWord, tailWord_1037515, baseEnd_1037515] using wordTrace_append hprefix tailTrace_1037515
  have hstable : (prefixWord ++ tailWord_1037515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037515).length < 2 ^ (prefixWord ++ tailWord_1037515).sum := by decide
  have hdescent : baseEnd_1037515 < baseStart_1037515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037533 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1037533 : Nat := 118140960795 + 1037533 * 2 ^ 59
def prefixEnd_1037533 : Nat := 4983230072969 + 3 ^ 40 * 1037533 * 2
def baseEnd_1037533 : Nat := 177584374633798127021993

theorem tailTrace_1037533 : CollatzResearch.WordTrace tailWord_1037533 prefixEnd_1037533 177584374633798127021993 := by
  unfold tailWord_1037533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37841937350202612374173253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25227958233468408249448835 37841937350202612374173253)
  ·
    refine ⟨7095363253162989820157485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37841937350202612374173253 7095363253162989820157485)
    ·
      refine ⟨2660761219936121182559057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7095363253162989820157485 2660761219936121182559057)
      ·
        refine ⟨1995570914952090886919293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2660761219936121182559057 1995570914952090886919293)
        ·
          refine ⟨748339093107034082594735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1995570914952090886919293 748339093107034082594735)
          ·
            refine ⟨1122508639660551123892103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748339093107034082594735 1122508639660551123892103)
            ·
              refine ⟨1683762959490826685838155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122508639660551123892103 1683762959490826685838155)
              ·
                refine ⟨2525644439236240028757233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683762959490826685838155 2525644439236240028757233)
                ·
                  refine ⟨1894233329427180021567925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2525644439236240028757233 1894233329427180021567925)
                  ·
                    refine ⟨177584374633798127021993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1894233329427180021567925 177584374633798127021993)
                    ·
                      rfl

theorem cell23_1037533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1037533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037533 prefixEnd_1037533 := by exact prefixLift 1037533
  have htrace : WordTrace (prefixWord ++ tailWord_1037533) baseStart_1037533 baseEnd_1037533 := by
    simpa [prefixWord, tailWord_1037533, baseEnd_1037533] using wordTrace_append hprefix tailTrace_1037533
  have hstable : (prefixWord ++ tailWord_1037533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037533).length < 2 ^ (prefixWord ++ tailWord_1037533).sum := by decide
  have hdescent : baseEnd_1037533 < baseStart_1037533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037545 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_1037545 : Nat := 118140960795 + 1037545 * 2 ^ 59
def prefixEnd_1037545 : Nat := 4983230072969 + 3 ^ 40 * 1037545 * 2
def baseEnd_1037545 : Nat := 532759285669248334115923

theorem tailTrace_1037545 : CollatzResearch.WordTrace tailWord_1037545 prefixEnd_1037545 532759285669248334115923 := by
  unfold tailWord_1037545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37842375026159138423610089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25228250017439425615740059 37842375026159138423610089)
  ·
    refine ⟨28381781269619353817707567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37842375026159138423610089 28381781269619353817707567)
    ·
      refine ⟨42572671904429030726561351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28381781269619353817707567 42572671904429030726561351)
      ·
        refine ⟨63859007856643546089842027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42572671904429030726561351 63859007856643546089842027)
        ·
          refine ⟨95788511784965319134763041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63859007856643546089842027 95788511784965319134763041)
          ·
            refine ⟨71841383838723989351072281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95788511784965319134763041 71841383838723989351072281)
            ·
              refine ⟨53881037879042992013304211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71841383838723989351072281 53881037879042992013304211)
              ·
                refine ⟨80821556818564488019956317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53881037879042992013304211 80821556818564488019956317)
                ·
                  refine ⟨30308083806961683007483619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80821556818564488019956317 30308083806961683007483619)
                  ·
                    refine ⟨45462125710442524511225429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30308083806961683007483619 45462125710442524511225429)
                    ·
                      refine ⟨532759285669248334115923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45462125710442524511225429 532759285669248334115923)
                      ·
                        rfl

theorem cell23_1037545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_1037545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037545 prefixEnd_1037545 := by exact prefixLift 1037545
  have htrace : WordTrace (prefixWord ++ tailWord_1037545) baseStart_1037545 baseEnd_1037545 := by
    simpa [prefixWord, tailWord_1037545, baseEnd_1037545] using wordTrace_append hprefix tailTrace_1037545
  have hstable : (prefixWord ++ tailWord_1037545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037545).length < 2 ^ (prefixWord ++ tailWord_1037545).sum := by decide
  have hdescent : baseEnd_1037545 < baseStart_1037545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037546 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1037546 : Nat := 118140960795 + 1037546 * 2 ^ 59
def prefixEnd_1037546 : Nat := 4983230072969 + 3 ^ 40 * 1037546 * 2
def baseEnd_1037546 : Nat := 177586599716634276734473

theorem tailTrace_1037546 : CollatzResearch.WordTrace tailWord_1037546 prefixEnd_1037546 177586599716634276734473 := by
  unfold tailWord_1037546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460602874788878898599123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25228274332770343729597661 9460602874788878898599123)
  ·
    refine ⟨14190904312183318347898685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9460602874788878898599123 14190904312183318347898685)
    ·
      refine ⟨5321589117068744380462007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14190904312183318347898685 5321589117068744380462007)
      ·
        refine ⟨7982383675603116570693011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321589117068744380462007 7982383675603116570693011)
        ·
          refine ⟨11973575513404674856039517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982383675603116570693011 11973575513404674856039517)
          ·
            refine ⟨4490090817526753071014819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11973575513404674856039517 4490090817526753071014819)
            ·
              refine ⟨6735136226290129606522229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490090817526753071014819 6735136226290129606522229)
              ·
                refine ⟨631419021214699650611459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6735136226290129606522229 631419021214699650611459)
                ·
                  refine ⟨947128531822049475917189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631419021214699650611459 947128531822049475917189)
                  ·
                    refine ⟨177586599716634276734473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947128531822049475917189 177586599716634276734473)
                    ·
                      rfl

theorem cell23_1037546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1037546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037546 prefixEnd_1037546 := by exact prefixLift 1037546
  have htrace : WordTrace (prefixWord ++ tailWord_1037546) baseStart_1037546 baseEnd_1037546 := by
    simpa [prefixWord, tailWord_1037546, baseEnd_1037546] using wordTrace_append hprefix tailTrace_1037546
  have hstable : (prefixWord ++ tailWord_1037546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037546).length < 2 ^ (prefixWord ++ tailWord_1037546).sum := by decide
  have hdescent : baseEnd_1037546 < baseStart_1037546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037576 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 6]
def baseStart_1037576 : Nat := 118140960795 + 1037576 * 2 ^ 59
def prefixEnd_1037576 : Nat := 4983230072969 + 3 ^ 40 * 1037576 * 2
def baseEnd_1037576 : Nat := 59197244841059745869809

theorem tailTrace_1037576 : CollatzResearch.WordTrace tailWord_1037576 prefixEnd_1037576 59197244841059745869809 := by
  unfold tailWord_1037576
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921752844523415358994291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25229003792697887145325721 18921752844523415358994291)
  ·
    refine ⟨28382629266785123038491437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18921752844523415358994291 28382629266785123038491437)
    ·
      refine ⟨10643485975044421139434289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28382629266785123038491437 10643485975044421139434289)
      ·
        refine ⟨7982614481283315854575717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10643485975044421139434289 7982614481283315854575717)
        ·
          refine ⟨1496740215240621722732947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7982614481283315854575717 1496740215240621722732947)
          ·
            refine ⟨2245110322860932584099421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496740215240621722732947 2245110322860932584099421)
            ·
              refine ⟨841916371072849719037283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245110322860932584099421 841916371072849719037283)
              ·
                refine ⟨1262874556609274578555925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841916371072849719037283 1262874556609274578555925)
                ·
                  refine ⟨59197244841059745869809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1262874556609274578555925 59197244841059745869809)
                  ·
                    rfl

theorem cell23_1037576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 6].length) (baseStart_1037576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037576 prefixEnd_1037576 := by exact prefixLift 1037576
  have htrace : WordTrace (prefixWord ++ tailWord_1037576) baseStart_1037576 baseEnd_1037576 := by
    simpa [prefixWord, tailWord_1037576, baseEnd_1037576] using wordTrace_append hprefix tailTrace_1037576
  have hstable : (prefixWord ++ tailWord_1037576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037576).length < 2 ^ (prefixWord ++ tailWord_1037576).sum := by decide
  have hdescent : baseEnd_1037576 < baseStart_1037576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037579 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 5, 2]
def baseStart_1037579 : Nat := 118140960795 + 1037579 * 2 ^ 59
def prefixEnd_1037579 : Nat := 4983230072969 + 3 ^ 40 * 1037579 * 2
def baseEnd_1037579 : Nat := 532776744011501201090767

theorem tailTrace_1037579 : CollatzResearch.WordTrace tailWord_1037579 prefixEnd_1037579 532776744011501201090767 := by
  unfold tailWord_1037579
  simp only [CollatzResearch.WordTrace]
  refine ⟨37843615108035962230347791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25229076738690641486898527 37843615108035962230347791)
  ·
    refine ⟨56765422662053943345521687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37843615108035962230347791 56765422662053943345521687)
    ·
      refine ⟨85148133993080915018282531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56765422662053943345521687 85148133993080915018282531)
      ·
        refine ⟨127722200989621372527423797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85148133993080915018282531 127722200989621372527423797)
        ·
          refine ⟨11973956342777003674445981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127722200989621372527423797 11973956342777003674445981)
          ·
            refine ⟨4490233628541376377917243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11973956342777003674445981 4490233628541376377917243)
            ·
              refine ⟨6735350442812064566875865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490233628541376377917243 6735350442812064566875865)
              ·
                refine ⟨5051512832109048425156899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6735350442812064566875865 5051512832109048425156899)
                ·
                  refine ⟨7577269248163572637735349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051512832109048425156899 7577269248163572637735349)
                  ·
                    refine ⟨710368992015334934787689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7577269248163572637735349 710368992015334934787689)
                    ·
                      refine ⟨532776744011501201090767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710368992015334934787689 532776744011501201090767)
                      ·
                        rfl

theorem cell23_1037579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5, 2].length) (baseStart_1037579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037579 prefixEnd_1037579 := by exact prefixLift 1037579
  have htrace : WordTrace (prefixWord ++ tailWord_1037579) baseStart_1037579 baseEnd_1037579 := by
    simpa [prefixWord, tailWord_1037579, baseEnd_1037579] using wordTrace_append hprefix tailTrace_1037579
  have hstable : (prefixWord ++ tailWord_1037579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037579).length < 2 ^ (prefixWord ++ tailWord_1037579).sum := by decide
  have hdescent : baseEnd_1037579 < baseStart_1037579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037603 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 1, 1, 3]
def baseStart_1037603 : Nat := 118140960795 + 1037603 * 2 ^ 59
def prefixEnd_1037603 : Nat := 4983230072969 + 3 ^ 40 * 1037603 * 2
def baseEnd_1037603 : Nat := 532789067547209107190657

theorem tailTrace_1037603 : CollatzResearch.WordTrace tailWord_1037603 prefixEnd_1037603 532789067547209107190657 := by
  unfold tailWord_1037603
  simp only [CollatzResearch.WordTrace]
  refine ⟨37844490459949014329221463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25229660306632676219480975 37844490459949014329221463)
  ·
    refine ⟨56766735689923521493832195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37844490459949014329221463 56766735689923521493832195)
    ·
      refine ⟨85150103534885282240748293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56766735689923521493832195 85150103534885282240748293)
      ·
        refine ⟨15965644412790990420140305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85150103534885282240748293 15965644412790990420140305)
        ·
          refine ⟨11974233309593242815105229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15965644412790990420140305 11974233309593242815105229)
          ·
            refine ⟨4490337491097466055664461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11974233309593242815105229 4490337491097466055664461)
            ·
              refine ⟨1683876559161549770874173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4490337491097466055664461 1683876559161549770874173)
              ·
                refine ⟨631453709685581164077815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683876559161549770874173 631453709685581164077815)
                ·
                  refine ⟨947180564528371746116723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631453709685581164077815 947180564528371746116723)
                  ·
                    refine ⟨1420770846792557619175085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 947180564528371746116723 1420770846792557619175085)
                    ·
                      refine ⟨532789067547209107190657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1420770846792557619175085 532789067547209107190657)
                      ·
                        rfl

theorem cell23_1037603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_1037603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037603 prefixEnd_1037603 := by exact prefixLift 1037603
  have htrace : WordTrace (prefixWord ++ tailWord_1037603) baseStart_1037603 baseEnd_1037603 := by
    simpa [prefixWord, tailWord_1037603, baseEnd_1037603] using wordTrace_append hprefix tailTrace_1037603
  have hstable : (prefixWord ++ tailWord_1037603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037603).length < 2 ^ (prefixWord ++ tailWord_1037603).sum := by decide
  have hdescent : baseEnd_1037603 < baseStart_1037603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037613 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1037613 : Nat := 118140960795 + 1037613 * 2 ^ 59
def prefixEnd_1037613 : Nat := 4983230072969 + 3 ^ 40 * 1037613 * 2
def baseEnd_1037613 : Nat := 532794202353754068065611

theorem tailTrace_1037613 : CollatzResearch.WordTrace tailWord_1037613 prefixEnd_1037613 532794202353754068065611 := by
  unfold tailWord_1037613
  simp only [CollatzResearch.WordTrace]
  refine ⟨37844855189912786037085493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25229903459941857358056995 37844855189912786037085493)
  ·
    refine ⟨3547955174054323690976765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37844855189912786037085493 3547955174054323690976765)
    ·
      refine ⟨1330483190270371384116287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3547955174054323690976765 1330483190270371384116287)
      ·
        refine ⟨1995724785405557076174431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330483190270371384116287 1995724785405557076174431)
        ·
          refine ⟨2993587178108335614261647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995724785405557076174431 2993587178108335614261647)
          ·
            refine ⟨4490380767162503421392471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993587178108335614261647 4490380767162503421392471)
            ·
              refine ⟨6735571150743755132088707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490380767162503421392471 6735571150743755132088707)
              ·
                refine ⟨10103356726115632698133061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735571150743755132088707 10103356726115632698133061)
                ·
                  refine ⟨1894379386146681130899949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10103356726115632698133061 1894379386146681130899949)
                  ·
                    refine ⟨710392269805005424087481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894379386146681130899949 710392269805005424087481)
                    ·
                      refine ⟨532794202353754068065611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710392269805005424087481 532794202353754068065611)
                      ·
                        rfl

theorem cell23_1037613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1037613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037613 prefixEnd_1037613 := by exact prefixLift 1037613
  have htrace : WordTrace (prefixWord ++ tailWord_1037613) baseStart_1037613 baseEnd_1037613 := by
    simpa [prefixWord, tailWord_1037613, baseEnd_1037613] using wordTrace_append hprefix tailTrace_1037613
  have hstable : (prefixWord ++ tailWord_1037613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037613).length < 2 ^ (prefixWord ++ tailWord_1037613).sum := by decide
  have hdescent : baseEnd_1037613 < baseStart_1037613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037619 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 4, 4]
def baseStart_1037619 : Nat := 118140960795 + 1037619 * 2 ^ 59
def prefixEnd_1037619 : Nat := 4983230072969 + 3 ^ 40 * 1037619 * 2
def baseEnd_1037619 : Nat := 177599094412560348196861

theorem tailTrace_1037619 : CollatzResearch.WordTrace tailWord_1037619 prefixEnd_1037619 177599094412560348196861 := by
  unfold tailWord_1037619
  simp only [CollatzResearch.WordTrace]
  refine ⟨37845074027891049061803911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25230049351927366041202607 37845074027891049061803911)
  ·
    refine ⟨56767611041836573592705867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37845074027891049061803911 56767611041836573592705867)
    ·
      refine ⟨85151416562754860389058801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56767611041836573592705867 85151416562754860389058801)
      ·
        refine ⟨63863562422066145291794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85151416562754860389058801 63863562422066145291794101)
        ·
          refine ⟨5987208977068701121105697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63863562422066145291794101 5987208977068701121105697)
          ·
            refine ⟨4490406732801525840829273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987208977068701121105697 4490406732801525840829273)
            ·
              refine ⟨3367805049601144380621955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490406732801525840829273 3367805049601144380621955)
              ·
                refine ⟨5051707574401716570932933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367805049601144380621955 5051707574401716570932933)
                ·
                  refine ⟨947195170200321857049925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5051707574401716570932933 947195170200321857049925)
                  ·
                    refine ⟨177599094412560348196861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947195170200321857049925 177599094412560348196861)
                    ·
                      rfl

theorem cell23_1037619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 4].length) (baseStart_1037619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037619 prefixEnd_1037619 := by exact prefixLift 1037619
  have htrace : WordTrace (prefixWord ++ tailWord_1037619) baseStart_1037619 baseEnd_1037619 := by
    simpa [prefixWord, tailWord_1037619, baseEnd_1037619] using wordTrace_append hprefix tailTrace_1037619
  have hstable : (prefixWord ++ tailWord_1037619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037619).length < 2 ^ (prefixWord ++ tailWord_1037619).sum := by decide
  have hdescent : baseEnd_1037619 < baseStart_1037619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037632 : List Nat := [2, 1, 1, 2, 2, 1, 6, 8]
def baseStart_1037632 : Nat := 118140960795 + 1037632 * 2 ^ 59
def prefixEnd_1037632 : Nat := 4983230072969 + 3 ^ 40 * 1037632 * 2
def baseEnd_1037632 : Nat := 19733479943932944212149

theorem tailTrace_1037632 : CollatzResearch.WordTrace tailWord_1037632 prefixEnd_1037632 19733479943932944212149 := by
  unfold tailWord_1037632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922774088421976141013575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25230365451229301521351433 18922774088421976141013575)
  ·
    refine ⟨28384161132632964211520363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922774088421976141013575 28384161132632964211520363)
    ·
      refine ⟨42576241698949446317280545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28384161132632964211520363 42576241698949446317280545)
      ·
        refine ⟨31932181274212084737960409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42576241698949446317280545 31932181274212084737960409)
        ·
          refine ⟨23949135955659063553470307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31932181274212084737960409 23949135955659063553470307)
          ·
            refine ⟨35923703933488595330205461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23949135955659063553470307 35923703933488595330205461)
            ·
              refine ⟨1683923621882277906103381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35923703933488595330205461 1683923621882277906103381)
              ·
                refine ⟨19733479943932944212149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1683923621882277906103381 19733479943932944212149)
                ·
                  rfl

theorem cell23_1037632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 8].length) (baseStart_1037632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037632 prefixEnd_1037632 := by exact prefixLift 1037632
  have htrace : WordTrace (prefixWord ++ tailWord_1037632) baseStart_1037632 baseEnd_1037632 := by
    simpa [prefixWord, tailWord_1037632, baseEnd_1037632] using wordTrace_append hprefix tailTrace_1037632
  have hstable : (prefixWord ++ tailWord_1037632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037632).length < 2 ^ (prefixWord ++ tailWord_1037632).sum := by decide
  have hdescent : baseEnd_1037632 < baseStart_1037632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037677 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1037677 : Nat := 118140960795 + 1037677 * 2 ^ 59
def prefixEnd_1037677 : Nat := 4983230072969 + 3 ^ 40 * 1037677 * 2
def baseEnd_1037677 : Nat := 532827065115641817665317

theorem tailTrace_1037677 : CollatzResearch.WordTrace tailWord_1037677 prefixEnd_1037677 532827065115641817665317 := by
  unfold tailWord_1037677
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847189461680924967415285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25231459641120616644943523 37847189461680924967415285)
  ·
    refine ⟨3548174012032586715695183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37847189461680924967415285 3548174012032586715695183)
    ·
      refine ⟨5322261018048880073542775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548174012032586715695183 5322261018048880073542775)
      ·
        refine ⟨7983391527073320110314163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322261018048880073542775 7983391527073320110314163)
        ·
          refine ⟨11975087290609980165471245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983391527073320110314163 11975087290609980165471245)
          ·
            refine ⟨4490657733978742562051717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11975087290609980165471245 4490657733978742562051717)
            ·
              refine ⟨841998325121014230384697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4490657733978742562051717 841998325121014230384697)
              ·
                refine ⟨631498743840760672788523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841998325121014230384697 631498743840760672788523)
                ·
                  refine ⟨947248115761141009182785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631498743840760672788523 947248115761141009182785)
                  ·
                    refine ⟨710436086820855756887089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947248115761141009182785 710436086820855756887089)
                    ·
                      refine ⟨532827065115641817665317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710436086820855756887089 532827065115641817665317)
                      ·
                        rfl

theorem cell23_1037677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1037677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037677 prefixEnd_1037677 := by exact prefixLift 1037677
  have htrace : WordTrace (prefixWord ++ tailWord_1037677) baseStart_1037677 baseEnd_1037677 := by
    simpa [prefixWord, tailWord_1037677, baseEnd_1037677] using wordTrace_append hprefix tailTrace_1037677
  have hstable : (prefixWord ++ tailWord_1037677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037677).length < 2 ^ (prefixWord ++ tailWord_1037677).sum := by decide
  have hdescent : baseEnd_1037677 < baseStart_1037677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037714 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1037714 : Nat := 118140960795 + 1037714 * 2 ^ 59
def prefixEnd_1037714 : Nat := 4983230072969 + 3 ^ 40 * 1037714 * 2
def baseEnd_1037714 : Nat := 532846063899858172902647

theorem tailTrace_1037714 : CollatzResearch.WordTrace tailWord_1037714 prefixEnd_1037714 532846063899858172902647 := by
  unfold tailWord_1037714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462134740636720071628049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25232359308364586857674797 9462134740636720071628049)
  ·
    refine ⟨7096601055477540053721037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9462134740636720071628049 7096601055477540053721037)
    ·
      refine ⟨2661225395804077520145389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7096601055477540053721037 2661225395804077520145389)
      ·
        refine ⟨997959523426529070054521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2661225395804077520145389 997959523426529070054521)
        ·
          refine ⟨748469642569896802540891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997959523426529070054521 748469642569896802540891)
          ·
            refine ⟨1122704463854845203811337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748469642569896802540891 1122704463854845203811337)
            ·
              refine ⟨842028347891133902858503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122704463854845203811337 842028347891133902858503)
              ·
                refine ⟨1263042521836700854287755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842028347891133902858503 1263042521836700854287755)
                ·
                  refine ⟨1894563782755051281431633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263042521836700854287755 1894563782755051281431633)
                  ·
                    refine ⟨1420922837066288461073725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1894563782755051281431633 1420922837066288461073725)
                    ·
                      refine ⟨532846063899858172902647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1420922837066288461073725 532846063899858172902647)
                      ·
                        rfl

theorem cell23_1037714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1037714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037714 prefixEnd_1037714 := by exact prefixLift 1037714
  have htrace : WordTrace (prefixWord ++ tailWord_1037714) baseStart_1037714 baseEnd_1037714 := by
    simpa [prefixWord, tailWord_1037714, baseEnd_1037714] using wordTrace_append hprefix tailTrace_1037714
  have hstable : (prefixWord ++ tailWord_1037714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037714).length < 2 ^ (prefixWord ++ tailWord_1037714).sum := by decide
  have hdescent : baseEnd_1037714 < baseStart_1037714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037720 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1037720 : Nat := 118140960795 + 1037720 * 2 ^ 59
def prefixEnd_1037720 : Nat := 4983230072969 + 3 ^ 40 * 1037720 * 2
def baseEnd_1037720 : Nat := 532849144783785149427619

theorem tailTrace_1037720 : CollatzResearch.WordTrace tailWord_1037720 prefixEnd_1037720 532849144783785149427619 := by
  unfold tailWord_1037720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924378900262571655615307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25232505200350095540820409 18924378900262571655615307)
  ·
    refine ⟨28386568350393857483422961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18924378900262571655615307 28386568350393857483422961)
    ·
      refine ⟨21289926262795393112567221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28386568350393857483422961 21289926262795393112567221)
      ·
        refine ⟨1995930587137068104303177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21289926262795393112567221 1995930587137068104303177)
        ·
          refine ⟨1496947940352801078227383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1995930587137068104303177 1496947940352801078227383)
          ·
            refine ⟨2245421910529201617341075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496947940352801078227383 2245421910529201617341075)
            ·
              refine ⟨3368132865793802426011613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245421910529201617341075 3368132865793802426011613)
              ·
                refine ⟨1263049824672675909754355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3368132865793802426011613 1263049824672675909754355)
                ·
                  refine ⟨1894574737009013864631533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263049824672675909754355 1894574737009013864631533)
                  ·
                    refine ⟨710465526378380199236825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1894574737009013864631533 710465526378380199236825)
                    ·
                      refine ⟨532849144783785149427619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710465526378380199236825 532849144783785149427619)
                      ·
                        rfl

theorem cell23_1037720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1037720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037720 prefixEnd_1037720 := by exact prefixLift 1037720
  have htrace : WordTrace (prefixWord ++ tailWord_1037720) baseStart_1037720 baseEnd_1037720 := by
    simpa [prefixWord, tailWord_1037720, baseEnd_1037720] using wordTrace_append hprefix tailTrace_1037720
  have hstable : (prefixWord ++ tailWord_1037720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037720).length < 2 ^ (prefixWord ++ tailWord_1037720).sum := by decide
  have hdescent : baseEnd_1037720 < baseStart_1037720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037733 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_1037733 : Nat := 118140960795 + 1037733 * 2 ^ 59
def prefixEnd_1037733 : Nat := 4983230072969 + 3 ^ 40 * 1037733 * 2
def baseEnd_1037733 : Nat := 532855820032293598565059

theorem tailTrace_1037733 : CollatzResearch.WordTrace tailWord_1037733 prefixEnd_1037733 532855820032293598565059 := by
  unfold tailWord_1037733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37849231949478046531453853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25232821299652031020969235 37849231949478046531453853)
  ·
    refine ⟨14193461981054267449295195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37849231949478046531453853 14193461981054267449295195)
    ·
      refine ⟨21290192971581401173942793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14193461981054267449295195 21290192971581401173942793)
      ·
        refine ⟨15967644728686050880457095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21290192971581401173942793 15967644728686050880457095)
        ·
          refine ⟨23951467093029076320685643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15967644728686050880457095 23951467093029076320685643)
          ·
            refine ⟨35927200639543614481028465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23951467093029076320685643 35927200639543614481028465)
            ·
              refine ⟨26945400479657710860771349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35927200639543614481028465 26945400479657710860771349)
              ·
                refine ⟨1263065647483955196598657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26945400479657710860771349 1263065647483955196598657)
                ·
                  refine ⟨947299235612966397448993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263065647483955196598657 947299235612966397448993)
                  ·
                    refine ⟨710474426709724798086745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947299235612966397448993 710474426709724798086745)
                    ·
                      refine ⟨532855820032293598565059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710474426709724798086745 532855820032293598565059)
                      ·
                        rfl

theorem cell23_1037733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_1037733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037733 prefixEnd_1037733 := by exact prefixLift 1037733
  have htrace : WordTrace (prefixWord ++ tailWord_1037733) baseStart_1037733 baseEnd_1037733 := by
    simpa [prefixWord, tailWord_1037733, baseEnd_1037733] using wordTrace_append hprefix tailTrace_1037733
  have hstable : (prefixWord ++ tailWord_1037733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037733).length < 2 ^ (prefixWord ++ tailWord_1037733).sum := by decide
  have hdescent : baseEnd_1037733 < baseStart_1037733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037769 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_1037769 : Nat := 118140960795 + 1037769 * 2 ^ 59
def prefixEnd_1037769 : Nat := 4983230072969 + 3 ^ 40 * 1037769 * 2
def baseEnd_1037769 : Nat := 177624768445285152571631

theorem tailTrace_1037769 : CollatzResearch.WordTrace tailWord_1037769 prefixEnd_1037769 177624768445285152571631 := by
  unfold tailWord_1037769
  simp only [CollatzResearch.WordTrace]
  refine ⟨37850544977347624679764361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25233696651565083119842907 37850544977347624679764361)
  ·
    refine ⟨28387908733010718509823271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37850544977347624679764361 28387908733010718509823271)
    ·
      refine ⟨42581863099516077764734907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28387908733010718509823271 42581863099516077764734907)
      ·
        refine ⟨63872794649274116647102361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42581863099516077764734907 63872794649274116647102361)
        ·
          refine ⟨47904595986955587485326771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63872794649274116647102361 47904595986955587485326771)
          ·
            refine ⟨71856893980433381227990157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47904595986955587485326771 71856893980433381227990157)
            ·
              refine ⟨26946335242662517960496309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71856893980433381227990157 26946335242662517960496309)
              ·
                refine ⟨2526218928999611058796529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26946335242662517960496309 2526218928999611058796529)
                ·
                  refine ⟨1894664196749708294097397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526218928999611058796529 1894664196749708294097397)
                  ·
                    refine ⟨177624768445285152571631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1894664196749708294097397 177624768445285152571631)
                    ·
                      rfl

theorem cell23_1037769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_1037769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037769 prefixEnd_1037769 := by exact prefixLift 1037769
  have htrace : WordTrace (prefixWord ++ tailWord_1037769) baseStart_1037769 baseEnd_1037769 := by
    simpa [prefixWord, tailWord_1037769, baseEnd_1037769] using wordTrace_append hprefix tailTrace_1037769
  have hstable : (prefixWord ++ tailWord_1037769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037769).length < 2 ^ (prefixWord ++ tailWord_1037769).sum := by decide
  have hdescent : baseEnd_1037769 < baseStart_1037769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037786 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_1037786 : Nat := 118140960795 + 1037786 * 2 ^ 59
def prefixEnd_1037786 : Nat := 4983230072969 + 3 ^ 40 * 1037786 * 2
def baseEnd_1037786 : Nat := 177627678168993963734105

theorem tailTrace_1037786 : CollatzResearch.WordTrace tailWord_1037786 prefixEnd_1037786 177627678168993963734105 := by
  unfold tailWord_1037786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462791254571509145783303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25234110012190691055422141 9462791254571509145783303)
  ·
    refine ⟨14194186881857263718674955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9462791254571509145783303 14194186881857263718674955)
    ·
      refine ⟨21291280322785895578012433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14194186881857263718674955 21291280322785895578012433)
      ·
        refine ⟨15968460242089421683509325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21291280322785895578012433 15968460242089421683509325)
        ·
          refine ⟨5988172590783533131315997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15968460242089421683509325 5988172590783533131315997)
          ·
            refine ⟨2245564721543824924243499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5988172590783533131315997 2245564721543824924243499)
            ·
              refine ⟨3368347082315737386365249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245564721543824924243499 3368347082315737386365249)
              ·
                refine ⟨2526260311736803039773937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3368347082315737386365249 2526260311736803039773937)
                ·
                  refine ⟨1894695233802602279830453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526260311736803039773937 1894695233802602279830453)
                  ·
                    refine ⟨177627678168993963734105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1894695233802602279830453 177627678168993963734105)
                    ·
                      rfl

theorem cell23_1037786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_1037786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037786 prefixEnd_1037786 := by exact prefixLift 1037786
  have htrace : WordTrace (prefixWord ++ tailWord_1037786) baseStart_1037786 baseEnd_1037786 := by
    simpa [prefixWord, tailWord_1037786, baseEnd_1037786] using wordTrace_append hprefix tailTrace_1037786
  have hstable : (prefixWord ++ tailWord_1037786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037786).length < 2 ^ (prefixWord ++ tailWord_1037786).sum := by decide
  have hdescent : baseEnd_1037786 < baseStart_1037786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037806 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1037806 : Nat := 118140960795 + 1037806 * 2 ^ 59
def prefixEnd_1037806 : Nat := 4983230072969 + 3 ^ 40 * 1037806 * 2
def baseEnd_1037806 : Nat := 532893304120071812952223

theorem tailTrace_1037806 : CollatzResearch.WordTrace tailWord_1037806 prefixEnd_1037806 532893304120071812952223 := by
  unfold tailWord_1037806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731486809776697499857659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25234596318809053332574181 4731486809776697499857659)
  ·
    refine ⟨7097230214665046249786489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4731486809776697499857659 7097230214665046249786489)
    ·
      refine ⟨5322922660998784687339867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7097230214665046249786489 5322922660998784687339867)
      ·
        refine ⟨7984383991498177031009801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322922660998784687339867 7984383991498177031009801)
        ·
          refine ⟨5988287993623632773257351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7984383991498177031009801 5988287993623632773257351)
          ·
            refine ⟨8982431990435449159886027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988287993623632773257351 8982431990435449159886027)
            ·
              refine ⟨13473647985653173739829041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982431990435449159886027 13473647985653173739829041)
              ·
                refine ⟨10105235989239880304871781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13473647985653173739829041 10105235989239880304871781)
                ·
                  refine ⟨1894731747982477557163459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10105235989239880304871781 1894731747982477557163459)
                  ·
                    refine ⟨2842097621973716335745189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1894731747982477557163459 2842097621973716335745189)
                    ·
                      refine ⟨532893304120071812952223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2842097621973716335745189 532893304120071812952223)
                      ·
                        rfl

theorem cell23_1037806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1037806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037806 prefixEnd_1037806 := by exact prefixLift 1037806
  have htrace : WordTrace (prefixWord ++ tailWord_1037806) baseStart_1037806 baseEnd_1037806 := by
    simpa [prefixWord, tailWord_1037806, baseEnd_1037806] using wordTrace_append hprefix tailTrace_1037806
  have hstable : (prefixWord ++ tailWord_1037806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037806).length < 2 ^ (prefixWord ++ tailWord_1037806).sum := by decide
  have hdescent : baseEnd_1037806 < baseStart_1037806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037833 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 1, 4]
def baseStart_1037833 : Nat := 118140960795 + 1037833 * 2 ^ 59
def prefixEnd_1037833 : Nat := 4983230072969 + 3 ^ 40 * 1037833 * 2
def baseEnd_1037833 : Nat := 177635722699247735771533

theorem tailTrace_1037833 : CollatzResearch.WordTrace tailWord_1037833 prefixEnd_1037833 177635722699247735771533 := by
  unfold tailWord_1037833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37852879249115763610094153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25235252832743842406729435 37852879249115763610094153)
  ·
    refine ⟨28389659436836822707570615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37852879249115763610094153 28389659436836822707570615)
    ·
      refine ⟨42584489155255234061355923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389659436836822707570615 42584489155255234061355923)
      ·
        refine ⟨63876733732882851092033885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42584489155255234061355923 63876733732882851092033885)
        ·
          refine ⟨23953775149831069159512707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63876733732882851092033885 23953775149831069159512707)
          ·
            refine ⟨35930662724746603739269061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23953775149831069159512707 35930662724746603739269061)
            ·
              refine ⟨6736999260889988201112949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35930662724746603739269061 6736999260889988201112949)
              ·
                refine ⟨631593680708436393854339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6736999260889988201112949 631593680708436393854339)
                ·
                  refine ⟨947390521062654590781509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631593680708436393854339 947390521062654590781509)
                  ·
                    refine ⟨177635722699247735771533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947390521062654590781509 177635722699247735771533)
                    ·
                      rfl

theorem cell23_1037833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 4].length) (baseStart_1037833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037833 prefixEnd_1037833 := by exact prefixLift 1037833
  have htrace : WordTrace (prefixWord ++ tailWord_1037833) baseStart_1037833 baseEnd_1037833 := by
    simpa [prefixWord, tailWord_1037833, baseEnd_1037833] using wordTrace_append hprefix tailTrace_1037833
  have hstable : (prefixWord ++ tailWord_1037833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037833).length < 2 ^ (prefixWord ++ tailWord_1037833).sum := by decide
  have hdescent : baseEnd_1037833 < baseStart_1037833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037923 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 1, 6]
def baseStart_1037923 : Nat := 118140960795 + 1037923 * 2 ^ 59
def prefixEnd_1037923 : Nat := 4983230072969 + 3 ^ 40 * 1037923 * 2
def baseEnd_1037923 : Nat := 177651127118882618396395

theorem tailTrace_1037923 : CollatzResearch.WordTrace tailWord_1037923 prefixEnd_1037923 177651127118882618396395 := by
  unfold tailWord_1037923
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856161818789708980870423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25237441212526472653913615 37856161818789708980870423)
  ·
    refine ⟨56784242728184563471305635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37856161818789708980870423 56784242728184563471305635)
    ·
      refine ⟨85176364092276845206958453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56784242728184563471305635 85176364092276845206958453)
      ·
        refine ⟨7985284133650954238152355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85176364092276845206958453 7985284133650954238152355)
        ·
          refine ⟨11977926200476431357228533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7985284133650954238152355 11977926200476431357228533)
          ·
            refine ⟨1122930581294665439740175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11977926200476431357228533 1122930581294665439740175)
            ·
              refine ⟨1684395871941998159610263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122930581294665439740175 1684395871941998159610263)
              ·
                refine ⟨2526593807912997239415395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684395871941998159610263 2526593807912997239415395)
                ·
                  refine ⟨3789890711869495859123093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526593807912997239415395 3789890711869495859123093)
                  ·
                    refine ⟨177651127118882618396395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3789890711869495859123093 177651127118882618396395)
                    ·
                      rfl

theorem cell23_1037923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 6].length) (baseStart_1037923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037923 prefixEnd_1037923 := by exact prefixLift 1037923
  have htrace : WordTrace (prefixWord ++ tailWord_1037923) baseStart_1037923 baseEnd_1037923 := by
    simpa [prefixWord, tailWord_1037923, baseEnd_1037923] using wordTrace_append hprefix tailTrace_1037923
  have hstable : (prefixWord ++ tailWord_1037923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037923).length < 2 ^ (prefixWord ++ tailWord_1037923).sum := by decide
  have hdescent : baseEnd_1037923 < baseStart_1037923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037930 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1037930 : Nat := 118140960795 + 1037930 * 2 ^ 59
def prefixEnd_1037930 : Nat := 4983230072969 + 3 ^ 40 * 1037930 * 2
def baseEnd_1037930 : Nat := 532956975721229327801653

theorem tailTrace_1037930 : CollatzResearch.WordTrace tailWord_1037930 prefixEnd_1037930 532956975721229327801653 := by
  unfold tailWord_1037930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464104282441087294093811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25237611419842899450916829 9464104282441087294093811)
  ·
    refine ⟨14196156423661630941140717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464104282441087294093811 14196156423661630941140717)
    ·
      refine ⟨5323558658873111602927769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14196156423661630941140717 5323558658873111602927769)
      ·
        refine ⟨3992668994154833702195827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323558658873111602927769 3992668994154833702195827)
        ·
          refine ⟨5989003491232250553293741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992668994154833702195827 5989003491232250553293741)
          ·
            refine ⟨2245876309212093957485153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5989003491232250553293741 2245876309212093957485153)
            ·
              refine ⟨1684407231909070468113865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245876309212093957485153 1684407231909070468113865)
              ·
                refine ⟨1263305423931802851085399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684407231909070468113865 1263305423931802851085399)
                ·
                  refine ⟨1894958135897704276628099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263305423931802851085399 1894958135897704276628099)
                  ·
                    refine ⟨2842437203846556414942149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1894958135897704276628099 2842437203846556414942149)
                    ·
                      refine ⟨532956975721229327801653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2842437203846556414942149 532956975721229327801653)
                      ·
                        rfl

theorem cell23_1037930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1037930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037930 prefixEnd_1037930 := by exact prefixLift 1037930
  have htrace : WordTrace (prefixWord ++ tailWord_1037930) baseStart_1037930 baseEnd_1037930 := by
    simpa [prefixWord, tailWord_1037930, baseEnd_1037930] using wordTrace_append hprefix tailTrace_1037930
  have hstable : (prefixWord ++ tailWord_1037930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037930).length < 2 ^ (prefixWord ++ tailWord_1037930).sum := by decide
  have hdescent : baseEnd_1037930 < baseStart_1037930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037936 : List Nat := [2, 1, 1, 1, 6, 2, 1, 9]
def baseStart_1037936 : Nat := 118140960795 + 1037936 * 2 ^ 59
def prefixEnd_1037936 : Nat := 4983230072969 + 3 ^ 40 * 1037936 * 2
def baseEnd_1037936 : Nat := 19739261355746529789875

theorem tailTrace_1037936 : CollatzResearch.WordTrace tailWord_1037936 prefixEnd_1037936 19739261355746529789875 := by
  unfold tailWord_1037936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928317983871306100546831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25237757311828408134062441 18928317983871306100546831)
  ·
    refine ⟨28392476975806959150820247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928317983871306100546831 28392476975806959150820247)
    ·
      refine ⟨42588715463710438726230371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392476975806959150820247 42588715463710438726230371)
      ·
        refine ⟨63883073195565658089345557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42588715463710438726230371 63883073195565658089345557)
        ·
          refine ⟨2994519056042140222938073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63883073195565658089345557 2994519056042140222938073)
          ·
            refine ⟨2245889292031605167203555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994519056042140222938073 2245889292031605167203555)
            ·
              refine ⟨3368833938047407750805333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245889292031605167203555 3368833938047407750805333)
              ·
                refine ⟨19739261355746529789875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3368833938047407750805333 19739261355746529789875)
                ·
                  rfl

theorem cell23_1037936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 9].length) (baseStart_1037936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037936 prefixEnd_1037936 := by exact prefixLift 1037936
  have htrace : WordTrace (prefixWord ++ tailWord_1037936) baseStart_1037936 baseEnd_1037936 := by
    simpa [prefixWord, tailWord_1037936, baseEnd_1037936] using wordTrace_append hprefix tailTrace_1037936
  have hstable : (prefixWord ++ tailWord_1037936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037936).length < 2 ^ (prefixWord ++ tailWord_1037936).sum := by decide
  have hdescent : baseEnd_1037936 < baseStart_1037936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037963 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 3]
def baseStart_1037963 : Nat := 118140960795 + 1037963 * 2 ^ 59
def prefixEnd_1037963 : Nat := 4983230072969 + 3 ^ 40 * 1037963 * 2
def baseEnd_1037963 : Nat := 532973920582827698689001

theorem tailTrace_1037963 : CollatzResearch.WordTrace tailWord_1037963 prefixEnd_1037963 532973920582827698689001 := by
  unfold tailWord_1037963
  simp only [CollatzResearch.WordTrace]
  refine ⟨37857620738644795812326543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25238413825763197208217695 37857620738644795812326543)
  ·
    refine ⟨56786431107967193718489815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37857620738644795812326543 56786431107967193718489815)
    ·
      refine ⟨85179646661950790577734723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56786431107967193718489815 85179646661950790577734723)
      ·
        refine ⟨127769469992926185866602085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85179646661950790577734723 127769469992926185866602085)
        ·
          refine ⟨23956775623673659849987891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127769469992926185866602085 23956775623673659849987891)
          ·
            refine ⟨35935163435510489774981837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23956775623673659849987891 35935163435510489774981837)
            ·
              refine ⟨13475686288316433665618189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35935163435510489774981837 13475686288316433665618189)
              ·
                refine ⟨5053382358118662624606821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13475686288316433665618189 5053382358118662624606821)
                ·
                  refine ⟨947509192147249242113779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5053382358118662624606821 947509192147249242113779)
                  ·
                    refine ⟨1421263788220873863170669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 947509192147249242113779 1421263788220873863170669)
                    ·
                      refine ⟨532973920582827698689001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421263788220873863170669 532973920582827698689001)
                      ·
                        rfl

theorem cell23_1037963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 3].length) (baseStart_1037963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037963 prefixEnd_1037963 := by exact prefixLift 1037963
  have htrace : WordTrace (prefixWord ++ tailWord_1037963) baseStart_1037963 baseEnd_1037963 := by
    simpa [prefixWord, tailWord_1037963, baseEnd_1037963] using wordTrace_append hprefix tailTrace_1037963
  have hstable : (prefixWord ++ tailWord_1037963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037963).length < 2 ^ (prefixWord ++ tailWord_1037963).sum := by decide
  have hdescent : baseEnd_1037963 < baseStart_1037963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037964 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 1, 2, 2]
def baseStart_1037964 : Nat := 118140960795 + 1037964 * 2 ^ 59
def prefixEnd_1037964 : Nat := 4983230072969 + 3 ^ 40 * 1037964 * 2
def baseEnd_1037964 : Nat := 532974434063482194776497

theorem tailTrace_1037964 : CollatzResearch.WordTrace tailWord_1037964 prefixEnd_1037964 532974434063482194776497 := by
  unfold tailWord_1037964
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928828605820586491556473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25238438141094115322075297 18928828605820586491556473)
  ·
    refine ⟨14196621454365439868667355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18928828605820586491556473 14196621454365439868667355)
    ·
      refine ⟨21294932181548159803001033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14196621454365439868667355 21294932181548159803001033)
      ·
        refine ⟨15971199136161119852250775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21294932181548159803001033 15971199136161119852250775)
        ·
          refine ⟨23956798704241679778376163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15971199136161119852250775 23956798704241679778376163)
          ·
            refine ⟨35935198056362519667564245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23956798704241679778376163 35935198056362519667564245)
            ·
              refine ⟨842231204445996554708537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35935198056362519667564245 842231204445996554708537)
              ·
                refine ⟨631673403334497416031403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842231204445996554708537 631673403334497416031403)
                ·
                  refine ⟨947510105001746124047105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631673403334497416031403 947510105001746124047105)
                  ·
                    refine ⟨710632578751309593035329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 947510105001746124047105 710632578751309593035329)
                    ·
                      refine ⟨532974434063482194776497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710632578751309593035329 532974434063482194776497)
                      ·
                        rfl

theorem cell23_1037964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_1037964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1037964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1037964 prefixEnd_1037964 := by exact prefixLift 1037964
  have htrace : WordTrace (prefixWord ++ tailWord_1037964) baseStart_1037964 baseEnd_1037964 := by
    simpa [prefixWord, tailWord_1037964, baseEnd_1037964] using wordTrace_append hprefix tailTrace_1037964
  have hstable : (prefixWord ++ tailWord_1037964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037964).length < 2 ^ (prefixWord ++ tailWord_1037964).sum := by decide
  have hdescent : baseEnd_1037964 < baseStart_1037964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038020 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1038020 : Nat := 118140960795 + 1038020 * 2 ^ 59
def prefixEnd_1038020 : Nat := 4983230072969 + 3 ^ 40 * 1038020 * 2
def baseEnd_1038020 : Nat := 533003188980133975676239

theorem tailTrace_1038020 : CollatzResearch.WordTrace tailWord_1038020 prefixEnd_1038020 533003188980133975676239 := by
  unfold tailWord_1038020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18929849849719147273575757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25239799799625529698101009 18929849849719147273575757)
  ·
    refine ⟨7098693693644680227590909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18929849849719147273575757 7098693693644680227590909)
    ·
      refine ⟨2662010135116755085346591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7098693693644680227590909 2662010135116755085346591)
      ·
        refine ⟨3993015202675132628019887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662010135116755085346591 3993015202675132628019887)
        ·
          refine ⟨5989522804012698942029831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993015202675132628019887 5989522804012698942029831)
          ·
            refine ⟨8984284206019048413044747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989522804012698942029831 8984284206019048413044747)
            ·
              refine ⟨13476426309028572619567121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984284206019048413044747 13476426309028572619567121)
              ·
                refine ⟨10107319731771429464675341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13476426309028572619567121 10107319731771429464675341)
                ·
                  refine ⟨3790244899414286049253253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10107319731771429464675341 3790244899414286049253253)
                  ·
                    refine ⟨710670918640178634234985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3790244899414286049253253 710670918640178634234985)
                    ·
                      refine ⟨533003188980133975676239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710670918640178634234985 533003188980133975676239)
                      ·
                        rfl

theorem cell23_1038020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1038020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038020 prefixEnd_1038020 := by exact prefixLift 1038020
  have htrace : WordTrace (prefixWord ++ tailWord_1038020) baseStart_1038020 baseEnd_1038020 := by
    simpa [prefixWord, tailWord_1038020, baseEnd_1038020] using wordTrace_append hprefix tailTrace_1038020
  have hstable : (prefixWord ++ tailWord_1038020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038020).length < 2 ^ (prefixWord ++ tailWord_1038020).sum := by decide
  have hdescent : baseEnd_1038020 < baseStart_1038020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038033 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_1038033 : Nat := 118140960795 + 1038033 * 2 ^ 59
def prefixEnd_1038033 : Nat := 4983230072969 + 3 ^ 40 * 1038033 * 2
def baseEnd_1038033 : Nat := 533009864228642424813679

theorem tailTrace_1038033 : CollatzResearch.WordTrace tailWord_1038033 prefixEnd_1038033 533009864228642424813679 := by
  unfold tailWord_1038033
  simp only [CollatzResearch.WordTrace]
  refine ⟨37860173848391197767374753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25240115898927465178249835 37860173848391197767374753)
  ·
    refine ⟨28395130386293398325531065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37860173848391197767374753 28395130386293398325531065)
    ·
      refine ⟨21296347789720048744148299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28395130386293398325531065 21296347789720048744148299)
      ·
        refine ⟨31944521684580073116222449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21296347789720048744148299 31944521684580073116222449)
        ·
          refine ⟨23958391263435054837166837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31944521684580073116222449 23958391263435054837166837)
          ·
            refine ⟨2246099180947036390984391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23958391263435054837166837 2246099180947036390984391)
            ·
              refine ⟨3369148771420554586476587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246099180947036390984391 3369148771420554586476587)
              ·
                refine ⟨5053723157130831879714881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369148771420554586476587 5053723157130831879714881)
                ·
                  refine ⟨3790292367848123909786161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053723157130831879714881 3790292367848123909786161)
                  ·
                    refine ⟨2842719275886092932339621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790292367848123909786161 2842719275886092932339621)
                    ·
                      refine ⟨533009864228642424813679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2842719275886092932339621 533009864228642424813679)
                      ·
                        rfl

theorem cell23_1038033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_1038033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038033 prefixEnd_1038033 := by exact prefixLift 1038033
  have htrace : WordTrace (prefixWord ++ tailWord_1038033) baseStart_1038033 baseEnd_1038033 := by
    simpa [prefixWord, tailWord_1038033, baseEnd_1038033] using wordTrace_append hprefix tailTrace_1038033
  have hstable : (prefixWord ++ tailWord_1038033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038033).length < 2 ^ (prefixWord ++ tailWord_1038033).sum := by decide
  have hdescent : baseEnd_1038033 < baseStart_1038033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038053 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1038053 : Nat := 118140960795 + 1038053 * 2 ^ 59
def prefixEnd_1038053 : Nat := 4983230072969 + 3 ^ 40 * 1038053 * 2
def baseEnd_1038053 : Nat := 533020133841732346563587

theorem tailTrace_1038053 : CollatzResearch.WordTrace tailWord_1038053 prefixEnd_1038053 533020133841732346563587 := by
  unfold tailWord_1038053
  simp only [CollatzResearch.WordTrace]
  refine ⟨37860903308318741183102813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25240602205545827455401875 37860903308318741183102813)
  ·
    refine ⟨14197838740619527943663555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37860903308318741183102813 14197838740619527943663555)
    ·
      refine ⟨21296758110929291915495333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14197838740619527943663555 21296758110929291915495333)
      ·
        refine ⟨3993142145799242234155375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21296758110929291915495333 3993142145799242234155375)
        ·
          refine ⟨5989713218698863351233063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993142145799242234155375 5989713218698863351233063)
          ·
            refine ⟨8984569828048295026849595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989713218698863351233063 8984569828048295026849595)
            ·
              refine ⟨13476854742072442540274393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984569828048295026849595 13476854742072442540274393)
              ·
                refine ⟨10107641056554331905205795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13476854742072442540274393 10107641056554331905205795)
                ·
                  refine ⟨15161461584831497857808693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10107641056554331905205795 15161461584831497857808693)
                  ·
                    refine ⟨1421387023577952924169565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15161461584831497857808693 1421387023577952924169565)
                    ·
                      refine ⟨533020133841732346563587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421387023577952924169565 533020133841732346563587)
                      ·
                        rfl

theorem cell23_1038053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1038053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038053 prefixEnd_1038053 := by exact prefixLift 1038053
  have htrace : WordTrace (prefixWord ++ tailWord_1038053) baseStart_1038053 baseEnd_1038053 := by
    simpa [prefixWord, tailWord_1038053, baseEnd_1038053] using wordTrace_append hprefix tailTrace_1038053
  have hstable : (prefixWord ++ tailWord_1038053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038053).length < 2 ^ (prefixWord ++ tailWord_1038053).sum := by decide
  have hdescent : baseEnd_1038053 < baseStart_1038053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038070 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1038070 : Nat := 118140960795 + 1038070 * 2 ^ 59
def prefixEnd_1038070 : Nat := 4983230072969 + 3 ^ 40 * 1038070 * 2
def baseEnd_1038070 : Nat := 533028863012858780051009

theorem tailTrace_1038070 : CollatzResearch.WordTrace tailWord_1038070 prefixEnd_1038070 533028863012858780051009 := by
  unfold tailWord_1038070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366345209328572067904479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25241015566171435390981109 2366345209328572067904479)
  ·
    refine ⟨3549517813992858101856719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366345209328572067904479 3549517813992858101856719)
    ·
      refine ⟨5324276720989287152785079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549517813992858101856719 5324276720989287152785079)
      ·
        refine ⟨7986415081483930729177619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324276720989287152785079 7986415081483930729177619)
        ·
          refine ⟨11979622622225896093766429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986415081483930729177619 11979622622225896093766429)
          ·
            refine ⟨4492358483334711035162411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11979622622225896093766429 4492358483334711035162411)
            ·
              refine ⟨6738537725002066552743617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492358483334711035162411 6738537725002066552743617)
              ·
                refine ⟨5053903293751549914557713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738537725002066552743617 5053903293751549914557713)
                ·
                  refine ⟨3790427470313662435918285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053903293751549914557713 3790427470313662435918285)
                  ·
                    refine ⟨1421410301367623413469357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790427470313662435918285 1421410301367623413469357)
                    ·
                      refine ⟨533028863012858780051009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421410301367623413469357 533028863012858780051009)
                      ·
                        rfl

theorem cell23_1038070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1038070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038070 prefixEnd_1038070 := by exact prefixLift 1038070
  have htrace : WordTrace (prefixWord ++ tailWord_1038070) baseStart_1038070 baseEnd_1038070 := by
    simpa [prefixWord, tailWord_1038070, baseEnd_1038070] using wordTrace_append hprefix tailTrace_1038070
  have hstable : (prefixWord ++ tailWord_1038070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038070).length < 2 ^ (prefixWord ++ tailWord_1038070).sum := by decide
  have hdescent : baseEnd_1038070 < baseStart_1038070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038130 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1038130 : Nat := 118140960795 + 1038130 * 2 ^ 59
def prefixEnd_1038130 : Nat := 4983230072969 + 3 ^ 40 * 1038130 * 2
def baseEnd_1038130 : Nat := 533059671852128545300733

theorem tailTrace_1038130 : CollatzResearch.WordTrace tailWord_1038130 prefixEnd_1038130 533059671852128545300733 := by
  unfold tailWord_1038130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465927932259945833413961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25242474486026522222437229 9465927932259945833413961)
  ·
    refine ⟨7099445949194959375060471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9465927932259945833413961 7099445949194959375060471)
    ·
      refine ⟨10649168923792439062590707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7099445949194959375060471 10649168923792439062590707)
      ·
        refine ⟨15973753385688658593886061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649168923792439062590707 15973753385688658593886061)
        ·
          refine ⟨5990157519633246972707273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15973753385688658593886061 5990157519633246972707273)
          ·
            refine ⟨4492618139724935229530455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5990157519633246972707273 4492618139724935229530455)
            ·
              refine ⟨6738927209587402844295683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492618139724935229530455 6738927209587402844295683)
              ·
                refine ⟨10108390814381104266443525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738927209587402844295683 10108390814381104266443525)
                ·
                  refine ⟨1895323277696457049958161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10108390814381104266443525 1895323277696457049958161)
                  ·
                    refine ⟨1421492458272342787468621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895323277696457049958161 1421492458272342787468621)
                    ·
                      refine ⟨533059671852128545300733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421492458272342787468621 533059671852128545300733)
                      ·
                        rfl

theorem cell23_1038130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1038130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038130 prefixEnd_1038130 := by exact prefixLift 1038130
  have htrace : WordTrace (prefixWord ++ tailWord_1038130) baseStart_1038130 baseEnd_1038130 := by
    simpa [prefixWord, tailWord_1038130, baseEnd_1038130] using wordTrace_append hprefix tailTrace_1038130
  have hstable : (prefixWord ++ tailWord_1038130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038130).length < 2 ^ (prefixWord ++ tailWord_1038130).sum := by decide
  have hdescent : baseEnd_1038130 < baseStart_1038130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038160 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3]
def baseStart_1038160 : Nat := 118140960795 + 1038160 * 2 ^ 59
def prefixEnd_1038160 : Nat := 4983230072969 + 3 ^ 40 * 1038160 * 2
def baseEnd_1038160 : Nat := 533075076271763427925595

theorem tailTrace_1038160 : CollatzResearch.WordTrace tailWord_1038160 prefixEnd_1038160 533075076271763427925595 := by
  unfold tailWord_1038160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932402959465549228623967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25243203945954065638165289 18932402959465549228623967)
  ·
    refine ⟨28398604439198323842935951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18932402959465549228623967 28398604439198323842935951)
    ·
      refine ⟨42597906658797485764403927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28398604439198323842935951 42597906658797485764403927)
      ·
        refine ⟨63896859988196228646605891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42597906658797485764403927 63896859988196228646605891)
        ·
          refine ⟨95845289982294342969908837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63896859988196228646605891 95845289982294342969908837)
          ·
            refine ⟨17970991871680189306857907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95845289982294342969908837 17970991871680189306857907)
            ·
              refine ⟨26956487807520283960286861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17970991871680189306857907 26956487807520283960286861)
              ·
                refine ⟨10108682927820106485107573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26956487807520283960286861 10108682927820106485107573)
                ·
                  refine ⟨947689024483134982978835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10108682927820106485107573 947689024483134982978835)
                  ·
                    refine ⟨1421533536724702474468253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 947689024483134982978835 1421533536724702474468253)
                    ·
                      refine ⟨533075076271763427925595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421533536724702474468253 533075076271763427925595)
                      ·
                        rfl

theorem cell23_1038160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_1038160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038160 prefixEnd_1038160 := by exact prefixLift 1038160
  have htrace : WordTrace (prefixWord ++ tailWord_1038160) baseStart_1038160 baseEnd_1038160 := by
    simpa [prefixWord, tailWord_1038160, baseEnd_1038160] using wordTrace_append hprefix tailTrace_1038160
  have hstable : (prefixWord ++ tailWord_1038160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038160).length < 2 ^ (prefixWord ++ tailWord_1038160).sum := by decide
  have hdescent : baseEnd_1038160 < baseStart_1038160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038193 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1038193 : Nat := 118140960795 + 1038193 * 2 ^ 59
def prefixEnd_1038193 : Nat := 4983230072969 + 3 ^ 40 * 1038193 * 2
def baseEnd_1038193 : Nat := 177697340377787266270981

theorem tailTrace_1038193 : CollatzResearch.WordTrace tailWord_1038193 prefixEnd_1038193 177697340377787266270981 := by
  unfold tailWord_1038193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866009527811545093199233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25244006351874363395466155 37866009527811545093199233)
  ·
    refine ⟨28399507145858658819899425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37866009527811545093199233 28399507145858658819899425)
    ·
      refine ⟨21299630359393994114924569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28399507145858658819899425 21299630359393994114924569)
      ·
        refine ⟨15974722769545495586193427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21299630359393994114924569 15974722769545495586193427)
        ·
          refine ⟨23962084154318243379290141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15974722769545495586193427 23962084154318243379290141)
          ·
            refine ⟨8985781557869341267233803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23962084154318243379290141 8985781557869341267233803)
            ·
              refine ⟨13478672336804011900850705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985781557869341267233803 13478672336804011900850705)
              ·
                refine ⟨10109004252603008925638029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13478672336804011900850705 10109004252603008925638029)
                ·
                  refine ⟨3790876594726128347114261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10109004252603008925638029 3790876594726128347114261)
                  ·
                    refine ⟨177697340377787266270981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3790876594726128347114261 177697340377787266270981)
                    ·
                      rfl

theorem cell23_1038193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1038193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038193 prefixEnd_1038193 := by exact prefixLift 1038193
  have htrace : WordTrace (prefixWord ++ tailWord_1038193) baseStart_1038193 baseEnd_1038193 := by
    simpa [prefixWord, tailWord_1038193, baseEnd_1038193] using wordTrace_append hprefix tailTrace_1038193
  have hstable : (prefixWord ++ tailWord_1038193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038193).length < 2 ^ (prefixWord ++ tailWord_1038193).sum := by decide
  have hdescent : baseEnd_1038193 < baseStart_1038193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038203 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_1038203 : Nat := 118140960795 + 1038203 * 2 ^ 59
def prefixEnd_1038203 : Nat := 4983230072969 + 3 ^ 40 * 1038203 * 2
def baseEnd_1038203 : Nat := 533097155939906759687897

theorem tailTrace_1038203 : CollatzResearch.WordTrace tailWord_1038203 prefixEnd_1038203 533097155939906759687897 := by
  unfold tailWord_1038203
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866374257775316801063263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25244249505183544534042175 37866374257775316801063263)
  ·
    refine ⟨56799561386662975201594895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37866374257775316801063263 56799561386662975201594895)
    ·
      refine ⟨85199342079994462802392343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56799561386662975201594895 85199342079994462802392343)
      ·
        refine ⟨127799013119991694203588515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85199342079994462802392343 127799013119991694203588515)
        ·
          refine ⟨191698519679987541305382773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127799013119991694203588515 191698519679987541305382773)
          ·
            refine ⟨17971736219998831997379635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191698519679987541305382773 17971736219998831997379635)
            ·
              refine ⟨26957604329998247996069453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17971736219998831997379635 26957604329998247996069453)
              ·
                refine ⟨10109101623749342998526045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26957604329998247996069453 10109101623749342998526045)
                ·
                  refine ⟨3790913108906003624447267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10109101623749342998526045 3790913108906003624447267)
                  ·
                    refine ⟨5686369663359005436670901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3790913108906003624447267 5686369663359005436670901)
                    ·
                      refine ⟨533097155939906759687897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5686369663359005436670901 533097155939906759687897)
                      ·
                        rfl

theorem cell23_1038203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_1038203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038203 prefixEnd_1038203 := by exact prefixLift 1038203
  have htrace : WordTrace (prefixWord ++ tailWord_1038203) baseStart_1038203 baseEnd_1038203 := by
    simpa [prefixWord, tailWord_1038203, baseEnd_1038203] using wordTrace_append hprefix tailTrace_1038203
  have hstable : (prefixWord ++ tailWord_1038203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038203).length < 2 ^ (prefixWord ++ tailWord_1038203).sum := by decide
  have hdescent : baseEnd_1038203 < baseStart_1038203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038234 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1038234 : Nat := 118140960795 + 1038234 * 2 ^ 59
def prefixEnd_1038234 : Nat := 4983230072969 + 3 ^ 40 * 1038234 * 2
def baseEnd_1038234 : Nat := 533113073840196138400255

theorem tailTrace_1038234 : CollatzResearch.WordTrace tailWord_1038234 prefixEnd_1038234 533113073840196138400255 := by
  unfold tailWord_1038234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466876230165752273860439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25245003280442006063627837 9466876230165752273860439)
  ·
    refine ⟨14200314345248628410790659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9466876230165752273860439 14200314345248628410790659)
    ·
      refine ⟨21300471517872942616185989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14200314345248628410790659 21300471517872942616185989)
      ·
        refine ⟨3993838409601176740534873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21300471517872942616185989 3993838409601176740534873)
        ·
          refine ⟨2995378807200882555401155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993838409601176740534873 2995378807200882555401155)
          ·
            refine ⟨4493068210801323833101733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995378807200882555401155 4493068210801323833101733)
            ·
              refine ⟨842450289525248218706575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4493068210801323833101733 842450289525248218706575)
              ·
                refine ⟨1263675434287872328059863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842450289525248218706575 1263675434287872328059863)
                ·
                  refine ⟨1895513151431808492089795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263675434287872328059863 1895513151431808492089795)
                  ·
                    refine ⟨2843269727147712738134693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895513151431808492089795 2843269727147712738134693)
                    ·
                      refine ⟨533113073840196138400255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2843269727147712738134693 533113073840196138400255)
                      ·
                        rfl

theorem cell23_1038234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1038234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038234 prefixEnd_1038234 := by exact prefixLift 1038234
  have htrace : WordTrace (prefixWord ++ tailWord_1038234) baseStart_1038234 baseEnd_1038234 := by
    simpa [prefixWord, tailWord_1038234, baseEnd_1038234] using wordTrace_append hprefix tailTrace_1038234
  have hstable : (prefixWord ++ tailWord_1038234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038234).length < 2 ^ (prefixWord ++ tailWord_1038234).sum := by decide
  have hdescent : baseEnd_1038234 < baseStart_1038234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038243 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1038243 : Nat := 118140960795 + 1038243 * 2 ^ 59
def prefixEnd_1038243 : Nat := 4983230072969 + 3 ^ 40 * 1038243 * 2
def baseEnd_1038243 : Nat := 533117695166086603187713

theorem tailTrace_1038243 : CollatzResearch.WordTrace tailWord_1038243 prefixEnd_1038243 533117695166086603187713 := by
  unfold tailWord_1038243
  simp only [CollatzResearch.WordTrace]
  refine ⟨37867833177630403632519383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25245222118420269088346255 37867833177630403632519383)
  ·
    refine ⟨56801749766445605448779075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37867833177630403632519383 56801749766445605448779075)
    ·
      refine ⟨85202624649668408173168613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56801749766445605448779075 85202624649668408173168613)
      ·
        refine ⟨15975492121812826532469115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85202624649668408173168613 15975492121812826532469115)
        ·
          refine ⟨23963238182719239798703673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15975492121812826532469115 23963238182719239798703673)
          ·
            refine ⟨17972428637039429849027755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23963238182719239798703673 17972428637039429849027755)
            ·
              refine ⟨26958642955559144773541633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17972428637039429849027755 26958642955559144773541633)
              ·
                refine ⟨20218982216669358580156225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26958642955559144773541633 20218982216669358580156225)
                ·
                  refine ⟨15164236662502018935117169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20218982216669358580156225 15164236662502018935117169)
                  ·
                    refine ⟨11373177496876514201337877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15164236662502018935117169 11373177496876514201337877)
                    ·
                      refine ⟨533117695166086603187713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11373177496876514201337877 533117695166086603187713)
                      ·
                        rfl

theorem cell23_1038243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1038243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038243 prefixEnd_1038243 := by exact prefixLift 1038243
  have htrace : WordTrace (prefixWord ++ tailWord_1038243) baseStart_1038243 baseEnd_1038243 := by
    simpa [prefixWord, tailWord_1038243, baseEnd_1038243] using wordTrace_append hprefix tailTrace_1038243
  have hstable : (prefixWord ++ tailWord_1038243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038243).length < 2 ^ (prefixWord ++ tailWord_1038243).sum := by decide
  have hdescent : baseEnd_1038243 < baseStart_1038243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038244 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1038244 : Nat := 118140960795 + 1038244 * 2 ^ 59
def prefixEnd_1038244 : Nat := 4983230072969 + 3 ^ 40 * 1038244 * 2
def baseEnd_1038244 : Nat := 177706069548913699758403

theorem tailTrace_1038244 : CollatzResearch.WordTrace tailWord_1038244 prefixEnd_1038244 177706069548913699758403 := by
  unfold tailWord_1038244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933934825313390401652893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25245246433751187202203857 18933934825313390401652893)
  ·
    refine ⟨7100225559492521400619835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18933934825313390401652893 7100225559492521400619835)
    ·
      refine ⟨10650338339238782100929753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7100225559492521400619835 10650338339238782100929753)
      ·
        refine ⟨7987753754429086575697315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10650338339238782100929753 7987753754429086575697315)
        ·
          refine ⟨11981630631643629863545973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987753754429086575697315 11981630631643629863545973)
          ·
            refine ⟨1123277871716590299707435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11981630631643629863545973 1123277871716590299707435)
            ·
              refine ⟨1684916807574885449561153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123277871716590299707435 1684916807574885449561153)
              ·
                refine ⟨1263687605681164087170865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684916807574885449561153 1263687605681164087170865)
                ·
                  refine ⟨947765704260873065378149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263687605681164087170865 947765704260873065378149)
                  ·
                    refine ⟨177706069548913699758403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947765704260873065378149 177706069548913699758403)
                    ·
                      rfl

theorem cell23_1038244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1038244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038244 prefixEnd_1038244 := by exact prefixLift 1038244
  have htrace : WordTrace (prefixWord ++ tailWord_1038244) baseStart_1038244 baseEnd_1038244 := by
    simpa [prefixWord, tailWord_1038244, baseEnd_1038244] using wordTrace_append hprefix tailTrace_1038244
  have hstable : (prefixWord ++ tailWord_1038244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038244).length < 2 ^ (prefixWord ++ tailWord_1038244).sum := by decide
  have hdescent : baseEnd_1038244 < baseStart_1038244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038280 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1038280 : Nat := 118140960795 + 1038280 * 2 ^ 59
def prefixEnd_1038280 : Nat := 4983230072969 + 3 ^ 40 * 1038280 * 2
def baseEnd_1038280 : Nat := 533136693950302958425043

theorem tailTrace_1038280 : CollatzResearch.WordTrace tailWord_1038280 prefixEnd_1038280 533136693950302958425043 := by
  unfold tailWord_1038280
  simp only [CollatzResearch.WordTrace]
  refine ⟨18934591339248179475808147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25246121785664239301077529 18934591339248179475808147)
  ·
    refine ⟨28401887008872269213712221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18934591339248179475808147 28401887008872269213712221)
    ·
      refine ⟨10650707628327100955142083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28401887008872269213712221 10650707628327100955142083)
      ·
        refine ⟨15976061442490651432713125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650707628327100955142083 15976061442490651432713125)
        ·
          refine ⟨2995511520466997143633711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15976061442490651432713125 2995511520466997143633711)
          ·
            refine ⟨4493267280700495715450567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995511520466997143633711 4493267280700495715450567)
            ·
              refine ⟨6739900921050743573175851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493267280700495715450567 6739900921050743573175851)
              ·
                refine ⟨10109851381576115359763777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739900921050743573175851 10109851381576115359763777)
                ·
                  refine ⟨7582388536182086519822833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10109851381576115359763777 7582388536182086519822833)
                  ·
                    refine ⟨5686791402136564889867125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7582388536182086519822833 5686791402136564889867125)
                    ·
                      refine ⟨533136693950302958425043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5686791402136564889867125 533136693950302958425043)
                      ·
                        rfl

theorem cell23_1038280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1038280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038280 prefixEnd_1038280 := by exact prefixLift 1038280
  have htrace : WordTrace (prefixWord ++ tailWord_1038280) baseStart_1038280 baseEnd_1038280 := by
    simpa [prefixWord, tailWord_1038280, baseEnd_1038280] using wordTrace_append hprefix tailTrace_1038280
  have hstable : (prefixWord ++ tailWord_1038280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038280).length < 2 ^ (prefixWord ++ tailWord_1038280).sum := by decide
  have hdescent : baseEnd_1038280 < baseStart_1038280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038318 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_1038318 : Nat := 118140960795 + 1038318 * 2 ^ 59
def prefixEnd_1038318 : Nat := 4983230072969 + 3 ^ 40 * 1038318 * 2
def baseEnd_1038318 : Nat := 533156206215173809749869

theorem tailTrace_1038318 : CollatzResearch.WordTrace tailWord_1038318 prefixEnd_1038318 533156206215173809749869 := by
  unfold tailWord_1038318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733821081544836430187451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25247045768239127627666405 4733821081544836430187451)
  ·
    refine ⟨7100731622317254645281177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4733821081544836430187451 7100731622317254645281177)
    ·
      refine ⟨5325548716737940983960883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7100731622317254645281177 5325548716737940983960883)
      ·
        refine ⟨7988323075106911475941325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325548716737940983960883 7988323075106911475941325)
        ·
          refine ⟨2995621153165091803477997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7988323075106911475941325 2995621153165091803477997)
          ·
            refine ⟨1123357932436909426304249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2995621153165091803477997 1123357932436909426304249)
            ·
              refine ⟨842518449327682069728187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123357932436909426304249 842518449327682069728187)
              ·
                refine ⟨1263777673991523104592281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842518449327682069728187 1263777673991523104592281)
                ·
                  refine ⟨947833255493642328444211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263777673991523104592281 947833255493642328444211)
                  ·
                    refine ⟨1421749883240463492666317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 947833255493642328444211 1421749883240463492666317)
                    ·
                      refine ⟨533156206215173809749869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421749883240463492666317 533156206215173809749869)
                      ·
                        rfl

theorem cell23_1038318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_1038318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038318 prefixEnd_1038318 := by exact prefixLift 1038318
  have htrace : WordTrace (prefixWord ++ tailWord_1038318) baseStart_1038318 baseEnd_1038318 := by
    simpa [prefixWord, tailWord_1038318, baseEnd_1038318] using wordTrace_append hprefix tailTrace_1038318
  have hstable : (prefixWord ++ tailWord_1038318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038318).length < 2 ^ (prefixWord ++ tailWord_1038318).sum := by decide
  have hdescent : baseEnd_1038318 < baseStart_1038318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038320 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_1038320 : Nat := 118140960795 + 1038320 * 2 ^ 59
def prefixEnd_1038320 : Nat := 4983230072969 + 3 ^ 40 * 1038320 * 2
def baseEnd_1038320 : Nat := 533157233176482801924859

theorem tailTrace_1038320 : CollatzResearch.WordTrace tailWord_1038320 prefixEnd_1038320 533157233176482801924859 := by
  unfold tailWord_1038320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935320799175722891536207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25247094398900963855381609 18935320799175722891536207)
  ·
    refine ⟨28402981198763584337304311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18935320799175722891536207 28402981198763584337304311)
    ·
      refine ⟨42604471798145376505956467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28402981198763584337304311 42604471798145376505956467)
      ·
        refine ⟨63906707697218064758934701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42604471798145376505956467 63906707697218064758934701)
        ·
          refine ⟨23965015386456774284600513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63906707697218064758934701 23965015386456774284600513)
          ·
            refine ⟨17973761539842580713450385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23965015386456774284600513 17973761539842580713450385)
            ·
              refine ⟨13480321154881935535087789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17973761539842580713450385 13480321154881935535087789)
              ·
                refine ⟨5055120433080725825657921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13480321154881935535087789 5055120433080725825657921)
                ·
                  refine ⟨3791340324810544369243441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5055120433080725825657921 3791340324810544369243441)
                  ·
                    refine ⟨2843505243607908276932581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791340324810544369243441 2843505243607908276932581)
                    ·
                      refine ⟨533157233176482801924859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2843505243607908276932581 533157233176482801924859)
                      ·
                        rfl

theorem cell23_1038320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_1038320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038320 prefixEnd_1038320 := by exact prefixLift 1038320
  have htrace : WordTrace (prefixWord ++ tailWord_1038320) baseStart_1038320 baseEnd_1038320 := by
    simpa [prefixWord, tailWord_1038320, baseEnd_1038320] using wordTrace_append hprefix tailTrace_1038320
  have hstable : (prefixWord ++ tailWord_1038320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038320).length < 2 ^ (prefixWord ++ tailWord_1038320).sum := by decide
  have hdescent : baseEnd_1038320 < baseStart_1038320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038347 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 5]
def baseStart_1038347 : Nat := 118140960795 + 1038347 * 2 ^ 59
def prefixEnd_1038347 : Nat := 4983230072969 + 3 ^ 40 * 1038347 * 2
def baseEnd_1038347 : Nat := 59241233017128244031915

theorem tailTrace_1038347 : CollatzResearch.WordTrace tailWord_1038347 prefixEnd_1038347 59241233017128244031915 := by
  unfold tailWord_1038347
  simp only [CollatzResearch.WordTrace]
  refine ⟨37871626369253629394305295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25247750912835752929536863 37871626369253629394305295)
  ·
    refine ⟨56807439553880444091457943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37871626369253629394305295 56807439553880444091457943)
    ·
      refine ⟨85211159330820666137186915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56807439553880444091457943 85211159330820666137186915)
      ·
        refine ⟨127816738996230999205780373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85211159330820666137186915 127816738996230999205780373)
        ·
          refine ⟨5991409640448328087770955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127816738996230999205780373 5991409640448328087770955)
          ·
            refine ⟨8987114460672492131656433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991409640448328087770955 8987114460672492131656433)
            ·
              refine ⟨6740335845504369098742325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8987114460672492131656433 6740335845504369098742325)
              ·
                refine ⟨631906485516034603007093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6740335845504369098742325 631906485516034603007093)
                ·
                  refine ⟨59241233017128244031915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631906485516034603007093 59241233017128244031915)
                  ·
                    rfl

theorem cell23_1038347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 5].length) (baseStart_1038347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038347 prefixEnd_1038347 := by exact prefixLift 1038347
  have htrace : WordTrace (prefixWord ++ tailWord_1038347) baseStart_1038347 baseEnd_1038347 := by
    simpa [prefixWord, tailWord_1038347, baseEnd_1038347] using wordTrace_append hprefix tailTrace_1038347
  have hstable : (prefixWord ++ tailWord_1038347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038347).length < 2 ^ (prefixWord ++ tailWord_1038347).sum := by decide
  have hdescent : baseEnd_1038347 < baseStart_1038347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038364 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 5]
def baseStart_1038364 : Nat := 118140960795 + 1038364 * 2 ^ 59
def prefixEnd_1038364 : Nat := 4983230072969 + 3 ^ 40 * 1038364 * 2
def baseEnd_1038364 : Nat := 59242202925031181086073

theorem tailTrace_1038364 : CollatzResearch.WordTrace tailWord_1038364 prefixEnd_1038364 59242202925031181086073 := by
  unfold tailWord_1038364
  simp only [CollatzResearch.WordTrace]
  refine ⟨18936123205096020648837073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25248164273461360865116097 18936123205096020648837073)
  ·
    refine ⟨14202092403822015486627805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18936123205096020648837073 14202092403822015486627805)
    ·
      refine ⟨5325784651433255807485427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14202092403822015486627805 5325784651433255807485427)
      ·
        refine ⟨7988676977149883711228141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325784651433255807485427 7988676977149883711228141)
        ·
          refine ⟨2995753866431206391710553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7988676977149883711228141 2995753866431206391710553)
          ·
            refine ⟨2246815399823404793782915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995753866431206391710553 2246815399823404793782915)
            ·
              refine ⟨3370223099735107190674373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246815399823404793782915 3370223099735107190674373)
              ·
                refine ⟨631916831200332598251445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3370223099735107190674373 631916831200332598251445)
                ·
                  refine ⟨59242202925031181086073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631916831200332598251445 59242202925031181086073)
                  ·
                    rfl

theorem cell23_1038364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_1038364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038364 prefixEnd_1038364 := by exact prefixLift 1038364
  have htrace : WordTrace (prefixWord ++ tailWord_1038364) baseStart_1038364 baseEnd_1038364 := by
    simpa [prefixWord, tailWord_1038364, baseEnd_1038364] using wordTrace_append hprefix tailTrace_1038364
  have hstable : (prefixWord ++ tailWord_1038364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038364).length < 2 ^ (prefixWord ++ tailWord_1038364).sum := by decide
  have hdescent : baseEnd_1038364 < baseStart_1038364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038367 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 7, 2]
def baseStart_1038367 : Nat := 118140960795 + 1038367 * 2 ^ 59
def prefixEnd_1038367 : Nat := 4983230072969 + 3 ^ 40 * 1038367 * 2
def baseEnd_1038367 : Nat := 533181366767244118037143

theorem tailTrace_1038367 : CollatzResearch.WordTrace tailWord_1038367 prefixEnd_1038367 533181366767244118037143 := by
  unfold tailWord_1038367
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872355829181172810033355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25248237219454115206688903 37872355829181172810033355)
  ·
    refine ⟨56808533743771759215050033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37872355829181172810033355 56808533743771759215050033)
    ·
      refine ⟨42606400307828819411287525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56808533743771759215050033 42606400307828819411287525)
      ·
        refine ⟨7988700057717903639616411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42606400307828819411287525 7988700057717903639616411)
        ·
          refine ⟨11983050086576855459424617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988700057717903639616411 11983050086576855459424617)
          ·
            refine ⟨8987287564932641594568463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11983050086576855459424617 8987287564932641594568463)
            ·
              refine ⟨13480931347398962391852695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987287564932641594568463 13480931347398962391852695)
              ·
                refine ⟨20221397021098443587779043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13480931347398962391852695 20221397021098443587779043)
                ·
                  refine ⟨30332095531647665381668565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20221397021098443587779043 30332095531647665381668565)
                  ·
                    refine ⟨710908489022992157382857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30332095531647665381668565 710908489022992157382857)
                    ·
                      refine ⟨533181366767244118037143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710908489022992157382857 533181366767244118037143)
                      ·
                        rfl

theorem cell23_1038367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_1038367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038367 prefixEnd_1038367 := by exact prefixLift 1038367
  have htrace : WordTrace (prefixWord ++ tailWord_1038367) baseStart_1038367 baseEnd_1038367 := by
    simpa [prefixWord, tailWord_1038367, baseEnd_1038367] using wordTrace_append hprefix tailTrace_1038367
  have hstable : (prefixWord ++ tailWord_1038367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038367).length < 2 ^ (prefixWord ++ tailWord_1038367).sum := by decide
  have hdescent : baseEnd_1038367 < baseStart_1038367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038397 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1038397 : Nat := 118140960795 + 1038397 * 2 ^ 59
def prefixEnd_1038397 : Nat := 4983230072969 + 3 ^ 40 * 1038397 * 2
def baseEnd_1038397 : Nat := 533196771186879000662005

theorem tailTrace_1038397 : CollatzResearch.WordTrace tailWord_1038397 prefixEnd_1038397 533196771186879000662005 := by
  unfold tailWord_1038397
  simp only [CollatzResearch.WordTrace]
  refine ⟨37873450019072487933625445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25248966679381658622416963 37873450019072487933625445)
  ·
    refine ⟨7101271878576091487554771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37873450019072487933625445 7101271878576091487554771)
    ·
      refine ⟨10651907817864137231332157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7101271878576091487554771 10651907817864137231332157)
      ·
        refine ⟨3994465431699051461749559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10651907817864137231332157 3994465431699051461749559)
        ·
          refine ⟨5991698147548577192624339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994465431699051461749559 5991698147548577192624339)
          ·
            refine ⟨8987547221322865788936509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991698147548577192624339 8987547221322865788936509)
            ·
              refine ⟨3370330207996074670851191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8987547221322865788936509 3370330207996074670851191)
              ·
                refine ⟨5055495311994112006276787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370330207996074670851191 5055495311994112006276787)
                ·
                  refine ⟨7583242967991168009415181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055495311994112006276787 7583242967991168009415181)
                  ·
                    refine ⟨2843716112996688003530693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7583242967991168009415181 2843716112996688003530693)
                    ·
                      refine ⟨533196771186879000662005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2843716112996688003530693 533196771186879000662005)
                      ·
                        rfl

theorem cell23_1038397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1038397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038397 prefixEnd_1038397 := by exact prefixLift 1038397
  have htrace : WordTrace (prefixWord ++ tailWord_1038397) baseStart_1038397 baseEnd_1038397 := by
    simpa [prefixWord, tailWord_1038397, baseEnd_1038397] using wordTrace_append hprefix tailTrace_1038397
  have hstable : (prefixWord ++ tailWord_1038397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038397).length < 2 ^ (prefixWord ++ tailWord_1038397).sum := by decide
  have hdescent : baseEnd_1038397 < baseStart_1038397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038407 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 5, 4]
def baseStart_1038407 : Nat := 118140960795 + 1038407 * 2 ^ 59
def prefixEnd_1038407 : Nat := 4983230072969 + 3 ^ 40 * 1038407 * 2
def baseEnd_1038407 : Nat := 177733968664474653845653

theorem tailTrace_1038407 : CollatzResearch.WordTrace tailWord_1038407 prefixEnd_1038407 177733968664474653845653 := by
  unfold tailWord_1038407
  simp only [CollatzResearch.WordTrace]
  refine ⟨37873814749036259641489475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25249209832690839760992983 37873814749036259641489475)
  ·
    refine ⟨56810722123554389462234213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37873814749036259641489475 56810722123554389462234213)
    ·
      refine ⟨10652010398166448024168915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56810722123554389462234213 10652010398166448024168915)
      ·
        refine ⟨15978015597249672036253373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10652010398166448024168915 15978015597249672036253373)
        ·
          refine ⟨5991755848968627013595015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15978015597249672036253373 5991755848968627013595015)
          ·
            refine ⟨8987633773452940520392523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991755848968627013595015 8987633773452940520392523)
            ·
              refine ⟨13481450660179410780588785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8987633773452940520392523 13481450660179410780588785)
              ·
                refine ⟨10111087995134558085441589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13481450660179410780588785 10111087995134558085441589)
                ·
                  refine ⟨947914499543864820510149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10111087995134558085441589 947914499543864820510149)
                  ·
                    refine ⟨177733968664474653845653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947914499543864820510149 177733968664474653845653)
                    ·
                      rfl

theorem cell23_1038407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_1038407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038407 prefixEnd_1038407 := by exact prefixLift 1038407
  have htrace : WordTrace (prefixWord ++ tailWord_1038407) baseStart_1038407 baseEnd_1038407 := by
    simpa [prefixWord, tailWord_1038407, baseEnd_1038407] using wordTrace_append hprefix tailTrace_1038407
  have hstable : (prefixWord ++ tailWord_1038407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038407).length < 2 ^ (prefixWord ++ tailWord_1038407).sum := by decide
  have hdescent : baseEnd_1038407 < baseStart_1038407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038414 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_1038414 : Nat := 118140960795 + 1038414 * 2 ^ 59
def prefixEnd_1038414 : Nat := 4983230072969 + 3 ^ 40 * 1038414 * 2
def baseEnd_1038414 : Nat := 533205500358005434149427

theorem tailTrace_1038414 : CollatzResearch.WordTrace tailWord_1038414 prefixEnd_1038414 533205500358005434149427 := by
  unfold tailWord_1038414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4734258757501362479624287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25249380040007266557996197 4734258757501362479624287)
  ·
    refine ⟨7101388136252043719436431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4734258757501362479624287 7101388136252043719436431)
    ·
      refine ⟨10652082204378065579154647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7101388136252043719436431 10652082204378065579154647)
      ·
        refine ⟨15978123306567098368731971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10652082204378065579154647 15978123306567098368731971)
        ·
          refine ⟨23967184959850647553097957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15978123306567098368731971 23967184959850647553097957)
          ·
            refine ⟨4493847179971996416205867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23967184959850647553097957 4493847179971996416205867)
            ·
              refine ⟨6740770769957994624308801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493847179971996416205867 6740770769957994624308801)
              ·
                refine ⟨5055578077468495968231601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6740770769957994624308801 5055578077468495968231601)
                ·
                  refine ⟨3791683558101371976173701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5055578077468495968231601 3791683558101371976173701)
                  ·
                    refine ⟨710940667144007245532569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3791683558101371976173701 710940667144007245532569)
                    ·
                      refine ⟨533205500358005434149427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 710940667144007245532569 533205500358005434149427)
                      ·
                        rfl

theorem cell23_1038414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_1038414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038414 prefixEnd_1038414 := by exact prefixLift 1038414
  have htrace : WordTrace (prefixWord ++ tailWord_1038414) baseStart_1038414 baseEnd_1038414 := by
    simpa [prefixWord, tailWord_1038414, baseEnd_1038414] using wordTrace_append hprefix tailTrace_1038414
  have hstable : (prefixWord ++ tailWord_1038414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038414).length < 2 ^ (prefixWord ++ tailWord_1038414).sum := by decide
  have hdescent : baseEnd_1038414 < baseStart_1038414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038417 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_1038417 : Nat := 118140960795 + 1038417 * 2 ^ 59
def prefixEnd_1038417 : Nat := 4983230072969 + 3 ^ 40 * 1038417 * 2
def baseEnd_1038417 : Nat := 533207040799968922411913

theorem tailTrace_1038417 : CollatzResearch.WordTrace tailWord_1038417 prefixEnd_1038417 533207040799968922411913 := by
  unfold tailWord_1038417
  simp only [CollatzResearch.WordTrace]
  refine ⟨37874179479000031349353505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25249452986000020899569003 37874179479000031349353505)
  ·
    refine ⟨28405634609250023512015129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37874179479000031349353505 28405634609250023512015129)
    ·
      refine ⟨21304225956937517634011347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28405634609250023512015129 21304225956937517634011347)
      ·
        refine ⟨31956338935406276451017021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21304225956937517634011347 31956338935406276451017021)
        ·
          refine ⟨11983627100777353669131383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31956338935406276451017021 11983627100777353669131383)
          ·
            refine ⟨17975440651166030503697075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983627100777353669131383 17975440651166030503697075)
            ·
              refine ⟨26963160976749045755545613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17975440651166030503697075 26963160976749045755545613)
              ·
                refine ⟨10111185366280892158329605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26963160976749045755545613 10111185366280892158329605)
                ·
                  refine ⟨1895847256177667279686801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10111185366280892158329605 1895847256177667279686801)
                  ·
                    refine ⟨1421885442133250459765101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895847256177667279686801 1421885442133250459765101)
                    ·
                      refine ⟨533207040799968922411913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1421885442133250459765101 533207040799968922411913)
                      ·
                        rfl

theorem cell23_1038417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_1038417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038417 prefixEnd_1038417 := by exact prefixLift 1038417
  have htrace : WordTrace (prefixWord ++ tailWord_1038417) baseStart_1038417 baseEnd_1038417 := by
    simpa [prefixWord, tailWord_1038417, baseEnd_1038417] using wordTrace_append hprefix tailTrace_1038417
  have hstable : (prefixWord ++ tailWord_1038417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038417).length < 2 ^ (prefixWord ++ tailWord_1038417).sum := by decide
  have hdescent : baseEnd_1038417 < baseStart_1038417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038424 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_1038424 : Nat := 118140960795 + 1038424 * 2 ^ 59
def prefixEnd_1038424 : Nat := 4983230072969 + 3 ^ 40 * 1038424 * 2
def baseEnd_1038424 : Nat := 177736878388183465008127

theorem tailTrace_1038424 : CollatzResearch.WordTrace tailWord_1038424 prefixEnd_1038424 177736878388183465008127 := by
  unfold tailWord_1038424
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937217394987335772429163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25249623193316447696572217 18937217394987335772429163)
  ·
    refine ⟨28405826092481003658643745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18937217394987335772429163 28405826092481003658643745)
    ·
      refine ⟨21304369569360752743982809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28405826092481003658643745 21304369569360752743982809)
      ·
        refine ⟨15978277177020564557987107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21304369569360752743982809 15978277177020564557987107)
        ·
          refine ⟨23967415765530846836980661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15978277177020564557987107 23967415765530846836980661)
          ·
            refine ⟨2246945228018516890966937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23967415765530846836980661 2246945228018516890966937)
            ·
              refine ⟨1685208921013887668225203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246945228018516890966937 1685208921013887668225203)
              ·
                refine ⟨2527813381520831502337805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685208921013887668225203 2527813381520831502337805)
                ·
                  refine ⟨947930018070311813376677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2527813381520831502337805 947930018070311813376677)
                  ·
                    refine ⟨177736878388183465008127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947930018070311813376677 177736878388183465008127)
                    ·
                      rfl

theorem cell23_1038424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_1038424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038424 prefixEnd_1038424 := by exact prefixLift 1038424
  have htrace : WordTrace (prefixWord ++ tailWord_1038424) baseStart_1038424 baseEnd_1038424 := by
    simpa [prefixWord, tailWord_1038424, baseEnd_1038424] using wordTrace_append hprefix tailTrace_1038424
  have hstable : (prefixWord ++ tailWord_1038424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038424).length < 2 ^ (prefixWord ++ tailWord_1038424).sum := by decide
  have hdescent : baseEnd_1038424 < baseStart_1038424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038488 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 6]
def baseStart_1038488 : Nat := 118140960795 + 1038488 * 2 ^ 59
def prefixEnd_1038488 : Nat := 4983230072969 + 3 ^ 40 * 1038488 * 2
def baseEnd_1038488 : Nat := 59249277547382016069343

theorem tailTrace_1038488 : CollatzResearch.WordTrace tailWord_1038488 prefixEnd_1038488 59249277547382016069343 := by
  unfold tailWord_1038488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18938384530871405237594059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25251179374495206983458745 18938384530871405237594059)
  ·
    refine ⟨28407576796307107856391089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18938384530871405237594059 28407576796307107856391089)
    ·
      refine ⟨21305682597230330892293317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28407576796307107856391089 21305682597230330892293317)
      ·
        refine ⟨3994815486980687042304997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21305682597230330892293317 3994815486980687042304997)
        ·
          refine ⟨749027903808878820432187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3994815486980687042304997 749027903808878820432187)
          ·
            refine ⟨1123541855713318230648281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749027903808878820432187 1123541855713318230648281)
            ·
              refine ⟨842656391784988672986211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123541855713318230648281 842656391784988672986211)
              ·
                refine ⟨1263984587677483009479317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842656391784988672986211 1263984587677483009479317)
                ·
                  refine ⟨59249277547382016069343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1263984587677483009479317 59249277547382016069343)
                  ·
                    rfl

theorem cell23_1038488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 6].length) (baseStart_1038488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038488 prefixEnd_1038488 := by exact prefixLift 1038488
  have htrace : WordTrace (prefixWord ++ tailWord_1038488) baseStart_1038488 baseEnd_1038488 := by
    simpa [prefixWord, tailWord_1038488, baseEnd_1038488] using wordTrace_append hprefix tailTrace_1038488
  have hstable : (prefixWord ++ tailWord_1038488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038488).length < 2 ^ (prefixWord ++ tailWord_1038488).sum := by decide
  have hdescent : baseEnd_1038488 < baseStart_1038488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038521 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1038521 : Nat := 118140960795 + 1038521 * 2 ^ 59
def prefixEnd_1038521 : Nat := 4983230072969 + 3 ^ 40 * 1038521 * 2
def baseEnd_1038521 : Nat := 533260442788036515511435

theorem tailTrace_1038521 : CollatzResearch.WordTrace tailWord_1038521 prefixEnd_1038521 533260442788036515511435 := by
  unfold tailWord_1038521
  simp only [CollatzResearch.WordTrace]
  refine ⟨37877972670623257111139417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25251981780415504740759611 37877972670623257111139417)
  ·
    refine ⟨28408479502967442833354563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37877972670623257111139417 28408479502967442833354563)
    ·
      refine ⟨42612719254451164250031845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28408479502967442833354563 42612719254451164250031845)
      ·
        refine ⟨7989884860209593296880971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42612719254451164250031845 7989884860209593296880971)
        ·
          refine ⟨11984827290314389945321457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7989884860209593296880971 11984827290314389945321457)
          ·
            refine ⟨8988620467735792458991093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11984827290314389945321457 8988620467735792458991093)
            ·
              refine ⟨842683168850230543030415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8988620467735792458991093 842683168850230543030415)
              ·
                refine ⟨1264024753275345814545623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842683168850230543030415 1264024753275345814545623)
                ·
                  refine ⟨1896037129913018721818435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264024753275345814545623 1896037129913018721818435)
                  ·
                    refine ⟨2844055694869528082727653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1896037129913018721818435 2844055694869528082727653)
                    ·
                      refine ⟨533260442788036515511435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2844055694869528082727653 533260442788036515511435)
                      ·
                        rfl

theorem cell23_1038521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1038521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038521 prefixEnd_1038521 := by exact prefixLift 1038521
  have htrace : WordTrace (prefixWord ++ tailWord_1038521) baseStart_1038521 baseEnd_1038521 := by
    simpa [prefixWord, tailWord_1038521, baseEnd_1038521] using wordTrace_append hprefix tailTrace_1038521
  have hstable : (prefixWord ++ tailWord_1038521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038521).length < 2 ^ (prefixWord ++ tailWord_1038521).sum := by decide
  have hdescent : baseEnd_1038521 < baseStart_1038521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038532 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1038532 : Nat := 118140960795 + 1038532 * 2 ^ 59
def prefixEnd_1038532 : Nat := 4983230072969 + 3 ^ 40 * 1038532 * 2
def baseEnd_1038532 : Nat := 533266091075235972473885

theorem tailTrace_1038532 : CollatzResearch.WordTrace tailWord_1038532 prefixEnd_1038532 533266091075235972473885 := by
  unfold tailWord_1038532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939186936791702994894925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25252249249055603993193233 18939186936791702994894925)
  ·
    refine ⟨7102195101296888623085597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18939186936791702994894925 7102195101296888623085597)
    ·
      refine ⟨2663323162986333233657099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7102195101296888623085597 2663323162986333233657099)
      ·
        refine ⟨3994984744479499850485649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663323162986333233657099 3994984744479499850485649)
        ·
          refine ⟨2996238558359624887864237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3994984744479499850485649 2996238558359624887864237)
          ·
            refine ⟨1123589459384859332949089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996238558359624887864237 1123589459384859332949089)
            ·
              refine ⟨842692094538644499711817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123589459384859332949089 842692094538644499711817)
              ·
                refine ⟨632019070903983374783863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842692094538644499711817 632019070903983374783863)
                ·
                  refine ⟨948028606355975062175795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632019070903983374783863 948028606355975062175795)
                  ·
                    refine ⟨1422042909533962593263693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948028606355975062175795 1422042909533962593263693)
                    ·
                      refine ⟨533266091075235972473885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422042909533962593263693 533266091075235972473885)
                      ·
                        rfl

theorem cell23_1038532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1038532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038532 prefixEnd_1038532 := by exact prefixLift 1038532
  have htrace : WordTrace (prefixWord ++ tailWord_1038532) baseStart_1038532 baseEnd_1038532 := by
    simpa [prefixWord, tailWord_1038532, baseEnd_1038532] using wordTrace_append hprefix tailTrace_1038532
  have hstable : (prefixWord ++ tailWord_1038532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038532).length < 2 ^ (prefixWord ++ tailWord_1038532).sum := by decide
  have hdescent : baseEnd_1038532 < baseStart_1038532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038554 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1038554 : Nat := 118140960795 + 1038554 * 2 ^ 59
def prefixEnd_1038554 : Nat := 4983230072969 + 3 ^ 40 * 1038554 * 2
def baseEnd_1038554 : Nat := 533277387649634886398783

theorem tailTrace_1038554 : CollatzResearch.WordTrace tailWord_1038554 prefixEnd_1038554 533277387649634886398783 := by
  unfold tailWord_1038554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9469794069875925936772679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25252784186335802498060477 9469794069875925936772679)
  ·
    refine ⟨14204691104813888905159019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9469794069875925936772679 14204691104813888905159019)
    ·
      refine ⟨21307036657220833357738529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14204691104813888905159019 21307036657220833357738529)
      ·
        refine ⟨15980277492915625018303897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21307036657220833357738529 15980277492915625018303897)
        ·
          refine ⟨11985208119686718763727923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15980277492915625018303897 11985208119686718763727923)
          ·
            refine ⟨17977812179530078145591885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11985208119686718763727923 17977812179530078145591885)
            ·
              refine ⟨6741679567323779304596957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17977812179530078145591885 6741679567323779304596957)
              ·
                refine ⟨2528129837746417239223859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6741679567323779304596957 2528129837746417239223859)
                ·
                  refine ⟨3792194756619625858835789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528129837746417239223859 3792194756619625858835789)
                  ·
                    refine ⟨1422073033732359697063421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3792194756619625858835789 1422073033732359697063421)
                    ·
                      refine ⟨533277387649634886398783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422073033732359697063421 533277387649634886398783)
                      ·
                        rfl

theorem cell23_1038554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1038554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038554 prefixEnd_1038554 := by exact prefixLift 1038554
  have htrace : WordTrace (prefixWord ++ tailWord_1038554) baseStart_1038554 baseEnd_1038554 := by
    simpa [prefixWord, tailWord_1038554, baseEnd_1038554] using wordTrace_append hprefix tailTrace_1038554
  have hstable : (prefixWord ++ tailWord_1038554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038554).length < 2 ^ (prefixWord ++ tailWord_1038554).sum := by decide
  have hdescent : baseEnd_1038554 < baseStart_1038554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038588 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_1038588 : Nat := 118140960795 + 1038588 * 2 ^ 59
def prefixEnd_1038588 : Nat := 4983230072969 + 3 ^ 40 * 1038588 * 2
def baseEnd_1038588 : Nat := 533294845991887753373627

theorem tailTrace_1038588 : CollatzResearch.WordTrace tailWord_1038588 prefixEnd_1038588 533294845991887753373627 := by
  unfold tailWord_1038588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940208180690263776914209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25253610907587018369218945 18940208180690263776914209)
  ·
    refine ⟨14205156135517697832685657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18940208180690263776914209 14205156135517697832685657)
    ·
      refine ⟨10653867101638273374514243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14205156135517697832685657 10653867101638273374514243)
      ·
        refine ⟨15980800652457410061771365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10653867101638273374514243 15980800652457410061771365)
        ·
          refine ⟨2996400122335764386582131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15980800652457410061771365 2996400122335764386582131)
          ·
            refine ⟨4494600183503646579873197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996400122335764386582131 4494600183503646579873197)
            ·
              refine ⟨1685475068813867467452449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4494600183503646579873197 1685475068813867467452449)
              ·
                refine ⟨1264106301610400600589337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685475068813867467452449 1264106301610400600589337)
                ·
                  refine ⟨948079726207800450442003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1264106301610400600589337 948079726207800450442003)
                  ·
                    refine ⟨1422119589311700675663005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948079726207800450442003 1422119589311700675663005)
                    ·
                      refine ⟨533294845991887753373627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422119589311700675663005 533294845991887753373627)
                      ·
                        rfl

theorem cell23_1038588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_1038588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038588 prefixEnd_1038588 := by exact prefixLift 1038588
  have htrace : WordTrace (prefixWord ++ tailWord_1038588) baseStart_1038588 baseEnd_1038588 := by
    simpa [prefixWord, tailWord_1038588, baseEnd_1038588] using wordTrace_append hprefix tailTrace_1038588
  have hstable : (prefixWord ++ tailWord_1038588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038588).length < 2 ^ (prefixWord ++ tailWord_1038588).sum := by decide
  have hdescent : baseEnd_1038588 < baseStart_1038588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038597 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_1038597 : Nat := 118140960795 + 1038597 * 2 ^ 59
def prefixEnd_1038597 : Nat := 4983230072969 + 3 ^ 40 * 1038597 * 2
def baseEnd_1038597 : Nat := 533299467317778218161085

theorem tailTrace_1038597 : CollatzResearch.WordTrace tailWord_1038597 prefixEnd_1038597 533299467317778218161085 := by
  unfold tailWord_1038597
  simp only [CollatzResearch.WordTrace]
  refine ⟨37880744618347922090906045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25253829745565281393937363 37880744618347922090906045)
  ·
    refine ⟨14205279231880470784089767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37880744618347922090906045 14205279231880470784089767)
    ·
      refine ⟨21307918847820706176134651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205279231880470784089767 21307918847820706176134651)
      ·
        refine ⟨31961878271731059264201977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21307918847820706176134651 31961878271731059264201977)
        ·
          refine ⟨23971408703798294448151483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31961878271731059264201977 23971408703798294448151483)
          ·
            refine ⟨35957113055697441672227225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23971408703798294448151483 35957113055697441672227225)
            ·
              refine ⟨26967834791773081254170419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35957113055697441672227225 26967834791773081254170419)
              ·
                refine ⟨40451752187659621881255629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26967834791773081254170419 40451752187659621881255629)
                ·
                  refine ⟨15169407070372358205470861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40451752187659621881255629 15169407070372358205470861)
                  ·
                    refine ⟨5688527651389634327051573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15169407070372358205470861 5688527651389634327051573)
                    ·
                      refine ⟨533299467317778218161085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5688527651389634327051573 533299467317778218161085)
                      ·
                        rfl

theorem cell23_1038597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_1038597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038597 prefixEnd_1038597 := by exact prefixLift 1038597
  have htrace : WordTrace (prefixWord ++ tailWord_1038597) baseStart_1038597 baseEnd_1038597 := by
    simpa [prefixWord, tailWord_1038597, baseEnd_1038597] using wordTrace_append hprefix tailTrace_1038597
  have hstable : (prefixWord ++ tailWord_1038597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038597).length < 2 ^ (prefixWord ++ tailWord_1038597).sum := by decide
  have hdescent : baseEnd_1038597 < baseStart_1038597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038628 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_1038628 : Nat := 118140960795 + 1038628 * 2 ^ 59
def prefixEnd_1038628 : Nat := 4983230072969 + 3 ^ 40 * 1038628 * 2
def baseEnd_1038628 : Nat := 533315385218067596873443

theorem tailTrace_1038628 : CollatzResearch.WordTrace tailWord_1038628 prefixEnd_1038628 533315385218067596873443 := by
  unfold tailWord_1038628
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940937640617807192642269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25254583520823742923523025 18940937640617807192642269)
  ·
    refine ⟨7102851615231677697240851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18940937640617807192642269 7102851615231677697240851)
    ·
      refine ⟨10654277422847516545861277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7102851615231677697240851 10654277422847516545861277)
      ·
        refine ⟨3995354033567818704697979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10654277422847516545861277 3995354033567818704697979)
        ·
          refine ⟨5993031050351728057046969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995354033567818704697979 5993031050351728057046969)
          ·
            refine ⟨4494773287763796042785227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5993031050351728057046969 4494773287763796042785227)
            ·
              refine ⟨6742159931645694064177841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494773287763796042785227 6742159931645694064177841)
              ·
                refine ⟨5056619948734270548133381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6742159931645694064177841 5056619948734270548133381)
                ·
                  refine ⟨948116240387675727775009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5056619948734270548133381 948116240387675727775009)
                  ·
                    refine ⟨711087180290756795831257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948116240387675727775009 711087180290756795831257)
                    ·
                      refine ⟨533315385218067596873443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711087180290756795831257 533315385218067596873443)
                      ·
                        rfl

theorem cell23_1038628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_1038628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038628 prefixEnd_1038628 := by exact prefixLift 1038628
  have htrace : WordTrace (prefixWord ++ tailWord_1038628) baseStart_1038628 baseEnd_1038628 := by
    simpa [prefixWord, tailWord_1038628, baseEnd_1038628] using wordTrace_append hprefix tailTrace_1038628
  have hstable : (prefixWord ++ tailWord_1038628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038628).length < 2 ^ (prefixWord ++ tailWord_1038628).sum := by decide
  have hdescent : baseEnd_1038628 < baseStart_1038628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038701 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1038701 : Nat := 118140960795 + 1038701 * 2 ^ 59
def prefixEnd_1038701 : Nat := 4983230072969 + 3 ^ 40 * 1038701 * 2
def baseEnd_1038701 : Nat := 533352869305845811260607

theorem tailTrace_1038701 : CollatzResearch.WordTrace tailWord_1038701 prefixEnd_1038701 533352869305845811260607 := by
  unfold tailWord_1038701
  simp only [CollatzResearch.WordTrace]
  refine ⟨37884537809971147852691957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25256358539980765235127971 37884537809971147852691957)
  ·
    refine ⟨3551675419684795111189871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37884537809971147852691957 3551675419684795111189871)
    ·
      refine ⟨5327513129527192666784807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551675419684795111189871 5327513129527192666784807)
      ·
        refine ⟨7991269694290789000177211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327513129527192666784807 7991269694290789000177211)
        ·
          refine ⟨11986904541436183500265817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991269694290789000177211 11986904541436183500265817)
          ·
            refine ⟨8990178406077137625199363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11986904541436183500265817 8990178406077137625199363)
            ·
              refine ⟨13485267609115706437799045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8990178406077137625199363 13485267609115706437799045)
              ·
                refine ⟨2528487676709194957087321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13485267609115706437799045 2528487676709194957087321)
                ·
                  refine ⟨1896365757531896217815491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528487676709194957087321 1896365757531896217815491)
                  ·
                    refine ⟨2844548636297844326723237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1896365757531896217815491 2844548636297844326723237)
                    ·
                      refine ⟨533352869305845811260607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2844548636297844326723237 533352869305845811260607)
                      ·
                        rfl

theorem cell23_1038701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1038701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038701 prefixEnd_1038701 := by exact prefixLift 1038701
  have htrace : WordTrace (prefixWord ++ tailWord_1038701) baseStart_1038701 baseEnd_1038701 := by
    simpa [prefixWord, tailWord_1038701, baseEnd_1038701] using wordTrace_append hprefix tailTrace_1038701
  have hstable : (prefixWord ++ tailWord_1038701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038701).length < 2 ^ (prefixWord ++ tailWord_1038701).sum := by decide
  have hdescent : baseEnd_1038701 < baseStart_1038701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038819 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1038819 : Nat := 118140960795 + 1038819 * 2 ^ 59
def prefixEnd_1038819 : Nat := 4983230072969 + 3 ^ 40 * 1038819 * 2
def baseEnd_1038819 : Nat := 533413460023076349585065

theorem tailTrace_1038819 : CollatzResearch.WordTrace tailWord_1038819 prefixEnd_1038819 533413460023076349585065 := by
  unfold tailWord_1038819
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888841623543654005487511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25259227749029102670325007 37888841623543654005487511)
  ·
    refine ⟨56833262435315481008231267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37888841623543654005487511 56833262435315481008231267)
    ·
      refine ⟨85249893652973221512346901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56833262435315481008231267 85249893652973221512346901)
      ·
        refine ⟨3996088764983119758391261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85249893652973221512346901 3996088764983119758391261)
        ·
          refine ⟨1498533286868669909396723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3996088764983119758391261 1498533286868669909396723)
          ·
            refine ⟨2247799930303004864095085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498533286868669909396723 2247799930303004864095085)
            ·
              refine ⟨842924973863626824035657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247799930303004864095085 842924973863626824035657)
              ·
                refine ⟨632193730397720118026743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842924973863626824035657 632193730397720118026743)
                ·
                  refine ⟨948290595596580177040115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632193730397720118026743 948290595596580177040115)
                  ·
                    refine ⟨1422435893394870265560173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948290595596580177040115 1422435893394870265560173)
                    ·
                      refine ⟨533413460023076349585065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422435893394870265560173 533413460023076349585065)
                      ·
                        rfl

theorem cell23_1038819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1038819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038819 prefixEnd_1038819 := by exact prefixLift 1038819
  have htrace : WordTrace (prefixWord ++ tailWord_1038819) baseStart_1038819 baseEnd_1038819 := by
    simpa [prefixWord, tailWord_1038819, baseEnd_1038819] using wordTrace_append hprefix tailTrace_1038819
  have hstable : (prefixWord ++ tailWord_1038819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038819).length < 2 ^ (prefixWord ++ tailWord_1038819).sum := by decide
  have hdescent : baseEnd_1038819 < baseStart_1038819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038838 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1038838 : Nat := 118140960795 + 1038838 * 2 ^ 59
def prefixEnd_1038838 : Nat := 4983230072969 + 3 ^ 40 * 1038838 * 2
def baseEnd_1038838 : Nat := 533423216155511775247477

theorem tailTrace_1038838 : CollatzResearch.WordTrace tailWord_1038838 prefixEnd_1038838 533423216155511775247477 := by
  unfold tailWord_1038838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368095913154676265651823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25259689740316546833619445 2368095913154676265651823)
  ·
    refine ⟨3552143869732014398477735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2368095913154676265651823 3552143869732014398477735)
    ·
      refine ⟨5328215804598021597716603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552143869732014398477735 5328215804598021597716603)
      ·
        refine ⟨7992323706897032396574905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328215804598021597716603 7992323706897032396574905)
        ·
          refine ⟨5994242780172774297431179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992323706897032396574905 5994242780172774297431179)
          ·
            refine ⟨8991364170259161446146769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994242780172774297431179 8991364170259161446146769)
            ·
              refine ⟨6743523127694371084610077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991364170259161446146769 6743523127694371084610077)
              ·
                refine ⟨2528821172885389156728779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6743523127694371084610077 2528821172885389156728779)
                ·
                  refine ⟨3793231759328083735093169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528821172885389156728779 3793231759328083735093169)
                  ·
                    refine ⟨2844923819496062801319877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3793231759328083735093169 2844923819496062801319877)
                    ·
                      refine ⟨533423216155511775247477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2844923819496062801319877 533423216155511775247477)
                      ·
                        rfl

theorem cell23_1038838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1038838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038838 prefixEnd_1038838 := by exact prefixLift 1038838
  have htrace : WordTrace (prefixWord ++ tailWord_1038838) baseStart_1038838 baseEnd_1038838 := by
    simpa [prefixWord, tailWord_1038838, baseEnd_1038838] using wordTrace_append hprefix tailTrace_1038838
  have hstable : (prefixWord ++ tailWord_1038838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038838).length < 2 ^ (prefixWord ++ tailWord_1038838).sum := by decide
  have hdescent : baseEnd_1038838 < baseStart_1038838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038858 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1038858 : Nat := 118140960795 + 1038858 * 2 ^ 59
def prefixEnd_1038858 : Nat := 4983230072969 + 3 ^ 40 * 1038858 * 2
def baseEnd_1038858 : Nat := 533433485768601696997385

theorem tailTrace_1038858 : CollatzResearch.WordTrace tailWord_1038858 prefixEnd_1038858 533433485768601696997385 := by
  unfold tailWord_1038858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472566017600590916539307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25260176046934909110771485 9472566017600590916539307)
  ·
    refine ⟨14208849026400886374808961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9472566017600590916539307 14208849026400886374808961)
    ·
      refine ⟨10656636769800664781106721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14208849026400886374808961 10656636769800664781106721)
      ·
        refine ⟨7992477577350498585830041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656636769800664781106721 7992477577350498585830041)
        ·
          refine ⟨5994358183012873939372531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992477577350498585830041 5994358183012873939372531)
          ·
            refine ⟨8991537274519310909058797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994358183012873939372531 8991537274519310909058797)
            ·
              refine ⟨3371826477944741590897049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8991537274519310909058797 3371826477944741590897049)
              ·
                refine ⟨2528869858458556193172787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371826477944741590897049 2528869858458556193172787)
                ·
                  refine ⟨3793304787687834289759181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2528869858458556193172787 3793304787687834289759181)
                  ·
                    refine ⟨1422489295382937858659693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793304787687834289759181 1422489295382937858659693)
                    ·
                      refine ⟨533433485768601696997385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422489295382937858659693 533433485768601696997385)
                      ·
                        rfl

theorem cell23_1038858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1038858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038858 prefixEnd_1038858 := by exact prefixLift 1038858
  have htrace : WordTrace (prefixWord ++ tailWord_1038858) baseStart_1038858 baseEnd_1038858 := by
    simpa [prefixWord, tailWord_1038858, baseEnd_1038858] using wordTrace_append hprefix tailTrace_1038858
  have hstable : (prefixWord ++ tailWord_1038858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038858).length < 2 ^ (prefixWord ++ tailWord_1038858).sum := by decide
  have hdescent : baseEnd_1038858 < baseStart_1038858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038862 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_1038862 : Nat := 118140960795 + 1038862 * 2 ^ 59
def prefixEnd_1038862 : Nat := 4983230072969 + 3 ^ 40 * 1038862 * 2
def baseEnd_1038862 : Nat := 533435539691219681347367

theorem tailTrace_1038862 : CollatzResearch.WordTrace tailWord_1038862 prefixEnd_1038862 533435539691219681347367 := by
  unfold tailWord_1038862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736301245298484043662855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25260273308258581566201893 4736301245298484043662855)
  ·
    refine ⟨7104451867947726065494283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736301245298484043662855 7104451867947726065494283)
    ·
      refine ⟨10656677801921589098241425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104451867947726065494283 10656677801921589098241425)
      ·
        refine ⟨7992508351441191823681069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656677801921589098241425 7992508351441191823681069)
        ·
          refine ⟨2997190631790446933880401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7992508351441191823681069 2997190631790446933880401)
          ·
            refine ⟨2247892973842835200410301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997190631790446933880401 2247892973842835200410301)
            ·
              refine ⟨842959865191063200153863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247892973842835200410301 842959865191063200153863)
              ·
                refine ⟨1264439797786594800230795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842959865191063200153863 1264439797786594800230795)
                ·
                  refine ⟨1896659696679892200346193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264439797786594800230795 1896659696679892200346193)
                  ·
                    refine ⟨1422494772509919150259645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1896659696679892200346193 1422494772509919150259645)
                    ·
                      refine ⟨533435539691219681347367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422494772509919150259645 533435539691219681347367)
                      ·
                        rfl

theorem cell23_1038862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_1038862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038862 prefixEnd_1038862 := by exact prefixLift 1038862
  have htrace : WordTrace (prefixWord ++ tailWord_1038862) baseStart_1038862 baseEnd_1038862 := by
    simpa [prefixWord, tailWord_1038862, baseEnd_1038862] using wordTrace_append hprefix tailTrace_1038862
  have hstable : (prefixWord ++ tailWord_1038862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038862).length < 2 ^ (prefixWord ++ tailWord_1038862).sum := by decide
  have hdescent : baseEnd_1038862 < baseStart_1038862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038876 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_1038876 : Nat := 118140960795 + 1038876 * 2 ^ 59
def prefixEnd_1038876 : Nat := 4983230072969 + 3 ^ 40 * 1038876 * 2
def baseEnd_1038876 : Nat := 533442728420382626572303

theorem tailTrace_1038876 : CollatzResearch.WordTrace tailWord_1038876 prefixEnd_1038876 533442728420382626572303 := by
  unfold tailWord_1038876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945460292168576370156241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25260613722891435160208321 18945460292168576370156241)
  ·
    refine ⟨14209095219126432277617181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18945460292168576370156241 14209095219126432277617181)
    ·
      refine ⟨5328410707172412104106443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14209095219126432277617181 5328410707172412104106443)
      ·
        refine ⟨7992616060758618156159665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328410707172412104106443 7992616060758618156159665)
        ·
          refine ⟨5994462045568963617119749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992616060758618156159665 5994462045568963617119749)
          ·
            refine ⟨1123961633544180678209953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5994462045568963617119749 1123961633544180678209953)
            ·
              refine ⟨842971225158135508657465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123961633544180678209953 842971225158135508657465)
              ·
                refine ⟨632228418868601631493099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842971225158135508657465 632228418868601631493099)
                ·
                  refine ⟨948342628302902447239649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632228418868601631493099 948342628302902447239649)
                  ·
                    refine ⟨711256971227176835429737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948342628302902447239649 711256971227176835429737)
                    ·
                      refine ⟨533442728420382626572303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711256971227176835429737 533442728420382626572303)
                      ·
                        rfl

theorem cell23_1038876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_1038876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038876 prefixEnd_1038876 := by exact prefixLift 1038876
  have htrace : WordTrace (prefixWord ++ tailWord_1038876) baseStart_1038876 baseEnd_1038876 := by
    simpa [prefixWord, tailWord_1038876, baseEnd_1038876] using wordTrace_append hprefix tailTrace_1038876
  have hstable : (prefixWord ++ tailWord_1038876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038876).length < 2 ^ (prefixWord ++ tailWord_1038876).sum := by decide
  have hdescent : baseEnd_1038876 < baseStart_1038876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038881 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1038881 : Nat := 118140960795 + 1038881 * 2 ^ 59
def prefixEnd_1038881 : Nat := 4983230072969 + 3 ^ 40 * 1038881 * 2
def baseEnd_1038881 : Nat := 533445295823655107009779

theorem tailTrace_1038881 : CollatzResearch.WordTrace tailWord_1038881 prefixEnd_1038881 533445295823655107009779 := by
  unfold tailWord_1038881
  simp only [CollatzResearch.WordTrace]
  refine ⟨37891102949319038594244497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25260735299546025729496331 37891102949319038594244497)
  ·
    refine ⟨28418327211989278945683373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37891102949319038594244497 28418327211989278945683373)
    ·
      refine ⟨10656872704495979604631265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28418327211989278945683373 10656872704495979604631265)
      ·
        refine ⟨7992654528371984703473449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656872704495979604631265 7992654528371984703473449)
        ·
          refine ⟨5994490896278988527605087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992654528371984703473449 5994490896278988527605087)
          ·
            refine ⟨8991736344418482791407631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994490896278988527605087 8991736344418482791407631)
            ·
              refine ⟨13487604516627724187111447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991736344418482791407631 13487604516627724187111447)
              ·
                refine ⟨20231406774941586280667171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13487604516627724187111447 20231406774941586280667171)
                ·
                  refine ⟨30347110162412379421000757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20231406774941586280667171 30347110162412379421000757)
                  ·
                    refine ⟨2845041577726160570718821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30347110162412379421000757 2845041577726160570718821)
                    ·
                      refine ⟨533445295823655107009779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2845041577726160570718821 533445295823655107009779)
                      ·
                        rfl

theorem cell23_1038881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1038881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038881 prefixEnd_1038881 := by exact prefixLift 1038881
  have htrace : WordTrace (prefixWord ++ tailWord_1038881) baseStart_1038881 baseEnd_1038881 := by
    simpa [prefixWord, tailWord_1038881, baseEnd_1038881] using wordTrace_append hprefix tailTrace_1038881
  have hstable : (prefixWord ++ tailWord_1038881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038881).length < 2 ^ (prefixWord ++ tailWord_1038881).sum := by decide
  have hdescent : baseEnd_1038881 < baseStart_1038881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038902 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1038902 : Nat := 118140960795 + 1038902 * 2 ^ 59
def prefixEnd_1038902 : Nat := 4983230072969 + 3 ^ 40 * 1038902 * 2
def baseEnd_1038902 : Nat := 533456078917399524847183

theorem tailTrace_1038902 : CollatzResearch.WordTrace tailWord_1038902 prefixEnd_1038902 533456078917399524847183 := by
  unfold tailWord_1038902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368241805140184948797435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25261245921495306120505973 2368241805140184948797435)
  ·
    refine ⟨3552362707710277423196153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2368241805140184948797435 3552362707710277423196153)
    ·
      refine ⟨2664272030782708067397115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3552362707710277423196153 2664272030782708067397115)
      ·
        refine ⟨3996408046174062101095673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664272030782708067397115 3996408046174062101095673)
        ·
          refine ⟨2997306034630546575821755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3996408046174062101095673 2997306034630546575821755)
          ·
            refine ⟨4495959051945819863732633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997306034630546575821755 4495959051945819863732633)
            ·
              refine ⟨3371969288959364897799475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4495959051945819863732633 3371969288959364897799475)
              ·
                refine ⟨5057953933439047346699213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371969288959364897799475 5057953933439047346699213)
                ·
                  refine ⟨1896732725039642755012205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5057953933439047346699213 1896732725039642755012205)
                  ·
                    refine ⟨711274771889866033129577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896732725039642755012205 711274771889866033129577)
                    ·
                      refine ⟨533456078917399524847183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711274771889866033129577 533456078917399524847183)
                      ·
                        rfl

theorem cell23_1038902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1038902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038902 prefixEnd_1038902 := by exact prefixLift 1038902
  have htrace : WordTrace (prefixWord ++ tailWord_1038902) baseStart_1038902 baseEnd_1038902 := by
    simpa [prefixWord, tailWord_1038902, baseEnd_1038902] using wordTrace_append hprefix tailTrace_1038902
  have hstable : (prefixWord ++ tailWord_1038902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038902).length < 2 ^ (prefixWord ++ tailWord_1038902).sum := by decide
  have hdescent : baseEnd_1038902 < baseStart_1038902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038911 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1038911 : Nat := 118140960795 + 1038911 * 2 ^ 59
def prefixEnd_1038911 : Nat := 4983230072969 + 3 ^ 40 * 1038911 * 2
def baseEnd_1038911 : Nat := 533460700243289989634641

theorem tailTrace_1038911 : CollatzResearch.WordTrace tailWord_1038911 prefixEnd_1038911 533460700243289989634641 := by
  unfold tailWord_1038911
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892197139210353717836587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25261464759473569145224391 37892197139210353717836587)
  ·
    refine ⟨56838295708815530576754881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37892197139210353717836587 56838295708815530576754881)
    ·
      refine ⟨42628721781611647932566161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56838295708815530576754881 42628721781611647932566161)
      ·
        refine ⟨31971541336208735949424621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42628721781611647932566161 31971541336208735949424621)
        ·
          refine ⟨11989328001078275981034233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31971541336208735949424621 11989328001078275981034233)
          ·
            refine ⟨8991996000808706985775675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989328001078275981034233 8991996000808706985775675)
            ·
              refine ⟨13487994001213060478663513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991996000808706985775675 13487994001213060478663513)
              ·
                refine ⟨10115995500909795358997635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13487994001213060478663513 10115995500909795358997635)
                ·
                  refine ⟨15173993251364693038496453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10115995500909795358997635 15173993251364693038496453)
                  ·
                    refine ⟨2845123734630879944718085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15173993251364693038496453 2845123734630879944718085)
                    ·
                      refine ⟨533460700243289989634641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2845123734630879944718085 533460700243289989634641)
                      ·
                        rfl

theorem cell23_1038911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1038911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038911 prefixEnd_1038911 := by exact prefixLift 1038911
  have htrace : WordTrace (prefixWord ++ tailWord_1038911) baseStart_1038911 baseEnd_1038911 := by
    simpa [prefixWord, tailWord_1038911, baseEnd_1038911] using wordTrace_append hprefix tailTrace_1038911
  have hstable : (prefixWord ++ tailWord_1038911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038911).length < 2 ^ (prefixWord ++ tailWord_1038911).sum := by decide
  have hdescent : baseEnd_1038911 < baseStart_1038911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038919 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_1038919 : Nat := 118140960795 + 1038919 * 2 ^ 59
def prefixEnd_1038919 : Nat := 4983230072969 + 3 ^ 40 * 1038919 * 2
def baseEnd_1038919 : Nat := 533464808088525958334605

theorem tailTrace_1038919 : CollatzResearch.WordTrace tailWord_1038919 prefixEnd_1038919 533464808088525958334605 := by
  unfold tailWord_1038919
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892488923181371084127811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25261659282120914056085207 37892488923181371084127811)
  ·
    refine ⟨56838733384772056626191717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37892488923181371084127811 56838733384772056626191717)
    ·
      refine ⟨10657262509644760617410947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56838733384772056626191717 10657262509644760617410947)
      ·
        refine ⟨15985893764467140926116421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657262509644760617410947 15985893764467140926116421)
        ·
          refine ⟨2997355080837588923646829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15985893764467140926116421 2997355080837588923646829)
          ·
            refine ⟨1124008155314095846367561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2997355080837588923646829 1124008155314095846367561)
            ·
              refine ⟨843006116485571884775671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124008155314095846367561 843006116485571884775671)
              ·
                refine ⟨1264509174728357827163507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843006116485571884775671 1264509174728357827163507)
                ·
                  refine ⟨1896763762092536740745261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264509174728357827163507 1896763762092536740745261)
                  ·
                    refine ⟨711286410784701277779473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896763762092536740745261 711286410784701277779473)
                    ·
                      refine ⟨533464808088525958334605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711286410784701277779473 533464808088525958334605)
                      ·
                        rfl

theorem cell23_1038919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_1038919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038919 prefixEnd_1038919 := by exact prefixLift 1038919
  have htrace : WordTrace (prefixWord ++ tailWord_1038919) baseStart_1038919 baseEnd_1038919 := by
    simpa [prefixWord, tailWord_1038919, baseEnd_1038919] using wordTrace_append hprefix tailTrace_1038919
  have hstable : (prefixWord ++ tailWord_1038919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038919).length < 2 ^ (prefixWord ++ tailWord_1038919).sum := by decide
  have hdescent : baseEnd_1038919 < baseStart_1038919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038932 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_1038932 : Nat := 118140960795 + 1038932 * 2 ^ 59
def prefixEnd_1038932 : Nat := 4983230072969 + 3 ^ 40 * 1038932 * 2
def baseEnd_1038932 : Nat := 533471483337034407472045

theorem tailTrace_1038932 : CollatzResearch.WordTrace tailWord_1038932 prefixEnd_1038932 533471483337034407472045 := by
  unfold tailWord_1038932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946481536067137152175525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25261975381422849536234033 18946481536067137152175525)
  ·
    refine ⟨3552465288012588216032911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18946481536067137152175525 3552465288012588216032911)
    ·
      refine ⟨5328697932018882324049367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552465288012588216032911 5328697932018882324049367)
      ·
        refine ⟨7993046898028323486074051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328697932018882324049367 7993046898028323486074051)
        ·
          refine ⟨11989570347042485229111077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993046898028323486074051 11989570347042485229111077)
          ·
            refine ⟨2248044440070465980458327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11989570347042485229111077 2248044440070465980458327)
            ·
              refine ⟨3372066660105698970687491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248044440070465980458327 3372066660105698970687491)
              ·
                refine ⟨5058099990158548456031237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372066660105698970687491 5058099990158548456031237)
                ·
                  refine ⟨948393748154727835505857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5058099990158548456031237 948393748154727835505857)
                  ·
                    refine ⟨711295311116045876629393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948393748154727835505857 711295311116045876629393)
                    ·
                      refine ⟨533471483337034407472045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711295311116045876629393 533471483337034407472045)
                      ·
                        rfl

theorem cell23_1038932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_1038932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038932 prefixEnd_1038932 := by exact prefixLift 1038932
  have htrace : WordTrace (prefixWord ++ tailWord_1038932) baseStart_1038932 baseEnd_1038932 := by
    simpa [prefixWord, tailWord_1038932, baseEnd_1038932] using wordTrace_append hprefix tailTrace_1038932
  have hstable : (prefixWord ++ tailWord_1038932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038932).length < 2 ^ (prefixWord ++ tailWord_1038932).sum := by decide
  have hdescent : baseEnd_1038932 < baseStart_1038932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038948 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1038948 : Nat := 118140960795 + 1038948 * 2 ^ 59
def prefixEnd_1038948 : Nat := 4983230072969 + 3 ^ 40 * 1038948 * 2
def baseEnd_1038948 : Nat := 533479699027506344871971

theorem tailTrace_1038948 : CollatzResearch.WordTrace tailWord_1038948 prefixEnd_1038948 533479699027506344871971 := by
  unfold tailWord_1038948
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946773320038154518466749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25262364426717539357955665 18946773320038154518466749)
  ·
    refine ⟨7105039995014307944425031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18946773320038154518466749 7105039995014307944425031)
    ·
      refine ⟨10657559992521461916637547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7105039995014307944425031 10657559992521461916637547)
      ·
        refine ⟨15986339988782192874956321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657559992521461916637547 15986339988782192874956321)
        ·
          refine ⟨11989754991586644656217241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15986339988782192874956321 11989754991586644656217241)
          ·
            refine ⟨8992316243689983492162931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989754991586644656217241 8992316243689983492162931)
            ·
              refine ⟨13488474365534975238244397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992316243689983492162931 13488474365534975238244397)
              ·
                refine ⟨5058177887075615714341649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13488474365534975238244397 5058177887075615714341649)
                ·
                  refine ⟨3793633415306711785756237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058177887075615714341649 3793633415306711785756237)
                  ·
                    refine ⟨1422612530740016919658589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3793633415306711785756237 1422612530740016919658589)
                    ·
                      refine ⟨533479699027506344871971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422612530740016919658589 533479699027506344871971)
                      ·
                        rfl

theorem cell23_1038948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1038948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038948 prefixEnd_1038948 := by exact prefixLift 1038948
  have htrace : WordTrace (prefixWord ++ tailWord_1038948) baseStart_1038948 baseEnd_1038948 := by
    simpa [prefixWord, tailWord_1038948, baseEnd_1038948] using wordTrace_append hprefix tailTrace_1038948
  have hstable : (prefixWord ++ tailWord_1038948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038948).length < 2 ^ (prefixWord ++ tailWord_1038948).sum := by decide
  have hdescent : baseEnd_1038948 < baseStart_1038948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038949 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_1038949 : Nat := 118140960795 + 1038949 * 2 ^ 59
def prefixEnd_1038949 : Nat := 4983230072969 + 3 ^ 40 * 1038949 * 2
def baseEnd_1038949 : Nat := 533480212508160840959467

theorem tailTrace_1038949 : CollatzResearch.WordTrace tailWord_1038949 prefixEnd_1038949 533480212508160840959467 := by
  unfold tailWord_1038949
  simp only [CollatzResearch.WordTrace]
  refine ⟨37893583113072686207719901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25262388742048457471813267 37893583113072686207719901)
  ·
    refine ⟨14210093667402257327894963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37893583113072686207719901 14210093667402257327894963)
    ·
      refine ⟨21315140501103385991842445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14210093667402257327894963 21315140501103385991842445)
      ·
        refine ⟨7993177687913769746940917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21315140501103385991842445 7993177687913769746940917)
        ·
          refine ⟨749360408241915913775711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7993177687913769746940917 749360408241915913775711)
          ·
            refine ⟨1124040612362873870663567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749360408241915913775711 1124040612362873870663567)
            ·
              refine ⟨1686060918544310805995351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124040612362873870663567 1686060918544310805995351)
              ·
                refine ⟨2529091377816466208993027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686060918544310805995351 2529091377816466208993027)
                ·
                  refine ⟨3793637066724699313489541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529091377816466208993027 3793637066724699313489541)
                  ·
                    refine ⟨711306950010881121279289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793637066724699313489541 711306950010881121279289)
                    ·
                      refine ⟨533480212508160840959467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711306950010881121279289 533480212508160840959467)
                      ·
                        rfl

theorem cell23_1038949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_1038949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038949 prefixEnd_1038949 := by exact prefixLift 1038949
  have htrace : WordTrace (prefixWord ++ tailWord_1038949) baseStart_1038949 baseEnd_1038949 := by
    simpa [prefixWord, tailWord_1038949, baseEnd_1038949] using wordTrace_append hprefix tailTrace_1038949
  have hstable : (prefixWord ++ tailWord_1038949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038949).length < 2 ^ (prefixWord ++ tailWord_1038949).sum := by decide
  have hdescent : baseEnd_1038949 < baseStart_1038949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038961 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_1038961 : Nat := 118140960795 + 1038961 * 2 ^ 59
def prefixEnd_1038961 : Nat := 4983230072969 + 3 ^ 40 * 1038961 * 2
def baseEnd_1038961 : Nat := 533486374276014794009411

theorem tailTrace_1038961 : CollatzResearch.WordTrace tailWord_1038961 prefixEnd_1038961 533486374276014794009411 := by
  unfold tailWord_1038961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37894020789029212257156737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25262680526019474838104491 37894020789029212257156737)
  ·
    refine ⟨28420515591771909192867553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37894020789029212257156737 28420515591771909192867553)
    ·
      refine ⟨21315386693828931894650665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28420515591771909192867553 21315386693828931894650665)
      ·
        refine ⟨15986540020371698920987999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21315386693828931894650665 15986540020371698920987999)
        ·
          refine ⟨23979810030557548381481999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15986540020371698920987999 23979810030557548381481999)
          ·
            refine ⟨35969715045836322572222999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23979810030557548381481999 35969715045836322572222999)
            ·
              refine ⟨53954572568754483858334499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35969715045836322572222999 53954572568754483858334499)
              ·
                refine ⟨80931858853131725787501749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53954572568754483858334499 80931858853131725787501749)
                ·
                  refine ⟨7587361767481099292578289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80931858853131725787501749 7587361767481099292578289)
                  ·
                    refine ⟨5690521325610824469433717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7587361767481099292578289 5690521325610824469433717)
                    ·
                      refine ⟨533486374276014794009411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5690521325610824469433717 533486374276014794009411)
                      ·
                        rfl

theorem cell23_1038961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_1038961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038961 prefixEnd_1038961 := by exact prefixLift 1038961
  have htrace : WordTrace (prefixWord ++ tailWord_1038961) baseStart_1038961 baseEnd_1038961 := by
    simpa [prefixWord, tailWord_1038961, baseEnd_1038961] using wordTrace_append hprefix tailTrace_1038961
  have hstable : (prefixWord ++ tailWord_1038961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038961).length < 2 ^ (prefixWord ++ tailWord_1038961).sum := by decide
  have hdescent : baseEnd_1038961 < baseStart_1038961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038991 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_1038991 : Nat := 118140960795 + 1038991 * 2 ^ 59
def prefixEnd_1038991 : Nat := 4983230072969 + 3 ^ 40 * 1038991 * 2
def baseEnd_1038991 : Nat := 533501778695649676634273

theorem tailTrace_1038991 : CollatzResearch.WordTrace tailWord_1038991 prefixEnd_1038991 533501778695649676634273 := by
  unfold tailWord_1038991
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895114978920527380748827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25263409985947018253832551 37895114978920527380748827)
  ·
    refine ⟨56842672468380791071123241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37895114978920527380748827 56842672468380791071123241)
    ·
      refine ⟨42632004351285593303342431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56842672468380791071123241 42632004351285593303342431)
      ·
        refine ⟨63948006526928389955013647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42632004351285593303342431 63948006526928389955013647)
        ·
          refine ⟨95922009790392584932520471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63948006526928389955013647 95922009790392584932520471)
          ·
            refine ⟨143883014685588877398780707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95922009790392584932520471 143883014685588877398780707)
            ·
              refine ⟨215824522028383316098171061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143883014685588877398780707 215824522028383316098171061)
              ·
                refine ⟨20233548940160935884203537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215824522028383316098171061 20233548940160935884203537)
                ·
                  refine ⟨15175161705120701913152653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20233548940160935884203537 15175161705120701913152653)
                  ·
                    refine ⟨5690685639420263217432245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15175161705120701913152653 5690685639420263217432245)
                    ·
                      refine ⟨533501778695649676634273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5690685639420263217432245 533501778695649676634273)
                      ·
                        rfl

theorem cell23_1038991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_1038991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1038991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1038991 prefixEnd_1038991 := by exact prefixLift 1038991
  have htrace : WordTrace (prefixWord ++ tailWord_1038991) baseStart_1038991 baseEnd_1038991 := by
    simpa [prefixWord, tailWord_1038991, baseEnd_1038991] using wordTrace_append hprefix tailTrace_1038991
  have hstable : (prefixWord ++ tailWord_1038991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038991).length < 2 ^ (prefixWord ++ tailWord_1038991).sum := by decide
  have hdescent : baseEnd_1038991 < baseStart_1038991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039005 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_1039005 : Nat := 118140960795 + 1039005 * 2 ^ 59
def prefixEnd_1039005 : Nat := 4983230072969 + 3 ^ 40 * 1039005 * 2
def baseEnd_1039005 : Nat := 533508967424812621859209

theorem tailTrace_1039005 : CollatzResearch.WordTrace tailWord_1039005 prefixEnd_1039005 533508967424812621859209 := by
  unfold tailWord_1039005
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895625600869807771758469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25263750400579871847838979 37895625600869807771758469)
  ·
    refine ⟨7105429800163088957204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37895625600869807771758469 7105429800163088957204713)
    ·
      refine ⟨5329072350122316717903535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7105429800163088957204713 5329072350122316717903535)
      ·
        refine ⟨7993608525183475076855303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329072350122316717903535 7993608525183475076855303)
        ·
          refine ⟨11990412787775212615282955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993608525183475076855303 11990412787775212615282955)
          ·
            refine ⟨17985619181662818922924433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990412787775212615282955 17985619181662818922924433)
            ·
              refine ⟨13489214386247114192193325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17985619181662818922924433 13489214386247114192193325)
              ·
                refine ⟨5058455394842667822072497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13489214386247114192193325 5058455394842667822072497)
                ·
                  refine ⟨3793841546132000866554373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5058455394842667822072497 3793841546132000866554373)
                  ·
                    refine ⟨711345289899750162478945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3793841546132000866554373 711345289899750162478945)
                    ·
                      refine ⟨533508967424812621859209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711345289899750162478945 533508967424812621859209)
                      ·
                        rfl

theorem cell23_1039005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_1039005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039005 prefixEnd_1039005 := by exact prefixLift 1039005
  have htrace : WordTrace (prefixWord ++ tailWord_1039005) baseStart_1039005 baseEnd_1039005 := by
    simpa [prefixWord, tailWord_1039005, baseEnd_1039005] using wordTrace_append hprefix tailTrace_1039005
  have hstable : (prefixWord ++ tailWord_1039005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039005).length < 2 ^ (prefixWord ++ tailWord_1039005).sum := by decide
  have hdescent : baseEnd_1039005 < baseStart_1039005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039011 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 10]
def baseStart_1039011 : Nat := 118140960795 + 1039011 * 2 ^ 59
def prefixEnd_1039011 : Nat := 4983230072969 + 3 ^ 40 * 1039011 * 2
def baseEnd_1039011 : Nat := 59279116478748844264909

theorem tailTrace_1039011 : CollatzResearch.WordTrace tailWord_1039011 prefixEnd_1039011 59279116478748844264909 := by
  unfold tailWord_1039011
  simp only [CollatzResearch.WordTrace]
  refine ⟨37895844438848070796476887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25263896292565380530984591 37895844438848070796476887)
  ·
    refine ⟨56843766658272106194715331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37895844438848070796476887 56843766658272106194715331)
    ·
      refine ⟨85265649987408159292072997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56843766658272106194715331 85265649987408159292072997)
      ·
        refine ⟨15987309372639029867263687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85265649987408159292072997 15987309372639029867263687)
        ·
          refine ⟨23980964058958544800895531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15987309372639029867263687 23980964058958544800895531)
          ·
            refine ⟨35971446088437817201343297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23980964058958544800895531 35971446088437817201343297)
            ·
              refine ⟨26978584566328362901007473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35971446088437817201343297 26978584566328362901007473)
              ·
                refine ⟨20233938424746272175755605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26978584566328362901007473 20233938424746272175755605)
                ·
                  refine ⟨59279116478748844264909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20233938424746272175755605 59279116478748844264909)
                  ·
                    rfl

theorem cell23_1039011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 10].length) (baseStart_1039011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039011 prefixEnd_1039011 := by exact prefixLift 1039011
  have htrace : WordTrace (prefixWord ++ tailWord_1039011) baseStart_1039011 baseEnd_1039011 := by
    simpa [prefixWord, tailWord_1039011, baseEnd_1039011] using wordTrace_append hprefix tailTrace_1039011
  have hstable : (prefixWord ++ tailWord_1039011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039011).length < 2 ^ (prefixWord ++ tailWord_1039011).sum := by decide
  have hdescent : baseEnd_1039011 < baseStart_1039011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039022 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1039022 : Nat := 118140960795 + 1039022 * 2 ^ 59
def prefixEnd_1039022 : Nat := 4983230072969 + 3 ^ 40 * 1039022 * 2
def baseEnd_1039022 : Nat := 533517696595939055346631

theorem tailTrace_1039022 : CollatzResearch.WordTrace tailWord_1039022 prefixEnd_1039022 533517696595939055346631 := by
  unfold tailWord_1039022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737030705226027459390915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25264163761205479783418213 4737030705226027459390915)
  ·
    refine ⟨7105546057839041189086373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4737030705226027459390915 7105546057839041189086373)
    ·
      refine ⟨1332289885844820222953695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7105546057839041189086373 1332289885844820222953695)
      ·
        refine ⟨1998434828767230334430543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332289885844820222953695 1998434828767230334430543)
        ·
          refine ⟨2997652243150845501645815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998434828767230334430543 2997652243150845501645815)
          ·
            refine ⟨4496478364726268252468723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997652243150845501645815 4496478364726268252468723)
            ·
              refine ⟨6744717547089402378703085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496478364726268252468723 6744717547089402378703085)
              ·
                refine ⟨2529269080158525892013657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6744717547089402378703085 2529269080158525892013657)
                ·
                  refine ⟨1896951810118894419010243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2529269080158525892013657 1896951810118894419010243)
                  ·
                    refine ⟨2845427715178341628515365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1896951810118894419010243 2845427715178341628515365)
                    ·
                      refine ⟨533517696595939055346631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2845427715178341628515365 533517696595939055346631)
                      ·
                        rfl

theorem cell23_1039022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1039022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039022 prefixEnd_1039022 := by exact prefixLift 1039022
  have htrace : WordTrace (prefixWord ++ tailWord_1039022) baseStart_1039022 baseEnd_1039022 := by
    simpa [prefixWord, tailWord_1039022, baseEnd_1039022] using wordTrace_append hprefix tailTrace_1039022
  have hstable : (prefixWord ++ tailWord_1039022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039022).length < 2 ^ (prefixWord ++ tailWord_1039022).sum := by decide
  have hdescent : baseEnd_1039022 < baseStart_1039022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039065 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 5, 2]
def baseStart_1039065 : Nat := 118140960795 + 1039065 * 2 ^ 59
def prefixEnd_1039065 : Nat := 4983230072969 + 3 ^ 40 * 1039065 * 2
def baseEnd_1039065 : Nat := 533539776264082387108933

theorem tailTrace_1039065 : CollatzResearch.WordTrace tailWord_1039065 prefixEnd_1039065 533539776264082387108933 := by
  unfold tailWord_1039065
  simp only [CollatzResearch.WordTrace]
  refine ⟨37897813980652438018942649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25265209320434958679295099 37897813980652438018942649)
  ·
    refine ⟨28423360485489328514206987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37897813980652438018942649 28423360485489328514206987)
    ·
      refine ⟨42635040728233992771310481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28423360485489328514206987 42635040728233992771310481)
      ·
        refine ⟨31976280546175494578482861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42635040728233992771310481 31976280546175494578482861)
        ·
          refine ⟨11991105204815810466931073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31976280546175494578482861 11991105204815810466931073)
          ·
            refine ⟨8993328903611857850198305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991105204815810466931073 8993328903611857850198305)
            ·
              refine ⟨6744996677708893387648729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993328903611857850198305 6744996677708893387648729)
              ·
                refine ⟨5058747508281670040736547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6744996677708893387648729 5058747508281670040736547)
                ·
                  refine ⟨7588121262422505061104821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5058747508281670040736547 7588121262422505061104821)
                  ·
                    refine ⟨711386368352109849478577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7588121262422505061104821 711386368352109849478577)
                    ·
                      refine ⟨533539776264082387108933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711386368352109849478577 533539776264082387108933)
                      ·
                        rfl

theorem cell23_1039065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_1039065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039065 prefixEnd_1039065 := by exact prefixLift 1039065
  have htrace : WordTrace (prefixWord ++ tailWord_1039065) baseStart_1039065 baseEnd_1039065 := by
    simpa [prefixWord, tailWord_1039065, baseEnd_1039065] using wordTrace_append hprefix tailTrace_1039065
  have hstable : (prefixWord ++ tailWord_1039065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039065).length < 2 ^ (prefixWord ++ tailWord_1039065).sum := by decide
  have hdescent : baseEnd_1039065 < baseStart_1039065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039075 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 3, 5]
def baseStart_1039075 : Nat := 118140960795 + 1039075 * 2 ^ 59
def prefixEnd_1039075 : Nat := 4983230072969 + 3 ^ 40 * 1039075 * 2
def baseEnd_1039075 : Nat := 177848303690209115994629

theorem tailTrace_1039075 : CollatzResearch.WordTrace tailWord_1039075 prefixEnd_1039075 177848303690209115994629 := by
  unfold tailWord_1039075
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898178710616209726806679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25265452473744139817871119 37898178710616209726806679)
  ·
    refine ⟨56847268065924314590210019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37898178710616209726806679 56847268065924314590210019)
    ·
      refine ⟨85270902098886471885315029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56847268065924314590210019 85270902098886471885315029)
      ·
        refine ⟨1998536767942651684812071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 85270902098886471885315029 1998536767942651684812071)
        ·
          refine ⟨2997805151913977527218107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998536767942651684812071 2997805151913977527218107)
          ·
            refine ⟨4496707727870966290827161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997805151913977527218107 4496707727870966290827161)
            ·
              refine ⟨3372530795903224718120371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496707727870966290827161 3372530795903224718120371)
              ·
                refine ⟨5058796193854837077180557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372530795903224718120371 5058796193854837077180557)
                ·
                  refine ⟨1897048572695563903942709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5058796193854837077180557 1897048572695563903942709)
                  ·
                    refine ⟨177848303690209115994629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1897048572695563903942709 177848303690209115994629)
                    ·
                      rfl

theorem cell23_1039075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 5].length) (baseStart_1039075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039075 prefixEnd_1039075 := by exact prefixLift 1039075
  have htrace : WordTrace (prefixWord ++ tailWord_1039075) baseStart_1039075 baseEnd_1039075 := by
    simpa [prefixWord, tailWord_1039075, baseEnd_1039075] using wordTrace_append hprefix tailTrace_1039075
  have hstable : (prefixWord ++ tailWord_1039075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039075).length < 2 ^ (prefixWord ++ tailWord_1039075).sum := by decide
  have hdescent : baseEnd_1039075 < baseStart_1039075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039088 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_1039088 : Nat := 118140960795 + 1039088 * 2 ^ 59
def prefixEnd_1039088 : Nat := 4983230072969 + 3 ^ 40 * 1039088 * 2
def baseEnd_1039088 : Nat := 177850528773045265707109

theorem tailTrace_1039088 : CollatzResearch.WordTrace tailWord_1039088 prefixEnd_1039088 177850528773045265707109 := by
  unfold tailWord_1039088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949326429784556473514959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25265768573046075298019945 18949326429784556473514959)
  ·
    refine ⟨28423989644676834710272439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949326429784556473514959 28423989644676834710272439)
    ·
      refine ⟨42635984467015252065408659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28423989644676834710272439 42635984467015252065408659)
      ·
        refine ⟨63953976700522878098112989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42635984467015252065408659 63953976700522878098112989)
        ·
          refine ⟨23982741262696079286792371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63953976700522878098112989 23982741262696079286792371)
          ·
            refine ⟨35974111894044118930188557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23982741262696079286792371 35974111894044118930188557)
            ·
              refine ⟨13490291960266544598820709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35974111894044118930188557 13490291960266544598820709)
              ·
                refine ⟨2529429742549977112278883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13490291960266544598820709 2529429742549977112278883)
                ·
                  refine ⟨3794144613824965668418325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529429742549977112278883 3794144613824965668418325)
                  ·
                    refine ⟨177850528773045265707109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3794144613824965668418325 177850528773045265707109)
                    ·
                      rfl

theorem cell23_1039088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_1039088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039088 prefixEnd_1039088 := by exact prefixLift 1039088
  have htrace : WordTrace (prefixWord ++ tailWord_1039088) baseStart_1039088 baseEnd_1039088 := by
    simpa [prefixWord, tailWord_1039088, baseEnd_1039088] using wordTrace_append hprefix tailTrace_1039088
  have hstable : (prefixWord ++ tailWord_1039088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039088).length < 2 ^ (prefixWord ++ tailWord_1039088).sum := by decide
  have hdescent : baseEnd_1039088 < baseStart_1039088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039089 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 1, 1, 3]
def baseStart_1039089 : Nat := 118140960795 + 1039089 * 2 ^ 59
def prefixEnd_1039089 : Nat := 4983230072969 + 3 ^ 40 * 1039089 * 2
def baseEnd_1039089 : Nat := 533552099799790293208823

theorem tailTrace_1039089 : CollatzResearch.WordTrace tailWord_1039089 prefixEnd_1039089 533552099799790293208823 := by
  unfold tailWord_1039089
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898689332565490117816321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25265792888376993411877547 37898689332565490117816321)
  ·
    refine ⟨28424016999424117588362241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37898689332565490117816321 28424016999424117588362241)
    ·
      refine ⟨21318012749568088191271681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28424016999424117588362241 21318012749568088191271681)
      ·
        refine ⟨15988509562176066143453761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21318012749568088191271681 15988509562176066143453761)
        ·
          refine ⟨11991382171632049607590321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15988509562176066143453761 11991382171632049607590321)
          ·
            refine ⟨8993536628724037205692741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991382171632049607590321 8993536628724037205692741)
            ·
              refine ⟨1686288117885756976067389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8993536628724037205692741 1686288117885756976067389)
              ·
                refine ⟨632358044207158866025271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686288117885756976067389 632358044207158866025271)
                ·
                  refine ⟨948537066310738299037907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632358044207158866025271 948537066310738299037907)
                  ·
                    refine ⟨1422805599466107448556861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948537066310738299037907 1422805599466107448556861)
                    ·
                      refine ⟨533552099799790293208823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422805599466107448556861 533552099799790293208823)
                      ·
                        rfl

theorem cell23_1039089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_1039089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039089 prefixEnd_1039089 := by exact prefixLift 1039089
  have htrace : WordTrace (prefixWord ++ tailWord_1039089) baseStart_1039089 baseEnd_1039089 := by
    simpa [prefixWord, tailWord_1039089, baseEnd_1039089] using wordTrace_append hprefix tailTrace_1039089
  have hstable : (prefixWord ++ tailWord_1039089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039089).length < 2 ^ (prefixWord ++ tailWord_1039089).sum := by decide
  have hdescent : baseEnd_1039089 < baseStart_1039089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039106 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1039106 : Nat := 118140960795 + 1039106 * 2 ^ 59
def prefixEnd_1039106 : Nat := 4983230072969 + 3 ^ 40 * 1039106 * 2
def baseEnd_1039106 : Nat := 533560828970916726696245

theorem tailTrace_1039106 : CollatzResearch.WordTrace tailWord_1039106 prefixEnd_1039106 533560828970916726696245 := by
  unfold tailWord_1039106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474827343375975505296293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25266206249002601347456781 9474827343375975505296293)
  ·
    refine ⟨1776530126882995407243055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9474827343375975505296293 1776530126882995407243055)
    ·
      refine ⟨2664795190324493110864583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776530126882995407243055 2664795190324493110864583)
      ·
        refine ⟨3997192785486739666296875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664795190324493110864583 3997192785486739666296875)
        ·
          refine ⟨5995789178230109499445313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997192785486739666296875 5995789178230109499445313)
          ·
            refine ⟨4496841883672582124583985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995789178230109499445313 4496841883672582124583985)
            ·
              refine ⟨3372631412754436593437989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496841883672582124583985 3372631412754436593437989)
              ·
                refine ⟨632368389891456861269623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3372631412754436593437989 632368389891456861269623)
                ·
                  refine ⟨948552584837185291904435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632368389891456861269623 948552584837185291904435)
                  ·
                    refine ⟨1422828877255777937856653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948552584837185291904435 1422828877255777937856653)
                    ·
                      refine ⟨533560828970916726696245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422828877255777937856653 533560828970916726696245)
                      ·
                        rfl

theorem cell23_1039106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1039106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039106 prefixEnd_1039106 := by exact prefixLift 1039106
  have htrace : WordTrace (prefixWord ++ tailWord_1039106) baseStart_1039106 baseEnd_1039106 := by
    simpa [prefixWord, tailWord_1039106, baseEnd_1039106] using wordTrace_append hprefix tailTrace_1039106
  have hstable : (prefixWord ++ tailWord_1039106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039106).length < 2 ^ (prefixWord ++ tailWord_1039106).sum := by decide
  have hdescent : baseEnd_1039106 < baseStart_1039106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039118 : List Nat := [4, 1, 1, 2, 1, 1, 1, 12]
def baseStart_1039118 : Nat := 118140960795 + 1039118 * 2 ^ 59
def prefixEnd_1039118 : Nat := 4983230072969 + 3 ^ 40 * 1039118 * 2
def baseEnd_1039118 : Nat := 19761740397732247398007

theorem tailTrace_1039118 : CollatzResearch.WordTrace tailWord_1039118 prefixEnd_1039118 19761740397732247398007 := by
  unfold tailWord_1039118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737468381182553508827751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25266498032973618713748005 4737468381182553508827751)
  ·
    refine ⟨7106202571773830263241627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4737468381182553508827751 7106202571773830263241627)
    ·
      refine ⟨10659303857660745394862441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7106202571773830263241627 10659303857660745394862441)
      ·
        refine ⟨7994477893245559046146831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659303857660745394862441 7994477893245559046146831)
        ·
          refine ⟨11991716839868338569220247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994477893245559046146831 11991716839868338569220247)
          ·
            refine ⟨17987575259802507853830371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11991716839868338569220247 17987575259802507853830371)
            ·
              refine ⟨26981362889703761780745557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17987575259802507853830371 26981362889703761780745557)
              ·
                refine ⟨19761740397732247398007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 26981362889703761780745557 19761740397732247398007)
                ·
                  rfl

theorem cell23_1039118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_1039118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039118 prefixEnd_1039118 := by exact prefixLift 1039118
  have htrace : WordTrace (prefixWord ++ tailWord_1039118) baseStart_1039118 baseEnd_1039118 := by
    simpa [prefixWord, tailWord_1039118, baseEnd_1039118] using wordTrace_append hprefix tailTrace_1039118
  have hstable : (prefixWord ++ tailWord_1039118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039118).length < 2 ^ (prefixWord ++ tailWord_1039118).sum := by decide
  have hdescent : baseEnd_1039118 < baseStart_1039118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039132 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1039132 : Nat := 118140960795 + 1039132 * 2 ^ 59
def prefixEnd_1039132 : Nat := 4983230072969 + 3 ^ 40 * 1039132 * 2
def baseEnd_1039132 : Nat := 533574179467933624971125

theorem tailTrace_1039132 : CollatzResearch.WordTrace tailWord_1039132 prefixEnd_1039132 533574179467933624971125 := by
  unfold tailWord_1039132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950128835704854230815825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25266838447606472307754433 18950128835704854230815825)
  ·
    refine ⟨14212596626778640673111869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18950128835704854230815825 14212596626778640673111869)
    ·
      refine ⟨5329723735041990252416951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14212596626778640673111869 5329723735041990252416951)
      ·
        refine ⟨7994585602562985378625427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329723735041990252416951 7994585602562985378625427)
        ·
          refine ⟨11991878403844478067938141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994585602562985378625427 11991878403844478067938141)
          ·
            refine ⟨4496954401441679275476803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11991878403844478067938141 4496954401441679275476803)
            ·
              refine ⟨6745431602162518913215205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496954401441679275476803 6745431602162518913215205)
              ·
                refine ⟨1264768425405472296227851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6745431602162518913215205 1264768425405472296227851)
                ·
                  refine ⟨1897152638108208444341777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264768425405472296227851 1897152638108208444341777)
                  ·
                    refine ⟨1422864478581156333256333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1897152638108208444341777 1422864478581156333256333)
                    ·
                      refine ⟨533574179467933624971125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1422864478581156333256333 533574179467933624971125)
                      ·
                        rfl

theorem cell23_1039132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1039132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039132 prefixEnd_1039132 := by exact prefixLift 1039132
  have htrace : WordTrace (prefixWord ++ tailWord_1039132) baseStart_1039132 baseEnd_1039132 := by
    simpa [prefixWord, tailWord_1039132, baseEnd_1039132] using wordTrace_append hprefix tailTrace_1039132
  have hstable : (prefixWord ++ tailWord_1039132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039132).length < 2 ^ (prefixWord ++ tailWord_1039132).sum := by decide
  have hdescent : baseEnd_1039132 < baseStart_1039132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039135 : List Nat := [1, 1, 2, 4, 2, 2, 4, 7]
def baseStart_1039135 : Nat := 118140960795 + 1039135 * 2 ^ 59
def prefixEnd_1039135 : Nat := 4983230072969 + 3 ^ 40 * 1039135 * 2
def baseEnd_1039135 : Nat := 19762063700366559749393

theorem tailTrace_1039135 : CollatzResearch.WordTrace tailWord_1039135 prefixEnd_1039135 19762063700366559749393 := by
  unfold tailWord_1039135
  simp only [CollatzResearch.WordTrace]
  refine ⟨37900367090398839973990859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25266911393599226649327239 37900367090398839973990859)
  ·
    refine ⟨56850550635598259960986289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37900367090398839973990859 56850550635598259960986289)
    ·
      refine ⟨42637912976698694970739717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56850550635598259960986289 42637912976698694970739717)
      ·
        refine ⟨7994608683131005307013697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42637912976698694970739717 7994608683131005307013697)
        ·
          refine ⟨5995956512348253980260273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994608683131005307013697 5995956512348253980260273)
          ·
            refine ⟨4496967384261190485195205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5995956512348253980260273 4496967384261190485195205)
            ·
              refine ⟨843181384548973215974101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4496967384261190485195205 843181384548973215974101)
              ·
                refine ⟨19762063700366559749393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 843181384548973215974101 19762063700366559749393)
                ·
                  rfl

theorem cell23_1039135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 7].length) (baseStart_1039135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039135 prefixEnd_1039135 := by exact prefixLift 1039135
  have htrace : WordTrace (prefixWord ++ tailWord_1039135) baseStart_1039135 baseEnd_1039135 := by
    simpa [prefixWord, tailWord_1039135, baseEnd_1039135] using wordTrace_append hprefix tailTrace_1039135
  have hstable : (prefixWord ++ tailWord_1039135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039135).length < 2 ^ (prefixWord ++ tailWord_1039135).sum := by decide
  have hdescent : baseEnd_1039135 < baseStart_1039135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039205 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1039205 : Nat := 118140960795 + 1039205 * 2 ^ 59
def prefixEnd_1039205 : Nat := 4983230072969 + 3 ^ 40 * 1039205 * 2
def baseEnd_1039205 : Nat := 533611663555711839358289

theorem tailTrace_1039205 : CollatzResearch.WordTrace tailWord_1039205 prefixEnd_1039205 533611663555711839358289 := by
  unfold tailWord_1039205
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902920200145241929039069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25268613466763494619359379 37902920200145241929039069)
  ·
    refine ⟨14213595075054465723389651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37902920200145241929039069 14213595075054465723389651)
    ·
      refine ⟨21320392612581698585084477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213595075054465723389651 21320392612581698585084477)
      ·
        refine ⟨7995147229718136969406679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21320392612581698585084477 7995147229718136969406679)
        ·
          refine ⟨11992720844577205454110019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995147229718136969406679 11992720844577205454110019)
          ·
            refine ⟨17989081266865808181165029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992720844577205454110019 17989081266865808181165029)
            ·
              refine ⟨3372952737537339033968443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17989081266865808181165029 3372952737537339033968443)
              ·
                refine ⟨5059429106306008550952665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372952737537339033968443 5059429106306008550952665)
                ·
                  refine ⟨3794571829729506413214499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5059429106306008550952665 3794571829729506413214499)
                  ·
                    refine ⟨5691857744594259619821749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794571829729506413214499 5691857744594259619821749)
                    ·
                      refine ⟨533611663555711839358289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5691857744594259619821749 533611663555711839358289)
                      ·
                        rfl

theorem cell23_1039205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1039205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039205 prefixEnd_1039205 := by exact prefixLift 1039205
  have htrace : WordTrace (prefixWord ++ tailWord_1039205) baseStart_1039205 baseEnd_1039205 := by
    simpa [prefixWord, tailWord_1039205, baseEnd_1039205] using wordTrace_append hprefix tailTrace_1039205
  have hstable : (prefixWord ++ tailWord_1039205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039205).length < 2 ^ (prefixWord ++ tailWord_1039205).sum := by decide
  have hdescent : baseEnd_1039205 < baseStart_1039205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039219 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 2, 2, 2]
def baseStart_1039219 : Nat := 118140960795 + 1039219 * 2 ^ 59
def prefixEnd_1039219 : Nat := 4983230072969 + 3 ^ 40 * 1039219 * 2
def baseEnd_1039219 : Nat := 533618852284874784583225

theorem tailTrace_1039219 : CollatzResearch.WordTrace tailWord_1039219 prefixEnd_1039219 533618852284874784583225 := by
  unfold tailWord_1039219
  simp only [CollatzResearch.WordTrace]
  refine ⟨37903430822094522320048711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25268953881396348213365807 37903430822094522320048711)
  ·
    refine ⟨56855146233141783480073067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37903430822094522320048711 56855146233141783480073067)
    ·
      refine ⟨85282719349712675220109601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56855146233141783480073067 85282719349712675220109601)
      ·
        refine ⟨63962039512284506415082201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85282719349712675220109601 63962039512284506415082201)
        ·
          refine ⟨47971529634213379811311651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63962039512284506415082201 47971529634213379811311651)
          ·
            refine ⟨71957294451320069716967477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47971529634213379811311651 71957294451320069716967477)
            ·
              refine ⟨6745996354811256535965701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71957294451320069716967477 6745996354811256535965701)
              ·
                refine ⟨1264874316527110600493569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6745996354811256535965701 1264874316527110600493569)
                ·
                  refine ⟨948655737395332950370177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1264874316527110600493569 948655737395332950370177)
                  ·
                    refine ⟨711491803046499712777633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948655737395332950370177 711491803046499712777633)
                    ·
                      refine ⟨533618852284874784583225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711491803046499712777633 533618852284874784583225)
                      ·
                        rfl

theorem cell23_1039219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2, 2].length) (baseStart_1039219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039219 prefixEnd_1039219 := by exact prefixLift 1039219
  have htrace : WordTrace (prefixWord ++ tailWord_1039219) baseStart_1039219 baseEnd_1039219 := by
    simpa [prefixWord, tailWord_1039219, baseEnd_1039219] using wordTrace_append hprefix tailTrace_1039219
  have hstable : (prefixWord ++ tailWord_1039219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039219).length < 2 ^ (prefixWord ++ tailWord_1039219).sum := by decide
  have hdescent : baseEnd_1039219 < baseStart_1039219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039242 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_1039242 : Nat := 118140960795 + 1039242 * 2 ^ 59
def prefixEnd_1039242 : Nat := 4983230072969 + 3 ^ 40 * 1039242 * 2
def baseEnd_1039242 : Nat := 59292295815547577177291

theorem tailTrace_1039242 : CollatzResearch.WordTrace tailWord_1039242 prefixEnd_1039242 59292295815547577177291 := by
  unfold tailWord_1039242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476067425252799312033995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25269513134007464832090653 9476067425252799312033995)
  ·
    refine ⟨14214101137879198968050993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476067425252799312033995 14214101137879198968050993)
    ·
      refine ⟨10660575853409399226038245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14214101137879198968050993 10660575853409399226038245)
      ·
        refine ⟨1998857972514262354882171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10660575853409399226038245 1998857972514262354882171)
        ·
          refine ⟨2998286958771393532323257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998857972514262354882171 2998286958771393532323257)
          ·
            refine ⟨2248715219078545149242443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2998286958771393532323257 2248715219078545149242443)
            ·
              refine ⟨3373072828617817723863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248715219078545149242443 3373072828617817723863665)
              ·
                refine ⟨2529804621463363292897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3373072828617817723863665 2529804621463363292897749)
                ·
                  refine ⟨59292295815547577177291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2529804621463363292897749 59292295815547577177291)
                  ·
                    rfl

theorem cell23_1039242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_1039242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039242 prefixEnd_1039242 := by exact prefixLift 1039242
  have htrace : WordTrace (prefixWord ++ tailWord_1039242) baseStart_1039242 baseEnd_1039242 := by
    simpa [prefixWord, tailWord_1039242, baseEnd_1039242] using wordTrace_append hprefix tailTrace_1039242
  have hstable : (prefixWord ++ tailWord_1039242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039242).length < 2 ^ (prefixWord ++ tailWord_1039242).sum := by decide
  have hdescent : baseEnd_1039242 < baseStart_1039242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039252 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1039252 : Nat := 118140960795 + 1039252 * 2 ^ 59
def prefixEnd_1039252 : Nat := 4983230072969 + 3 ^ 40 * 1039252 * 2
def baseEnd_1039252 : Nat := 533635797146473155470573

theorem tailTrace_1039252 : CollatzResearch.WordTrace tailWord_1039252 prefixEnd_1039252 533635797146473155470573 := by
  unfold tailWord_1039252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18952317215487484478000005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25269756287316645970666673 18952317215487484478000005)
  ·
    refine ⟨3553559477903903339625001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18952317215487484478000005 3553559477903903339625001)
    ·
      refine ⟨2665169608427927504718751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3553559477903903339625001 2665169608427927504718751)
      ·
        refine ⟨3997754412641891257078127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665169608427927504718751 3997754412641891257078127)
        ·
          refine ⟨5996631618962836885617191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997754412641891257078127 5996631618962836885617191)
          ·
            refine ⟨8994947428444255328425787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996631618962836885617191 8994947428444255328425787)
            ·
              refine ⟨13492421142666382992638681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994947428444255328425787 13492421142666382992638681)
              ·
                refine ⟨10119315856999787244479011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492421142666382992638681 10119315856999787244479011)
                ·
                  refine ⟨15178973785499680866718517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119315856999787244479011 15178973785499680866718517)
                  ·
                    refine ⟨1423028792390595081254861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15178973785499680866718517 1423028792390595081254861)
                    ·
                      refine ⟨533635797146473155470573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1423028792390595081254861 533635797146473155470573)
                      ·
                        rfl

theorem cell23_1039252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1039252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039252 prefixEnd_1039252 := by exact prefixLift 1039252
  have htrace : WordTrace (prefixWord ++ tailWord_1039252) baseStart_1039252 baseEnd_1039252 := by
    simpa [prefixWord, tailWord_1039252, baseEnd_1039252] using wordTrace_append hprefix tailTrace_1039252
  have hstable : (prefixWord ++ tailWord_1039252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039252).length < 2 ^ (prefixWord ++ tailWord_1039252).sum := by decide
  have hdescent : baseEnd_1039252 < baseStart_1039252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039255 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 7]
def baseStart_1039255 : Nat := 118140960795 + 1039255 * 2 ^ 59
def prefixEnd_1039255 : Nat := 4983230072969 + 3 ^ 40 * 1039255 * 2
def baseEnd_1039255 : Nat := 177879112529478881244353

theorem tailTrace_1039255 : CollatzResearch.WordTrace tailWord_1039255 prefixEnd_1039255 177879112529478881244353 := by
  unfold tailWord_1039255
  simp only [CollatzResearch.WordTrace]
  refine ⟨37904743849964100468359219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25269829233309400312239479 37904743849964100468359219)
  ·
    refine ⟨56857115774946150702538829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37904743849964100468359219 56857115774946150702538829)
    ·
      refine ⟨21321418415604806513452061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56857115774946150702538829 21321418415604806513452061)
      ·
        refine ⟨7995531905851802442544523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21321418415604806513452061 7995531905851802442544523)
        ·
          refine ⟨11993297858777703663816785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995531905851802442544523 11993297858777703663816785)
          ·
            refine ⟨8994973394083277747862589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11993297858777703663816785 8994973394083277747862589)
            ·
              refine ⟨3373115022781229155448471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8994973394083277747862589 3373115022781229155448471)
              ·
                refine ⟨5059672534171843733172707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373115022781229155448471 5059672534171843733172707)
                ·
                  refine ⟨7589508801257765599759061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059672534171843733172707 7589508801257765599759061)
                  ·
                    refine ⟨177879112529478881244353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7589508801257765599759061 177879112529478881244353)
                    ·
                      rfl

theorem cell23_1039255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_1039255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039255 prefixEnd_1039255 := by exact prefixLift 1039255
  have htrace : WordTrace (prefixWord ++ tailWord_1039255) baseStart_1039255 baseEnd_1039255 := by
    simpa [prefixWord, tailWord_1039255, baseEnd_1039255] using wordTrace_append hprefix tailTrace_1039255
  have hstable : (prefixWord ++ tailWord_1039255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039255).length < 2 ^ (prefixWord ++ tailWord_1039255).sum := by decide
  have hdescent : baseEnd_1039255 < baseStart_1039255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039312 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_1039312 : Nat := 118140960795 + 1039312 * 2 ^ 59
def prefixEnd_1039312 : Nat := 4983230072969 + 3 ^ 40 * 1039312 * 2
def baseEnd_1039312 : Nat := 533666605985742920720297

theorem tailTrace_1039312 : CollatzResearch.WordTrace tailWord_1039312 prefixEnd_1039312 533666605985742920720297 := by
  unfold tailWord_1039312
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953411405378799601592095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25271215207171732802122793 18953411405378799601592095)
  ·
    refine ⟨28430117108068199402388143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18953411405378799601592095 28430117108068199402388143)
    ·
      refine ⟨42645175662102299103582215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28430117108068199402388143 42645175662102299103582215)
      ·
        refine ⟨63967763493153448655373323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42645175662102299103582215 63967763493153448655373323)
        ·
          refine ⟨95951645239730172983059985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63967763493153448655373323 95951645239730172983059985)
          ·
            refine ⟨71963733929797629737294989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95951645239730172983059985 71963733929797629737294989)
            ·
              refine ⟨26986400223674111151485621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71963733929797629737294989 26986400223674111151485621)
              ·
                refine ⟨2529975020969447920451777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26986400223674111151485621 2529975020969447920451777)
                ·
                  refine ⟨1897481265727085940338833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2529975020969447920451777 1897481265727085940338833)
                  ·
                    refine ⟨1423110949295314455254125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1897481265727085940338833 1423110949295314455254125)
                    ·
                      refine ⟨533666605985742920720297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1423110949295314455254125 533666605985742920720297)
                      ·
                        rfl

theorem cell23_1039312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_1039312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039312 prefixEnd_1039312 := by exact prefixLift 1039312
  have htrace : WordTrace (prefixWord ++ tailWord_1039312) baseStart_1039312 baseEnd_1039312 := by
    simpa [prefixWord, tailWord_1039312, baseEnd_1039312] using wordTrace_append hprefix tailTrace_1039312
  have hstable : (prefixWord ++ tailWord_1039312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039312).length < 2 ^ (prefixWord ++ tailWord_1039312).sum := by decide
  have hdescent : baseEnd_1039312 < baseStart_1039312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039319 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 1, 4]
def baseStart_1039319 : Nat := 118140960795 + 1039319 * 2 ^ 59
def prefixEnd_1039319 : Nat := 4983230072969 + 3 ^ 40 * 1039319 * 2
def baseEnd_1039319 : Nat := 177890066783441464444255

theorem tailTrace_1039319 : CollatzResearch.WordTrace tailWord_1039319 prefixEnd_1039319 177890066783441464444255 := by
  unfold tailWord_1039319
  simp only [CollatzResearch.WordTrace]
  refine ⟨37907078121732239398689011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25271385414488159599126007 37907078121732239398689011)
  ·
    refine ⟨56860617182598359098033517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37907078121732239398689011 56860617182598359098033517)
    ·
      refine ⟨21322731443474384661762569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56860617182598359098033517 21322731443474384661762569)
      ·
        refine ⟨15992048582605788496321927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21322731443474384661762569 15992048582605788496321927)
        ·
          refine ⟨23988072873908682744482891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992048582605788496321927 23988072873908682744482891)
          ·
            refine ⟨35982109310863024116724337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23988072873908682744482891 35982109310863024116724337)
            ·
              refine ⟨26986581983147268087543253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35982109310863024116724337 26986581983147268087543253)
              ·
                refine ⟨632498015230014095801795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26986581983147268087543253 632498015230014095801795)
                ·
                  refine ⟨948747022845021143702693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632498015230014095801795 948747022845021143702693)
                  ·
                    refine ⟨177890066783441464444255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 948747022845021143702693 177890066783441464444255)
                    ·
                      rfl

theorem cell23_1039319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_1039319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039319 prefixEnd_1039319 := by exact prefixLift 1039319
  have htrace : WordTrace (prefixWord ++ tailWord_1039319) baseStart_1039319 baseEnd_1039319 := by
    simpa [prefixWord, tailWord_1039319, baseEnd_1039319] using wordTrace_append hprefix tailTrace_1039319
  have hstable : (prefixWord ++ tailWord_1039319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039319).length < 2 ^ (prefixWord ++ tailWord_1039319).sum := by decide
  have hdescent : baseEnd_1039319 < baseStart_1039319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039393 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1039393 : Nat := 118140960795 + 1039393 * 2 ^ 59
def prefixEnd_1039393 : Nat := 4983230072969 + 3 ^ 40 * 1039393 * 2
def baseEnd_1039393 : Nat := 533708197918757103807425

theorem tailTrace_1039393 : CollatzResearch.WordTrace tailWord_1039393 prefixEnd_1039393 533708197918757103807425 := by
  unfold tailWord_1039393
  simp only [CollatzResearch.WordTrace]
  refine ⟨37909777123464150036882833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25273184748976100024588555 37909777123464150036882833)
  ·
    refine ⟨28432332842598112527662125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37909777123464150036882833 28432332842598112527662125)
    ·
      refine ⟨10662124815974292197873297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28432332842598112527662125 10662124815974292197873297)
      ·
        refine ⟨7996593611980719148404973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10662124815974292197873297 7996593611980719148404973)
        ·
          refine ⟨2998722604492769680651865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7996593611980719148404973 2998722604492769680651865)
          ·
            refine ⟨2249041953369577260488899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2998722604492769680651865 2249041953369577260488899)
            ·
              refine ⟨3373562930054365890733349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249041953369577260488899 3373562930054365890733349)
              ·
                refine ⟨632543049385193604512503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3373562930054365890733349 632543049385193604512503)
                ·
                  refine ⟨948814574077790406768755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632543049385193604512503 948814574077790406768755)
                  ·
                    refine ⟨1423221861116685610153133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948814574077790406768755 1423221861116685610153133)
                    ·
                      refine ⟨533708197918757103807425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1423221861116685610153133 533708197918757103807425)
                      ·
                        rfl

theorem cell23_1039393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1039393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039393 prefixEnd_1039393 := by exact prefixLift 1039393
  have htrace : WordTrace (prefixWord ++ tailWord_1039393) baseStart_1039393 baseEnd_1039393 := by
    simpa [prefixWord, tailWord_1039393, baseEnd_1039393] using wordTrace_append hprefix tailTrace_1039393
  have hstable : (prefixWord ++ tailWord_1039393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039393).length < 2 ^ (prefixWord ++ tailWord_1039393).sum := by decide
  have hdescent : baseEnd_1039393 < baseStart_1039393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039409 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_1039409 : Nat := 118140960795 + 1039409 * 2 ^ 59
def prefixEnd_1039409 : Nat := 4983230072969 + 3 ^ 40 * 1039409 * 2
def baseEnd_1039409 : Nat := 177905471203076347069117

theorem tailTrace_1039409 : CollatzResearch.WordTrace tailWord_1039409 prefixEnd_1039409 177905471203076347069117 := by
  unfold tailWord_1039409
  simp only [CollatzResearch.WordTrace]
  refine ⟨37910360691406184769465281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25273573794270789846310187 37910360691406184769465281)
  ·
    refine ⟨28432770518554638577098961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37910360691406184769465281 28432770518554638577098961)
    ·
      refine ⟨21324577888915978932824221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28432770518554638577098961 21324577888915978932824221)
      ·
        refine ⟨7996716708343492099809083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21324577888915978932824221 7996716708343492099809083)
        ·
          refine ⟨11995075062515238149713625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996716708343492099809083 11995075062515238149713625)
          ·
            refine ⟨8996306296886428612285219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11995075062515238149713625 8996306296886428612285219)
            ·
              refine ⟨13494459445329642918427829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996306296886428612285219 13494459445329642918427829)
              ·
                refine ⟨1265105572999654023602609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13494459445329642918427829 1265105572999654023602609)
                ·
                  refine ⟨948829179749740517701957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1265105572999654023602609 948829179749740517701957)
                  ·
                    refine ⟨177905471203076347069117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 948829179749740517701957 177905471203076347069117)
                    ·
                      rfl

theorem cell23_1039409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_1039409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039409 prefixEnd_1039409 := by exact prefixLift 1039409
  have htrace : WordTrace (prefixWord ++ tailWord_1039409) baseStart_1039409 baseEnd_1039409 := by
    simpa [prefixWord, tailWord_1039409, baseEnd_1039409] using wordTrace_append hprefix tailTrace_1039409
  have hstable : (prefixWord ++ tailWord_1039409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039409).length < 2 ^ (prefixWord ++ tailWord_1039409).sum := by decide
  have hdescent : baseEnd_1039409 < baseStart_1039409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039416 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_1039416 : Nat := 118140960795 + 1039416 * 2 ^ 59
def prefixEnd_1039416 : Nat := 4983230072969 + 3 ^ 40 * 1039416 * 2
def baseEnd_1039416 : Nat := 533720007973810513819819

theorem tailTrace_1039416 : CollatzResearch.WordTrace tailWord_1039416 prefixEnd_1039416 533720007973810513819819 := by
  unfold tailWord_1039416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955308001190412482485051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25273744001587216643313401 18955308001190412482485051)
  ·
    refine ⟨28432962001785618723727577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18955308001190412482485051 28432962001785618723727577)
    ·
      refine ⟨21324721501339214042795683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28432962001785618723727577 21324721501339214042795683)
      ·
        refine ⟨31987082252008821064193525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21324721501339214042795683 31987082252008821064193525)
        ·
          refine ⟨2998788961125826974768143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31987082252008821064193525 2998788961125826974768143)
          ·
            refine ⟨4498183441688740462152215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998788961125826974768143 4498183441688740462152215)
            ·
              refine ⟨6747275162533110693228323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498183441688740462152215 6747275162533110693228323)
              ·
                refine ⟨10120912743799666039842485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6747275162533110693228323 10120912743799666039842485)
                ·
                  refine ⟨948835569731218691235233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10120912743799666039842485 948835569731218691235233)
                  ·
                    refine ⟨711626677298414018426425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 948835569731218691235233 711626677298414018426425)
                    ·
                      refine ⟨533720007973810513819819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711626677298414018426425 533720007973810513819819)
                      ·
                        rfl

theorem cell23_1039416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_1039416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039416 prefixEnd_1039416 := by exact prefixLift 1039416
  have htrace : WordTrace (prefixWord ++ tailWord_1039416) baseStart_1039416 baseEnd_1039416 := by
    simpa [prefixWord, tailWord_1039416, baseEnd_1039416] using wordTrace_append hprefix tailTrace_1039416
  have hstable : (prefixWord ++ tailWord_1039416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039416).length < 2 ^ (prefixWord ++ tailWord_1039416).sum := by decide
  have hdescent : baseEnd_1039416 < baseStart_1039416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039430 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1039430 : Nat := 118140960795 + 1039430 * 2 ^ 59
def prefixEnd_1039430 : Nat := 4983230072969 + 3 ^ 40 * 1039430 * 2
def baseEnd_1039430 : Nat := 177909065567657819681585

theorem tailTrace_1039430 : CollatzResearch.WordTrace tailWord_1039430 prefixEnd_1039430 177909065567657819681585 := by
  unfold tailWord_1039430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184722707010315792374367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25274084416220070237319829 1184722707010315792374367)
  ·
    refine ⟨1777084060515473688561551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184722707010315792374367 1777084060515473688561551)
    ·
      refine ⟨2665626090773210532842327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777084060515473688561551 2665626090773210532842327)
      ·
        refine ⟨3998439136159815799263491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665626090773210532842327 3998439136159815799263491)
        ·
          refine ⟨5997658704239723698895237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998439136159815799263491 5997658704239723698895237)
          ·
            refine ⟨1124561007044948193542857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5997658704239723698895237 1124561007044948193542857)
            ·
              refine ⟨843420755283711145157143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124561007044948193542857 843420755283711145157143)
              ·
                refine ⟨1265131132925566717735715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843420755283711145157143 1265131132925566717735715)
                ·
                  refine ⟨1897696699388350076603573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265131132925566717735715 1897696699388350076603573)
                  ·
                    refine ⟨177909065567657819681585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1897696699388350076603573 177909065567657819681585)
                    ·
                      rfl

theorem cell23_1039430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1039430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039430 prefixEnd_1039430 := by exact prefixLift 1039430
  have htrace : WordTrace (prefixWord ++ tailWord_1039430) baseStart_1039430 baseEnd_1039430 := by
    simpa [prefixWord, tailWord_1039430, baseEnd_1039430] using wordTrace_append hprefix tailTrace_1039430
  have hstable : (prefixWord ++ tailWord_1039430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039430).length < 2 ^ (prefixWord ++ tailWord_1039430).sum := by decide
  have hdescent : baseEnd_1039430 < baseStart_1039430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039466 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1039466 : Nat := 118140960795 + 1039466 * 2 ^ 59
def prefixEnd_1039466 : Nat := 4983230072969 + 3 ^ 40 * 1039466 * 2
def baseEnd_1039466 : Nat := 533745682006535318194589

theorem tailTrace_1039466 : CollatzResearch.WordTrace tailWord_1039466 prefixEnd_1039466 533745682006535318194589 := by
  unfold tailWord_1039466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478109913049920876072563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25274959768133122336193501 9478109913049920876072563)
  ·
    refine ⟨14217164869574881314108845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9478109913049920876072563 14217164869574881314108845)
    ·
      refine ⟨5331436826090580492790817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14217164869574881314108845 5331436826090580492790817)
      ·
        refine ⟨3998577619567935369593113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5331436826090580492790817 3998577619567935369593113)
        ·
          refine ⟨2998933214675951527194835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3998577619567935369593113 2998933214675951527194835)
          ·
            refine ⟨4498399822013927290792253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998933214675951527194835 4498399822013927290792253)
            ·
              refine ⟨1686899933255222734047095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4498399822013927290792253 1686899933255222734047095)
              ·
                refine ⟨2530349899882834101070643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686899933255222734047095 2530349899882834101070643)
                ·
                  refine ⟨3795524849824251151605965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530349899882834101070643 3795524849824251151605965)
                  ·
                    refine ⟨1423321818684094181852237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3795524849824251151605965 1423321818684094181852237)
                    ·
                      refine ⟨533745682006535318194589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1423321818684094181852237 533745682006535318194589)
                      ·
                        rfl

theorem cell23_1039466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1039466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039466 prefixEnd_1039466 := by exact prefixLift 1039466
  have htrace : WordTrace (prefixWord ++ tailWord_1039466) baseStart_1039466 baseEnd_1039466 := by
    simpa [prefixWord, tailWord_1039466, baseEnd_1039466] using wordTrace_append hprefix tailTrace_1039466
  have hstable : (prefixWord ++ tailWord_1039466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039466).length < 2 ^ (prefixWord ++ tailWord_1039466).sum := by decide
  have hdescent : baseEnd_1039466 < baseStart_1039466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039596 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_1039596 : Nat := 118140960795 + 1039596 * 2 ^ 59
def prefixEnd_1039596 : Nat := 4983230072969 + 3 ^ 40 * 1039596 * 2
def baseEnd_1039596 : Nat := 533812434491619809568991

theorem tailTrace_1039596 : CollatzResearch.WordTrace tailWord_1039596 prefixEnd_1039596 533812434491619809568991 := by
  unfold tailWord_1039596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18958590570864357853261321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25278120761152477137681761 18958590570864357853261321)
  ·
    refine ⟨14218942928148268389945991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18958590570864357853261321 14218942928148268389945991)
    ·
      refine ⟨21328414392222402584918987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14218942928148268389945991 21328414392222402584918987)
      ·
        refine ⟨31992621588333603877378481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21328414392222402584918987 31992621588333603877378481)
        ·
          refine ⟨23994466191250202908033861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31992621588333603877378481 23994466191250202908033861)
          ·
            refine ⟨4498962410859413045256349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23994466191250202908033861 4498962410859413045256349)
            ·
              refine ⟨1687110904072279891971131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4498962410859413045256349 1687110904072279891971131)
              ·
                refine ⟨2530666356108419837956697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687110904072279891971131 2530666356108419837956697)
                ·
                  refine ⟨1897999767081314878467523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2530666356108419837956697 1897999767081314878467523)
                  ·
                    refine ⟨2846999650621972317701285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1897999767081314878467523 2846999650621972317701285)
                    ·
                      refine ⟨533812434491619809568991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2846999650621972317701285 533812434491619809568991)
                      ·
                        rfl

theorem cell23_1039596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_1039596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039596 prefixEnd_1039596 := by exact prefixLift 1039596
  have htrace : WordTrace (prefixWord ++ tailWord_1039596) baseStart_1039596 baseEnd_1039596 := by
    simpa [prefixWord, tailWord_1039596, baseEnd_1039596] using wordTrace_append hprefix tailTrace_1039596
  have hstable : (prefixWord ++ tailWord_1039596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039596).length < 2 ^ (prefixWord ++ tailWord_1039596).sum := by decide
  have hdescent : baseEnd_1039596 < baseStart_1039596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039606 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1039606 : Nat := 118140960795 + 1039606 * 2 ^ 59
def prefixEnd_1039606 : Nat := 4983230072969 + 3 ^ 40 * 1039606 * 2
def baseEnd_1039606 : Nat := 177939189766054923481315

theorem tailTrace_1039606 : CollatzResearch.WordTrace tailWord_1039606 prefixEnd_1039606 177939189766054923481315 := by
  unfold tailWord_1039606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369846616980780463399167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25278363914461658276257781 2369846616980780463399167)
  ·
    refine ⟨3554769925471170695098751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2369846616980780463399167 3554769925471170695098751)
    ·
      refine ⟨5332154888206756042648127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554769925471170695098751 5332154888206756042648127)
      ·
        refine ⟨7998232332310134063972191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332154888206756042648127 7998232332310134063972191)
        ·
          refine ⟨11997348498465201095958287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998232332310134063972191 11997348498465201095958287)
          ·
            refine ⟨17996022747697801643937431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997348498465201095958287 17996022747697801643937431)
            ·
              refine ⟨26994034121546702465906147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996022747697801643937431 26994034121546702465906147)
              ·
                refine ⟨40491051182320053698859221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26994034121546702465906147 40491051182320053698859221)
                ·
                  refine ⟨949009012085626258567013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40491051182320053698859221 949009012085626258567013)
                  ·
                    refine ⟨177939189766054923481315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 949009012085626258567013 177939189766054923481315)
                    ·
                      rfl

theorem cell23_1039606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1039606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039606 prefixEnd_1039606 := by exact prefixLift 1039606
  have htrace : WordTrace (prefixWord ++ tailWord_1039606) baseStart_1039606 baseEnd_1039606 := by
    simpa [prefixWord, tailWord_1039606, baseEnd_1039606] using wordTrace_append hprefix tailTrace_1039606
  have hstable : (prefixWord ++ tailWord_1039606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039606).length < 2 ^ (prefixWord ++ tailWord_1039606).sum := by decide
  have hdescent : baseEnd_1039606 < baseStart_1039606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039619 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 8]
def baseStart_1039619 : Nat := 118140960795 + 1039619 * 2 ^ 59
def prefixEnd_1039619 : Nat := 4983230072969 + 3 ^ 40 * 1039619 * 2
def baseEnd_1039619 : Nat := 59313804949630357731265

theorem tailTrace_1039619 : CollatzResearch.WordTrace tailWord_1039619 prefixEnd_1039619 59313804949630357731265 := by
  unfold tailWord_1039619
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918020020645390634609911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25278680013763593756406607 37918020020645390634609911)
  ·
    refine ⟨56877030030968085951914867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37918020020645390634609911 56877030030968085951914867)
    ·
      refine ⟨85315545046452128927872301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56877030030968085951914867 85315545046452128927872301)
      ·
        refine ⟨31993329392419548347952113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85315545046452128927872301 31993329392419548347952113)
        ·
          refine ⟨23994997044314661260964085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31993329392419548347952113 23994997044314661260964085)
          ·
            refine ⟨2249530972904499493215383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23994997044314661260964085 2249530972904499493215383)
            ·
              refine ⟨3374296459356749239823075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249530972904499493215383 3374296459356749239823075)
              ·
                refine ⟨5061444689035123859734613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374296459356749239823075 5061444689035123859734613)
                ·
                  refine ⟨59313804949630357731265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5061444689035123859734613 59313804949630357731265)
                  ·
                    rfl

theorem cell23_1039619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 8].length) (baseStart_1039619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039619 prefixEnd_1039619 := by exact prefixLift 1039619
  have htrace : WordTrace (prefixWord ++ tailWord_1039619) baseStart_1039619 baseEnd_1039619 := by
    simpa [prefixWord, tailWord_1039619, baseEnd_1039619] using wordTrace_append hprefix tailTrace_1039619
  have hstable : (prefixWord ++ tailWord_1039619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039619).length < 2 ^ (prefixWord ++ tailWord_1039619).sum := by decide
  have hdescent : baseEnd_1039619 < baseStart_1039619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039639 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1039639 : Nat := 118140960795 + 1039639 * 2 ^ 59
def prefixEnd_1039639 : Nat := 4983230072969 + 3 ^ 40 * 1039639 * 2
def baseEnd_1039639 : Nat := 533834514159763141331293

theorem tailTrace_1039639 : CollatzResearch.WordTrace tailWord_1039639 prefixEnd_1039639 533834514159763141331293 := by
  unfold tailWord_1039639
  simp only [CollatzResearch.WordTrace]
  refine ⟨37918749480572934050337971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25279166320381956033558647 37918749480572934050337971)
  ·
    refine ⟨56878124220859401075506957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37918749480572934050337971 56878124220859401075506957)
    ·
      refine ⟨21329296582822275403315109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56878124220859401075506957 21329296582822275403315109)
      ·
        refine ⟨3999243109279176638121583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21329296582822275403315109 3999243109279176638121583)
        ·
          refine ⟨5998864663918764957182375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999243109279176638121583 5998864663918764957182375)
          ·
            refine ⟨8998296995878147435773563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5998864663918764957182375 8998296995878147435773563)
            ·
              refine ⟨13497445493817221153660345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998296995878147435773563 13497445493817221153660345)
              ·
                refine ⟨10123084120362915865245259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13497445493817221153660345 10123084120362915865245259)
                ·
                  refine ⟨15184626180544373797867889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123084120362915865245259 15184626180544373797867889)
                  ·
                    refine ⟨11388469635408280348400917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15184626180544373797867889 11388469635408280348400917)
                    ·
                      refine ⟨533834514159763141331293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11388469635408280348400917 533834514159763141331293)
                      ·
                        rfl

theorem cell23_1039639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1039639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039639 prefixEnd_1039639 := by exact prefixLift 1039639
  have htrace : WordTrace (prefixWord ++ tailWord_1039639) baseStart_1039639 baseEnd_1039639 := by
    simpa [prefixWord, tailWord_1039639, baseEnd_1039639] using wordTrace_append hprefix tailTrace_1039639
  have hstable : (prefixWord ++ tailWord_1039639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039639).length < 2 ^ (prefixWord ++ tailWord_1039639).sum := by decide
  have hdescent : baseEnd_1039639 < baseStart_1039639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039699 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_1039699 : Nat := 118140960795 + 1039699 * 2 ^ 59
def prefixEnd_1039699 : Nat := 4983230072969 + 3 ^ 40 * 1039699 * 2
def baseEnd_1039699 : Nat := 533865322999032906581017

theorem tailTrace_1039699 : CollatzResearch.WordTrace tailWord_1039699 prefixEnd_1039699 533865322999032906581017 := by
  unfold tailWord_1039699
  simp only [CollatzResearch.WordTrace]
  refine ⟨37920937860355564297522151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25280625240237042865014767 37920937860355564297522151)
  ·
    refine ⟨56881406790533346446283227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37920937860355564297522151 56881406790533346446283227)
    ·
      refine ⟨85322110185800019669424841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56881406790533346446283227 85322110185800019669424841)
      ·
        refine ⟨63991582639350014752068631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85322110185800019669424841 63991582639350014752068631)
        ·
          refine ⟨95987373959025022128102947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63991582639350014752068631 95987373959025022128102947)
          ·
            refine ⟨143981060938537533192154421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95987373959025022128102947 143981060938537533192154421)
            ·
              refine ⟨13498224462987893736764477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143981060938537533192154421 13498224462987893736764477)
              ·
                refine ⟨5061834173620460151286679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13498224462987893736764477 5061834173620460151286679)
                ·
                  refine ⟨7592751260430690226930019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061834173620460151286679 7592751260430690226930019)
                  ·
                    refine ⟨11389126890646035340395029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7592751260430690226930019 11389126890646035340395029)
                    ·
                      refine ⟨533865322999032906581017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11389126890646035340395029 533865322999032906581017)
                      ·
                        rfl

theorem cell23_1039699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_1039699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039699 prefixEnd_1039699 := by exact prefixLift 1039699
  have htrace : WordTrace (prefixWord ++ tailWord_1039699) baseStart_1039699 baseEnd_1039699 := by
    simpa [prefixWord, tailWord_1039699, baseEnd_1039699] using wordTrace_append hprefix tailTrace_1039699
  have hstable : (prefixWord ++ tailWord_1039699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039699).length < 2 ^ (prefixWord ++ tailWord_1039699).sum := by decide
  have hdescent : baseEnd_1039699 < baseStart_1039699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039703 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_1039703 : Nat := 118140960795 + 1039703 * 2 ^ 59
def prefixEnd_1039703 : Nat := 4983230072969 + 3 ^ 40 * 1039703 * 2
def baseEnd_1039703 : Nat := 533867376921650890930999

theorem tailTrace_1039703 : CollatzResearch.WordTrace tailWord_1039703 prefixEnd_1039703 533867376921650890930999 := by
  unfold tailWord_1039703
  simp only [CollatzResearch.WordTrace]
  refine ⟨37921083752341072980667763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25280722501560715320445175 37921083752341072980667763)
  ·
    refine ⟨56881625628511609471001645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37921083752341072980667763 56881625628511609471001645)
    ·
      refine ⟨21330609610691853551625617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56881625628511609471001645 21330609610691853551625617)
      ·
        refine ⟨15997957208018890163719213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21330609610691853551625617 15997957208018890163719213)
        ·
          refine ⟨5999233953007083811394705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15997957208018890163719213 5999233953007083811394705)
          ·
            refine ⟨4499425464755312858546029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5999233953007083811394705 4499425464755312858546029)
            ·
              refine ⟨1687284549283242321954761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4499425464755312858546029 1687284549283242321954761)
              ·
                refine ⟨1265463411962431741466071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687284549283242321954761 1265463411962431741466071)
                ·
                  refine ⟨1898195117943647612199107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265463411962431741466071 1898195117943647612199107)
                  ·
                    refine ⟨2847292676915471418298661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1898195117943647612199107 2847292676915471418298661)
                    ·
                      refine ⟨533867376921650890930999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2847292676915471418298661 533867376921650890930999)
                      ·
                        rfl

theorem cell23_1039703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_1039703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039703 prefixEnd_1039703 := by exact prefixLift 1039703
  have htrace : WordTrace (prefixWord ++ tailWord_1039703) baseStart_1039703 baseEnd_1039703 := by
    simpa [prefixWord, tailWord_1039703, baseEnd_1039703] using wordTrace_append hprefix tailTrace_1039703
  have hstable : (prefixWord ++ tailWord_1039703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039703).length < 2 ^ (prefixWord ++ tailWord_1039703).sum := by decide
  have hdescent : baseEnd_1039703 < baseStart_1039703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039716 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1039716 : Nat := 118140960795 + 1039716 * 2 ^ 59
def prefixEnd_1039716 : Nat := 4983230072969 + 3 ^ 40 * 1039716 * 2
def baseEnd_1039716 : Nat := 533874052170159340068439

theorem tailTrace_1039716 : CollatzResearch.WordTrace tailWord_1039716 prefixEnd_1039716 533874052170159340068439 := by
  unfold tailWord_1039716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960778950646988100445501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25281038600862650800594001 18960778950646988100445501)
  ·
    refine ⟨7110292106492620537667063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18960778950646988100445501 7110292106492620537667063)
    ·
      refine ⟨10665438159738930806500595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7110292106492620537667063 10665438159738930806500595)
      ·
        refine ⟨15998157239608396209750893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665438159738930806500595 15998157239608396209750893)
        ·
          refine ⟨5999308964853148578656585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15998157239608396209750893 5999308964853148578656585)
          ·
            refine ⟨4499481723639861433992439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5999308964853148578656585 4499481723639861433992439)
            ·
              refine ⟨6749222585459792150988659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499481723639861433992439 6749222585459792150988659)
              ·
                refine ⟨10123833878189688226482989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749222585459792150988659 10123833878189688226482989)
                ·
                  refine ⟨3796437704321133084931121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10123833878189688226482989 3796437704321133084931121)
                  ·
                    refine ⟨2847328278240849813698341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796437704321133084931121 2847328278240849813698341)
                    ·
                      refine ⟨533874052170159340068439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2847328278240849813698341 533874052170159340068439)
                      ·
                        rfl

theorem cell23_1039716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1039716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039716 prefixEnd_1039716 := by exact prefixLift 1039716
  have htrace : WordTrace (prefixWord ++ tailWord_1039716) baseStart_1039716 baseEnd_1039716 := by
    simpa [prefixWord, tailWord_1039716, baseEnd_1039716] using wordTrace_append hprefix tailTrace_1039716
  have hstable : (prefixWord ++ tailWord_1039716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039716).length < 2 ^ (prefixWord ++ tailWord_1039716).sum := by decide
  have hdescent : baseEnd_1039716 < baseStart_1039716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039726 : List Nat := [4, 1, 2, 4, 12]
def baseStart_1039726 : Nat := 118140960795 + 1039726 * 2 ^ 59
def prefixEnd_1039726 : Nat := 4983230072969 + 3 ^ 40 * 1039726 * 2
def baseEnd_1039726 : Nat := 732344563754052539017

theorem tailTrace_1039726 : CollatzResearch.WordTrace tailWord_1039726 prefixEnd_1039726 732344563754052539017 := by
  unfold tailWord_1039726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740240328907218488594379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25281281754171831939170021 4740240328907218488594379)
  ·
    refine ⟨7110360493360827732891569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4740240328907218488594379 7110360493360827732891569)
    ·
      refine ⟨5332770370020620799668677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7110360493360827732891569 5332770370020620799668677)
      ·
        refine ⟨999894444378866399937877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5332770370020620799668677 999894444378866399937877)
        ·
          refine ⟨732344563754052539017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 999894444378866399937877 732344563754052539017)
          ·
            rfl

theorem cell23_1039726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 12].length) (baseStart_1039726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039726 prefixEnd_1039726 := by exact prefixLift 1039726
  have htrace : WordTrace (prefixWord ++ tailWord_1039726) baseStart_1039726 baseEnd_1039726 := by
    simpa [prefixWord, tailWord_1039726, baseEnd_1039726] using wordTrace_append hprefix tailTrace_1039726
  have hstable : (prefixWord ++ tailWord_1039726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039726).length < 2 ^ (prefixWord ++ tailWord_1039726).sum := by decide
  have hdescent : baseEnd_1039726 < baseStart_1039726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039739 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 9]
def baseStart_1039739 : Nat := 118140960795 + 1039739 * 2 ^ 59
def prefixEnd_1039739 : Nat := 4983230072969 + 3 ^ 40 * 1039739 * 2
def baseEnd_1039739 : Nat := 177961954075070916693611

theorem tailTrace_1039739 : CollatzResearch.WordTrace tailWord_1039739 prefixEnd_1039739 177961954075070916693611 := by
  unfold tailWord_1039739
  simp only [CollatzResearch.WordTrace]
  refine ⟨37922396780210651128978271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25281597853473767419318847 37922396780210651128978271)
  ·
    refine ⟨56883595170315976693467407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37922396780210651128978271 56883595170315976693467407)
    ·
      refine ⟨85325392755473965040201111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56883595170315976693467407 85325392755473965040201111)
      ·
        refine ⟨127988089133210947560301667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85325392755473965040201111 127988089133210947560301667)
        ·
          refine ⟨191982133699816421340452501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127988089133210947560301667 191982133699816421340452501)
          ·
            refine ⟨8999162517178894750333711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191982133699816421340452501 8999162517178894750333711)
            ·
              refine ⟨13498743775768342125500567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999162517178894750333711 13498743775768342125500567)
              ·
                refine ⟨20248115663652513188250851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13498743775768342125500567 20248115663652513188250851)
                ·
                  refine ⟨30372173495478769782376277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20248115663652513188250851 30372173495478769782376277)
                  ·
                    refine ⟨177961954075070916693611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 30372173495478769782376277 177961954075070916693611)
                    ·
                      rfl

theorem cell23_1039739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_1039739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039739 prefixEnd_1039739 := by exact prefixLift 1039739
  have htrace : WordTrace (prefixWord ++ tailWord_1039739) baseStart_1039739 baseEnd_1039739 := by
    simpa [prefixWord, tailWord_1039739, baseEnd_1039739] using wordTrace_append hprefix tailTrace_1039739
  have hstable : (prefixWord ++ tailWord_1039739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039739).length < 2 ^ (prefixWord ++ tailWord_1039739).sum := by decide
  have hdescent : baseEnd_1039739 < baseStart_1039739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039804 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1039804 : Nat := 118140960795 + 1039804 * 2 ^ 59
def prefixEnd_1039804 : Nat := 4983230072969 + 3 ^ 40 * 1039804 * 2
def baseEnd_1039804 : Nat := 533919238467754995768035

theorem tailTrace_1039804 : CollatzResearch.WordTrace tailWord_1039804 prefixEnd_1039804 533919238467754995768035 := by
  unfold tailWord_1039804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962383762487583615047233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25283178349983444820062977 18962383762487583615047233)
  ·
    refine ⟨14221787821865687711285425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18962383762487583615047233 14221787821865687711285425)
    ·
      refine ⟨10666340866399265783464069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14221787821865687711285425 10666340866399265783464069)
      ·
        refine ⟨1999938912449862334399513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10666340866399265783464069 1999938912449862334399513)
        ·
          refine ⟨1499954184337396750799635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999938912449862334399513 1499954184337396750799635)
          ·
            refine ⟨2249931276506095126199453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499954184337396750799635 2249931276506095126199453)
            ·
              refine ⟨843724228689785672324795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2249931276506095126199453 843724228689785672324795)
              ·
                refine ⟨1265586343034678508487193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843724228689785672324795 1265586343034678508487193)
                ·
                  refine ⟨949189757276008881365395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1265586343034678508487193 949189757276008881365395)
                  ·
                    refine ⟨1423784635914013322048093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949189757276008881365395 1423784635914013322048093)
                    ·
                      refine ⟨533919238467754995768035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1423784635914013322048093 533919238467754995768035)
                      ·
                        rfl

theorem cell23_1039804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1039804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039804 prefixEnd_1039804 := by exact prefixLift 1039804
  have htrace : WordTrace (prefixWord ++ tailWord_1039804) baseStart_1039804 baseEnd_1039804 := by
    simpa [prefixWord, tailWord_1039804, baseEnd_1039804] using wordTrace_append hprefix tailTrace_1039804
  have hstable : (prefixWord ++ tailWord_1039804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039804).length < 2 ^ (prefixWord ++ tailWord_1039804).sum := by decide
  have hdescent : baseEnd_1039804 < baseStart_1039804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039816 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 7]
def baseStart_1039816 : Nat := 118140960795 + 1039816 * 2 ^ 59
def prefixEnd_1039816 : Nat := 4983230072969 + 3 ^ 40 * 1039816 * 2
def baseEnd_1039816 : Nat := 59325044470623216535331

theorem tailTrace_1039816 : CollatzResearch.WordTrace tailWord_1039816 prefixEnd_1039816 59325044470623216535331 := by
  unfold tailWord_1039816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962602600465846639765651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25283470133954462186354201 18962602600465846639765651)
  ·
    refine ⟨28443903900698769959648477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18962602600465846639765651 28443903900698769959648477)
    ·
      refine ⟨10666463962762038734868179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28443903900698769959648477 10666463962762038734868179)
      ·
        refine ⟨15999695944143058102302269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10666463962762038734868179 15999695944143058102302269)
        ·
          refine ⟨5999885979053646788363351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15999695944143058102302269 5999885979053646788363351)
          ·
            refine ⟨8999828968580470182545027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999885979053646788363351 8999828968580470182545027)
            ·
              refine ⟨13499743452870705273817541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999828968580470182545027 13499743452870705273817541)
              ·
                refine ⟨2531201897413257238840789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13499743452870705273817541 2531201897413257238840789)
                ·
                  refine ⟨59325044470623216535331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2531201897413257238840789 59325044470623216535331)
                  ·
                    rfl

theorem cell23_1039816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_1039816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039816 prefixEnd_1039816 := by exact prefixLift 1039816
  have htrace : WordTrace (prefixWord ++ tailWord_1039816) baseStart_1039816 baseEnd_1039816 := by
    simpa [prefixWord, tailWord_1039816, baseEnd_1039816] using wordTrace_append hprefix tailTrace_1039816
  have hstable : (prefixWord ++ tailWord_1039816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039816).length < 2 ^ (prefixWord ++ tailWord_1039816).sum := by decide
  have hdescent : baseEnd_1039816 < baseStart_1039816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039830 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1039830 : Nat := 118140960795 + 1039830 * 2 ^ 59
def prefixEnd_1039830 : Nat := 4983230072969 + 3 ^ 40 * 1039830 * 2
def baseEnd_1039830 : Nat := 533932588964771894042915

theorem tailTrace_1039830 : CollatzResearch.WordTrace tailWord_1039830 prefixEnd_1039830 533932588964771894042915 := by
  unfold tailWord_1039830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370357238930060854408809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25283810548587315780360629 2370357238930060854408809)
  ·
    refine ⟨1777767929197545640806607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2370357238930060854408809 1777767929197545640806607)
    ·
      refine ⟨2666651893796318461209911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777767929197545640806607 2666651893796318461209911)
      ·
        refine ⟨3999977840694477691814867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666651893796318461209911 3999977840694477691814867)
        ·
          refine ⟨5999966761041716537722301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999977840694477691814867 5999966761041716537722301)
          ·
            refine ⟨2249987535390643701645863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5999966761041716537722301 2249987535390643701645863)
            ·
              refine ⟨3374981303085965552468795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249987535390643701645863 3374981303085965552468795)
              ·
                refine ⟨5062471954628948328703193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374981303085965552468795 5062471954628948328703193)
                ·
                  refine ⟨3796853965971711246527395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062471954628948328703193 3796853965971711246527395)
                  ·
                    refine ⟨5695280948957566869791093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3796853965971711246527395 5695280948957566869791093)
                    ·
                      refine ⟨533932588964771894042915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5695280948957566869791093 533932588964771894042915)
                      ·
                        rfl

theorem cell23_1039830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1039830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039830 prefixEnd_1039830 := by exact prefixLift 1039830
  have htrace : WordTrace (prefixWord ++ tailWord_1039830) baseStart_1039830 baseEnd_1039830 := by
    simpa [prefixWord, tailWord_1039830, baseEnd_1039830] using wordTrace_append hprefix tailTrace_1039830
  have hstable : (prefixWord ++ tailWord_1039830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039830).length < 2 ^ (prefixWord ++ tailWord_1039830).sum := by decide
  have hdescent : baseEnd_1039830 < baseStart_1039830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039850 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_1039850 : Nat := 118140960795 + 1039850 * 2 ^ 59
def prefixEnd_1039850 : Nat := 4983230072969 + 3 ^ 40 * 1039850 * 2
def baseEnd_1039850 : Nat := 59326984286429090643647

theorem tailTrace_1039850 : CollatzResearch.WordTrace tailWord_1039850 prefixEnd_1039850 59326984286429090643647 := by
  unfold tailWord_1039850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481611320702129271567251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25284296855205678057512669 9481611320702129271567251)
  ·
    refine ⟨14222416981053193907350877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481611320702129271567251 14222416981053193907350877)
    ·
      refine ⟨5333406367894947715256579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14222416981053193907350877 5333406367894947715256579)
      ·
        refine ⟨8000109551842421572884869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333406367894947715256579 8000109551842421572884869)
        ·
          refine ⟨1500020540970454044915913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8000109551842421572884869 1500020540970454044915913)
          ·
            refine ⟨1125015405727840533686935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500020540970454044915913 1125015405727840533686935)
            ·
              refine ⟨1687523108591760800530403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125015405727840533686935 1687523108591760800530403)
              ·
                refine ⟨2531284662887641200795605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687523108591760800530403 2531284662887641200795605)
                ·
                  refine ⟨59326984286429090643647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2531284662887641200795605 59326984286429090643647)
                  ·
                    rfl

theorem cell23_1039850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_1039850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039850 prefixEnd_1039850 := by exact prefixLift 1039850
  have htrace : WordTrace (prefixWord ++ tailWord_1039850) baseStart_1039850 baseEnd_1039850 := by
    simpa [prefixWord, tailWord_1039850, baseEnd_1039850] using wordTrace_append hprefix tailTrace_1039850
  have hstable : (prefixWord ++ tailWord_1039850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039850).length < 2 ^ (prefixWord ++ tailWord_1039850).sum := by decide
  have hdescent : baseEnd_1039850 < baseStart_1039850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039856 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_1039856 : Nat := 118140960795 + 1039856 * 2 ^ 59
def prefixEnd_1039856 : Nat := 4983230072969 + 3 ^ 40 * 1039856 * 2
def baseEnd_1039856 : Nat := 533945939461788792317795

theorem tailTrace_1039856 : CollatzResearch.WordTrace tailWord_1039856 prefixEnd_1039856 533945939461788792317795 := by
  unfold tailWord_1039856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963332060393390055493711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25284442747191186740658281 18963332060393390055493711)
  ·
    refine ⟨28444998090590085083240567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18963332060393390055493711 28444998090590085083240567)
    ·
      refine ⟨42667497135885127624860851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28444998090590085083240567 42667497135885127624860851)
      ·
        refine ⟨64001245703827691437291277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42667497135885127624860851 64001245703827691437291277)
        ·
          refine ⟨24000467138935384288984229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64001245703827691437291277 24000467138935384288984229)
          ·
            refine ⟨4500087588550384554184543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24000467138935384288984229 4500087588550384554184543)
            ·
              refine ⟨6750131382825576831276815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500087588550384554184543 6750131382825576831276815)
              ·
                refine ⟨10125197074238365246915223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6750131382825576831276815 10125197074238365246915223)
                ·
                  refine ⟨15187795611357547870372835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125197074238365246915223 15187795611357547870372835)
                  ·
                    refine ⟨22781693417036321805559253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15187795611357547870372835 22781693417036321805559253)
                    ·
                      refine ⟨533945939461788792317795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22781693417036321805559253 533945939461788792317795)
                      ·
                        rfl

theorem cell23_1039856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_1039856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039856 prefixEnd_1039856 := by exact prefixLift 1039856
  have htrace : WordTrace (prefixWord ++ tailWord_1039856) baseStart_1039856 baseEnd_1039856 := by
    simpa [prefixWord, tailWord_1039856, baseEnd_1039856] using wordTrace_append hprefix tailTrace_1039856
  have hstable : (prefixWord ++ tailWord_1039856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039856).length < 2 ^ (prefixWord ++ tailWord_1039856).sum := by decide
  have hdescent : baseEnd_1039856 < baseStart_1039856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039861 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1039861 : Nat := 118140960795 + 1039861 * 2 ^ 59
def prefixEnd_1039861 : Nat := 4983230072969 + 3 ^ 40 * 1039861 * 2
def baseEnd_1039861 : Nat := 533948506865061272755273

theorem tailTrace_1039861 : CollatzResearch.WordTrace tailWord_1039861 prefixEnd_1039861 533948506865061272755273 := by
  unfold tailWord_1039861
  simp only [CollatzResearch.WordTrace]
  refine ⟨37926846485768665964919437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25284564323845777309946291 37926846485768665964919437)
  ·
    refine ⟨14222567432163249736844789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37926846485768665964919437 14222567432163249736844789)
    ·
      refine ⟨1333365696765304662829199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14222567432163249736844789 1333365696765304662829199)
      ·
        refine ⟨2000048545147956994243799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333365696765304662829199 2000048545147956994243799)
        ·
          refine ⟨3000072817721935491365699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000048545147956994243799 3000072817721935491365699)
          ·
            refine ⟨4500109226582903237048549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000072817721935491365699 4500109226582903237048549)
            ·
              refine ⟨843770479984294356946603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4500109226582903237048549 843770479984294356946603)
              ·
                refine ⟨1265655719976441535419905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843770479984294356946603 1265655719976441535419905)
                ·
                  refine ⟨949241789982331151564929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1265655719976441535419905 949241789982331151564929)
                  ·
                    refine ⟨711931342486748363673697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 949241789982331151564929 711931342486748363673697)
                    ·
                      refine ⟨533948506865061272755273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711931342486748363673697 533948506865061272755273)
                      ·
                        rfl

theorem cell23_1039861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1039861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039861 prefixEnd_1039861 := by exact prefixLift 1039861
  have htrace : WordTrace (prefixWord ++ tailWord_1039861) baseStart_1039861 baseEnd_1039861 := by
    simpa [prefixWord, tailWord_1039861, baseEnd_1039861] using wordTrace_append hprefix tailTrace_1039861
  have hstable : (prefixWord ++ tailWord_1039861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039861).length < 2 ^ (prefixWord ++ tailWord_1039861).sum := by decide
  have hdescent : baseEnd_1039861 < baseStart_1039861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039900 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_1039900 : Nat := 118140960795 + 1039900 * 2 ^ 59
def prefixEnd_1039900 : Nat := 4983230072969 + 3 ^ 40 * 1039900 * 2
def baseEnd_1039900 : Nat := 533968532610586620167593

theorem tailTrace_1039900 : CollatzResearch.WordTrace tailWord_1039900 prefixEnd_1039900 533968532610586620167593 := by
  unfold tailWord_1039900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964134466313687812794577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25285512621751583750392769 18964134466313687812794577)
  ·
    refine ⟨14223100849735265859595933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18964134466313687812794577 14223100849735265859595933)
    ·
      refine ⟨5333662818650724697348475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14223100849735265859595933 5333662818650724697348475)
      ·
        refine ⟨8000494227976087046022713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333662818650724697348475 8000494227976087046022713)
        ·
          refine ⟨6000370670982065284517035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000494227976087046022713 6000370670982065284517035)
          ·
            refine ⟨9000556006473097926775553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000370670982065284517035 9000556006473097926775553)
            ·
              refine ⟨6750417004854823445081665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000556006473097926775553 6750417004854823445081665)
              ·
                refine ⟨5062812753641117583811249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750417004854823445081665 5062812753641117583811249)
                ·
                  refine ⟨3797109565230838187858437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062812753641117583811249 3797109565230838187858437)
                  ·
                    refine ⟨711958043480782160223457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3797109565230838187858437 711958043480782160223457)
                    ·
                      refine ⟨533968532610586620167593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711958043480782160223457 533968532610586620167593)
                      ·
                        rfl

theorem cell23_1039900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_1039900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039900 prefixEnd_1039900 := by exact prefixLift 1039900
  have htrace : WordTrace (prefixWord ++ tailWord_1039900) baseStart_1039900 baseEnd_1039900 := by
    simpa [prefixWord, tailWord_1039900, baseEnd_1039900] using wordTrace_append hprefix tailTrace_1039900
  have hstable : (prefixWord ++ tailWord_1039900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039900).length < 2 ^ (prefixWord ++ tailWord_1039900).sum := by decide
  have hdescent : baseEnd_1039900 < baseStart_1039900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039923 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 6]
def baseStart_1039923 : Nat := 118140960795 + 1039923 * 2 ^ 59
def prefixEnd_1039923 : Nat := 4983230072969 + 3 ^ 40 * 1039923 * 2
def baseEnd_1039923 : Nat := 59331149185071114464443

theorem tailTrace_1039923 : CollatzResearch.WordTrace tailWord_1039923 prefixEnd_1039923 59331149185071114464443 := by
  unfold tailWord_1039923
  simp only [CollatzResearch.WordTrace]
  refine ⟨37929107811544050553676423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25286071874362700369117615 37929107811544050553676423)
  ·
    refine ⟨56893661717316075830514635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37929107811544050553676423 56893661717316075830514635)
    ·
      refine ⟨85340492575974113745771953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56893661717316075830514635 85340492575974113745771953)
      ·
        refine ⟨64005369431980585309328965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85340492575974113745771953 64005369431980585309328965)
        ·
          refine ⟨12001006768496359745499181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64005369431980585309328965 12001006768496359745499181)
          ·
            refine ⟨4500377538186134904562193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12001006768496359745499181 4500377538186134904562193)
            ·
              refine ⟨3375283153639601178421645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500377538186134904562193 3375283153639601178421645)
              ·
                refine ⟨1265731182614850441908117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3375283153639601178421645 1265731182614850441908117)
                ·
                  refine ⟨59331149185071114464443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1265731182614850441908117 59331149185071114464443)
                  ·
                    rfl

theorem cell23_1039923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 6].length) (baseStart_1039923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039923 prefixEnd_1039923 := by exact prefixLift 1039923
  have htrace : WordTrace (prefixWord ++ tailWord_1039923) baseStart_1039923 baseEnd_1039923 := by
    simpa [prefixWord, tailWord_1039923, baseEnd_1039923] using wordTrace_append hprefix tailTrace_1039923
  have hstable : (prefixWord ++ tailWord_1039923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039923).length < 2 ^ (prefixWord ++ tailWord_1039923).sum := by decide
  have hdescent : baseEnd_1039923 < baseStart_1039923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039950 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_1039950 : Nat := 118140960795 + 1039950 * 2 ^ 59
def prefixEnd_1039950 : Nat := 4983230072969 + 3 ^ 40 * 1039950 * 2
def baseEnd_1039950 : Nat := 533994206643311424542363

theorem tailTrace_1039950 : CollatzResearch.WordTrace tailWord_1039950 prefixEnd_1039950 533994206643311424542363 := by
  unfold tailWord_1039950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741261572805779270613663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25286728388297489443272869 4741261572805779270613663)
  ·
    refine ⟨7111892359208668905920495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4741261572805779270613663 7111892359208668905920495)
    ·
      refine ⟨10667838538813003358880743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111892359208668905920495 10667838538813003358880743)
      ·
        refine ⟨16001757808219505038321115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667838538813003358880743 16001757808219505038321115)
        ·
          refine ⟨24002636712329257557481673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001757808219505038321115 24002636712329257557481673)
          ·
            refine ⟨18001977534246943168111255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24002636712329257557481673 18001977534246943168111255)
            ·
              refine ⟨27002966301370414752166883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18001977534246943168111255 27002966301370414752166883)
              ·
                refine ⟨40504449452055622128250325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27002966301370414752166883 40504449452055622128250325)
                ·
                  refine ⟨949323034032553643630867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40504449452055622128250325 949323034032553643630867)
                  ·
                    refine ⟨1423984551048830465446301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949323034032553643630867 1423984551048830465446301)
                    ·
                      refine ⟨533994206643311424542363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1423984551048830465446301 533994206643311424542363)
                      ·
                        rfl

theorem cell23_1039950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_1039950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039950 prefixEnd_1039950 := by exact prefixLift 1039950
  have htrace : WordTrace (prefixWord ++ tailWord_1039950) baseStart_1039950 baseEnd_1039950 := by
    simpa [prefixWord, tailWord_1039950, baseEnd_1039950] using wordTrace_append hprefix tailTrace_1039950
  have hstable : (prefixWord ++ tailWord_1039950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039950).length < 2 ^ (prefixWord ++ tailWord_1039950).sum := by decide
  have hdescent : baseEnd_1039950 < baseStart_1039950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039960 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_1039960 : Nat := 118140960795 + 1039960 * 2 ^ 59
def prefixEnd_1039960 : Nat := 4983230072969 + 3 ^ 40 * 1039960 * 2
def baseEnd_1039960 : Nat := 533999341449856385417317

theorem tailTrace_1039960 : CollatzResearch.WordTrace tailWord_1039960 prefixEnd_1039960 533999341449856385417317 := by
  unfold tailWord_1039960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965228656205002936386667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25286971541606670581848889 18965228656205002936386667)
  ·
    refine ⟨28447842984307504404580001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18965228656205002936386667 28447842984307504404580001)
    ·
      refine ⟨21335882238230628303435001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28447842984307504404580001 21335882238230628303435001)
      ·
        refine ⟨16001911678672971227576251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21335882238230628303435001 16001911678672971227576251)
        ·
          refine ⟨24002867518009456841364377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001911678672971227576251 24002867518009456841364377)
          ·
            refine ⟨18002150638507092631023283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24002867518009456841364377 18002150638507092631023283)
            ·
              refine ⟨27003225957760638946534925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002150638507092631023283 27003225957760638946534925)
              ·
                refine ⟨10126209734160239604950597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27003225957760638946534925 10126209734160239604950597)
                ·
                  refine ⟨1898664325155044925928237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10126209734160239604950597 1898664325155044925928237)
                  ·
                    refine ⟨711999121933141847223089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898664325155044925928237 711999121933141847223089)
                    ·
                      refine ⟨533999341449856385417317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 711999121933141847223089 533999341449856385417317)
                      ·
                        rfl

theorem cell23_1039960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_1039960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039960 prefixEnd_1039960 := by exact prefixLift 1039960
  have htrace : WordTrace (prefixWord ++ tailWord_1039960) baseStart_1039960 baseEnd_1039960 := by
    simpa [prefixWord, tailWord_1039960, baseEnd_1039960] using wordTrace_append hprefix tailTrace_1039960
  have hstable : (prefixWord ++ tailWord_1039960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039960).length < 2 ^ (prefixWord ++ tailWord_1039960).sum := by decide
  have hdescent : baseEnd_1039960 < baseStart_1039960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039993 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1039993 : Nat := 118140960795 + 1039993 * 2 ^ 59
def prefixEnd_1039993 : Nat := 4983230072969 + 3 ^ 40 * 1039993 * 2
def baseEnd_1039993 : Nat := 534016286311454756304665

theorem tailTrace_1039993 : CollatzResearch.WordTrace tailWord_1039993 prefixEnd_1039993 534016286311454756304665 := by
  unfold tailWord_1039993
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931660921290452508724633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25287773947526968339149755 37931660921290452508724633)
  ·
    refine ⟨28448745690967839381543475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37931660921290452508724633 28448745690967839381543475)
    ·
      refine ⟨42673118536451759072315213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28448745690967839381543475 42673118536451759072315213)
      ·
        refine ⟨16002419451169409652118205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42673118536451759072315213 16002419451169409652118205)
        ·
          refine ⟨6000907294188528619544327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16002419451169409652118205 6000907294188528619544327)
          ·
            refine ⟨9001360941282792929316491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6000907294188528619544327 9001360941282792929316491)
            ·
              refine ⟨13502041411924189393974737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001360941282792929316491 13502041411924189393974737)
              ·
                refine ⟨10126531058943142045481053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502041411924189393974737 10126531058943142045481053)
                ·
                  refine ⟨3797449147103678267055395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10126531058943142045481053 3797449147103678267055395)
                  ·
                    refine ⟨5696173720655517400583093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797449147103678267055395 5696173720655517400583093)
                    ·
                      refine ⟨534016286311454756304665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5696173720655517400583093 534016286311454756304665)
                      ·
                        rfl

theorem cell23_1039993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1039993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1039993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1039993 prefixEnd_1039993 := by exact prefixLift 1039993
  have htrace : WordTrace (prefixWord ++ tailWord_1039993) baseStart_1039993 baseEnd_1039993 := by
    simpa [prefixWord, tailWord_1039993, baseEnd_1039993] using wordTrace_append hprefix tailTrace_1039993
  have hstable : (prefixWord ++ tailWord_1039993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039993).length < 2 ^ (prefixWord ++ tailWord_1039993).sum := by decide
  have hdescent : baseEnd_1039993 < baseStart_1039993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040001 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_1040001 : Nat := 118140960795 + 1040001 * 2 ^ 59
def prefixEnd_1040001 : Nat := 4983230072969 + 3 ^ 40 * 1040001 * 2
def baseEnd_1040001 : Nat := 534020394156690725004629

theorem tailTrace_1040001 : CollatzResearch.WordTrace tailWord_1040001 prefixEnd_1040001 534020394156690725004629 := by
  unfold tailWord_1040001
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931952705261469875015857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25287968470174313250010571 37931952705261469875015857)
  ·
    refine ⟨28448964528946102406261893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37931952705261469875015857 28448964528946102406261893)
    ·
      refine ⟨5334180849177394201174105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28448964528946102406261893 5334180849177394201174105)
      ·
        refine ⟨4000635636883045650880579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334180849177394201174105 4000635636883045650880579)
        ·
          refine ⟨6000953455324568476320869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000635636883045650880579 6000953455324568476320869)
          ·
            refine ⟨1125178772873356589310163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6000953455324568476320869 1125178772873356589310163)
            ·
              refine ⟨1687768159310034883965245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125178772873356589310163 1687768159310034883965245)
              ·
                refine ⟨632913059741263081486967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687768159310034883965245 632913059741263081486967)
                ·
                  refine ⟨949369589611894622230451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632913059741263081486967 949369589611894622230451)
                  ·
                    refine ⟨1424054384417841933345677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949369589611894622230451 1424054384417841933345677)
                    ·
                      refine ⟨534020394156690725004629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424054384417841933345677 534020394156690725004629)
                      ·
                        rfl

theorem cell23_1040001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_1040001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040001 prefixEnd_1040001 := by exact prefixLift 1040001
  have htrace : WordTrace (prefixWord ++ tailWord_1040001) baseStart_1040001 baseEnd_1040001 := by
    simpa [prefixWord, tailWord_1040001, baseEnd_1040001] using wordTrace_append hprefix tailTrace_1040001
  have hstable : (prefixWord ++ tailWord_1040001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040001).length < 2 ^ (prefixWord ++ tailWord_1040001).sum := by decide
  have hdescent : baseEnd_1040001 < baseStart_1040001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040003 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1040003 : Nat := 118140960795 + 1040003 * 2 ^ 59
def prefixEnd_1040003 : Nat := 4983230072969 + 3 ^ 40 * 1040003 * 2
def baseEnd_1040003 : Nat := 534021421117999717179619

theorem tailTrace_1040003 : CollatzResearch.WordTrace tailWord_1040003 prefixEnd_1040003 534021421117999717179619 := by
  unfold tailWord_1040003
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932025651254224216588663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25288017100836149477725775 37932025651254224216588663)
  ·
    refine ⟨56898038476881336324882995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37932025651254224216588663 56898038476881336324882995)
    ·
      refine ⟨85347057715322004487324493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56898038476881336324882995 85347057715322004487324493)
      ·
        refine ⟨32005146643245751682746685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85347057715322004487324493 32005146643245751682746685)
        ·
          refine ⟨12001929991217156881030007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32005146643245751682746685 12001929991217156881030007)
          ·
            refine ⟨18002894986825735321545011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001929991217156881030007 18002894986825735321545011)
            ·
              refine ⟨27004342480238602982317517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002894986825735321545011 27004342480238602982317517)
              ·
                refine ⟨10126628430089476118369069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27004342480238602982317517 10126628430089476118369069)
                ·
                  refine ⟨3797485661283553544388401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10126628430089476118369069 3797485661283553544388401)
                  ·
                    refine ⟨2848114245962665158291301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797485661283553544388401 2848114245962665158291301)
                    ·
                      refine ⟨534021421117999717179619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2848114245962665158291301 534021421117999717179619)
                      ·
                        rfl

theorem cell23_1040003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1040003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040003 prefixEnd_1040003 := by exact prefixLift 1040003
  have htrace : WordTrace (prefixWord ++ tailWord_1040003) baseStart_1040003 baseEnd_1040003 := by
    simpa [prefixWord, tailWord_1040003, baseEnd_1040003] using wordTrace_append hprefix tailTrace_1040003
  have hstable : (prefixWord ++ tailWord_1040003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040003).length < 2 ^ (prefixWord ++ tailWord_1040003).sum := by decide
  have hdescent : baseEnd_1040003 < baseStart_1040003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040010 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1040010 : Nat := 118140960795 + 1040010 * 2 ^ 59
def prefixEnd_1040010 : Nat := 4983230072969 + 3 ^ 40 * 1040010 * 2
def baseEnd_1040010 : Nat := 534025015482581189792087

theorem tailTrace_1040010 : CollatzResearch.WordTrace tailWord_1040010 prefixEnd_1040010 534025015482581189792087 := by
  unfold tailWord_1040010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483070240557216103023371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25288187308152576274728989 9483070240557216103023371)
  ·
    refine ⟨14224605360835824154535057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483070240557216103023371 14224605360835824154535057)
    ·
      refine ⟨10668454020626868115901293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14224605360835824154535057 10668454020626868115901293)
      ·
        refine ⟨4000670257735075543462985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10668454020626868115901293 4000670257735075543462985)
        ·
          refine ⟨3000502693301306657597239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000670257735075543462985 3000502693301306657597239)
          ·
            refine ⟨4500754039951959986395859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000502693301306657597239 4500754039951959986395859)
            ·
              refine ⟨6751131059927939979593789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500754039951959986395859 6751131059927939979593789)
              ·
                refine ⟨2531674147472977492347671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6751131059927939979593789 2531674147472977492347671)
                ·
                  refine ⟨3797511221209466238521507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531674147472977492347671 3797511221209466238521507)
                  ·
                    refine ⟨5696266831814199357782261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797511221209466238521507 5696266831814199357782261)
                    ·
                      refine ⟨534025015482581189792087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5696266831814199357782261 534025015482581189792087)
                      ·
                        rfl

theorem cell23_1040010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1040010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040010 prefixEnd_1040010 := by exact prefixLift 1040010
  have htrace : WordTrace (prefixWord ++ tailWord_1040010) baseStart_1040010 baseEnd_1040010 := by
    simpa [prefixWord, tailWord_1040010, baseEnd_1040010] using wordTrace_append hprefix tailTrace_1040010
  have hstable : (prefixWord ++ tailWord_1040010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040010).length < 2 ^ (prefixWord ++ tailWord_1040010).sum := by decide
  have hdescent : baseEnd_1040010 < baseStart_1040010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040018 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1040018 : Nat := 118140960795 + 1040018 * 2 ^ 59
def prefixEnd_1040018 : Nat := 4983230072969 + 3 ^ 40 * 1040018 * 2
def baseEnd_1040018 : Nat := 534029123327817158492051

theorem tailTrace_1040018 : CollatzResearch.WordTrace tailWord_1040018 prefixEnd_1040018 534029123327817158492051 := by
  unfold tailWord_1040018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483143186549970444596177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25288381830799921185589805 9483143186549970444596177)
  ·
    refine ⟨7112357389912477833447133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9483143186549970444596177 7112357389912477833447133)
    ·
      refine ⟨2667134021217179187542675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7112357389912477833447133 2667134021217179187542675)
      ·
        refine ⟨4000701031825768781314013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667134021217179187542675 4000701031825768781314013)
        ·
          refine ⟨1500262886934663292992755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4000701031825768781314013 1500262886934663292992755)
          ·
            refine ⟨2250394330401994939489133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500262886934663292992755 2250394330401994939489133)
            ·
              refine ⟨843897873900748102308425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250394330401994939489133 843897873900748102308425)
              ·
                refine ⟨632923405425561076731319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843897873900748102308425 632923405425561076731319)
                ·
                  refine ⟨949385108138341615096979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632923405425561076731319 949385108138341615096979)
                  ·
                    refine ⟨1424077662207512422645469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949385108138341615096979 1424077662207512422645469)
                    ·
                      refine ⟨534029123327817158492051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424077662207512422645469 534029123327817158492051)
                      ·
                        rfl

theorem cell23_1040018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1040018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040018 prefixEnd_1040018 := by exact prefixLift 1040018
  have htrace : WordTrace (prefixWord ++ tailWord_1040018) baseStart_1040018 baseEnd_1040018 := by
    simpa [prefixWord, tailWord_1040018, baseEnd_1040018] using wordTrace_append hprefix tailTrace_1040018
  have hstable : (prefixWord ++ tailWord_1040018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040018).length < 2 ^ (prefixWord ++ tailWord_1040018).sum := by decide
  have hdescent : baseEnd_1040018 < baseStart_1040018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040024 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1040024 : Nat := 118140960795 + 1040024 * 2 ^ 59
def prefixEnd_1040024 : Nat := 4983230072969 + 3 ^ 40 * 1040024 * 2
def baseEnd_1040024 : Nat := 534032204211744135017023

theorem tailTrace_1040024 : CollatzResearch.WordTrace tailWord_1040024 prefixEnd_1040024 534032204211744135017023 := by
  unfold tailWord_1040024
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966395792089072401551563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25288527722785429868735417 18966395792089072401551563)
  ·
    refine ⟨28449593688133608602327345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18966395792089072401551563 28449593688133608602327345)
    ·
      refine ⟨21337195266100206451745509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28449593688133608602327345 21337195266100206451745509)
      ·
        refine ⟨4000724112393788709702283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21337195266100206451745509 4000724112393788709702283)
        ·
          refine ⟨6001086168590683064553425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000724112393788709702283 6001086168590683064553425)
          ·
            refine ⟨4500814626443012298415069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6001086168590683064553425 4500814626443012298415069)
            ·
              refine ⟨1687805484916129611905651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4500814626443012298415069 1687805484916129611905651)
              ·
                refine ⟨2531708227374194417858477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687805484916129611905651 2531708227374194417858477)
                ·
                  refine ⟨949390585265322906696929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2531708227374194417858477 949390585265322906696929)
                  ·
                    refine ⟨712042938948992180022697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 949390585265322906696929 712042938948992180022697)
                    ·
                      refine ⟨534032204211744135017023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712042938948992180022697 534032204211744135017023)
                      ·
                        rfl

theorem cell23_1040024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1040024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040024 prefixEnd_1040024 := by exact prefixLift 1040024
  have htrace : WordTrace (prefixWord ++ tailWord_1040024) baseStart_1040024 baseEnd_1040024 := by
    simpa [prefixWord, tailWord_1040024, baseEnd_1040024] using wordTrace_append hprefix tailTrace_1040024
  have hstable : (prefixWord ++ tailWord_1040024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040024).length < 2 ^ (prefixWord ++ tailWord_1040024).sum := by decide
  have hdescent : baseEnd_1040024 < baseStart_1040024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040030 : List Nat := [4, 3, 1, 1, 1, 2, 1, 10]
def baseStart_1040030 : Nat := 118140960795 + 1040030 * 2 ^ 59
def prefixEnd_1040030 : Nat := 4983230072969 + 3 ^ 40 * 1040030 * 2
def baseEnd_1040030 : Nat := 19779084633173004131185

theorem tailTrace_1040030 : CollatzResearch.WordTrace tailWord_1040030 prefixEnd_1040030 19779084633173004131185 := by
  unfold tailWord_1040030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741626302769550978477693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25288673614770938551881029 4741626302769550978477693)
  ·
    refine ⟨1778109863538581616929135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4741626302769550978477693 1778109863538581616929135)
    ·
      refine ⟨2667164795307872425393703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1778109863538581616929135 2667164795307872425393703)
      ·
        refine ⟨4000747192961808638090555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667164795307872425393703 4000747192961808638090555)
        ·
          refine ⟨6001120789442712957135833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000747192961808638090555 6001120789442712957135833)
          ·
            refine ⟨4500840592082034717851875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6001120789442712957135833 4500840592082034717851875)
            ·
              refine ⟨6751260888123052076777813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500840592082034717851875 6751260888123052076777813)
              ·
                refine ⟨19779084633173004131185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6751260888123052076777813 19779084633173004131185)
                ·
                  rfl

theorem cell23_1040030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_1040030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040030 prefixEnd_1040030 := by exact prefixLift 1040030
  have htrace : WordTrace (prefixWord ++ tailWord_1040030) baseStart_1040030 baseEnd_1040030 := by
    simpa [prefixWord, tailWord_1040030, baseEnd_1040030] using wordTrace_append hprefix tailTrace_1040030
  have hstable : (prefixWord ++ tailWord_1040030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040030).length < 2 ^ (prefixWord ++ tailWord_1040030).sum := by decide
  have hdescent : baseEnd_1040030 < baseStart_1040030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040054 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1040054 : Nat := 118140960795 + 1040054 * 2 ^ 59
def prefixEnd_1040054 : Nat := 4983230072969 + 3 ^ 40 * 1040054 * 2
def baseEnd_1040054 : Nat := 534047608631379017641885

theorem tailTrace_1040054 : CollatzResearch.WordTrace tailWord_1040054 prefixEnd_1040054 534047608631379017641885 := by
  unfold tailWord_1040054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370867860879341245418451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25289257182712973284463477 2370867860879341245418451)
  ·
    refine ⟨3556301791319011868127677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370867860879341245418451 3556301791319011868127677)
    ·
      refine ⟨1333613171744629450547879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3556301791319011868127677 1333613171744629450547879)
      ·
        refine ⟨2000419757616944175821819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333613171744629450547879 2000419757616944175821819)
        ·
          refine ⟨3000629636425416263732729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000419757616944175821819 3000629636425416263732729)
          ·
            refine ⟨2250472227319062197799547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3000629636425416263732729 2250472227319062197799547)
            ·
              refine ⟨3375708340978593296699321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250472227319062197799547 3375708340978593296699321)
              ·
                refine ⟨2531781255733944972524491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375708340978593296699321 2531781255733944972524491)
                ·
                  refine ⟨3797671883600917458786737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531781255733944972524491 3797671883600917458786737)
                  ·
                    refine ⟨2848253912700688094090053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797671883600917458786737 2848253912700688094090053)
                    ·
                      refine ⟨534047608631379017641885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2848253912700688094090053 534047608631379017641885)
                      ·
                        rfl

theorem cell23_1040054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1040054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040054 prefixEnd_1040054 := by exact prefixLift 1040054
  have htrace : WordTrace (prefixWord ++ tailWord_1040054) baseStart_1040054 baseEnd_1040054 := by
    simpa [prefixWord, tailWord_1040054, baseEnd_1040054] using wordTrace_append hprefix tailTrace_1040054
  have hstable : (prefixWord ++ tailWord_1040054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040054).length < 2 ^ (prefixWord ++ tailWord_1040054).sum := by decide
  have hdescent : baseEnd_1040054 < baseStart_1040054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040077 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1040077 : Nat := 118140960795 + 1040077 * 2 ^ 59
def prefixEnd_1040077 : Nat := 4983230072969 + 3 ^ 40 * 1040077 * 2
def baseEnd_1040077 : Nat := 178019806228810809218093

theorem tailTrace_1040077 : CollatzResearch.WordTrace tailWord_1040077 prefixEnd_1040077 178019806228810809218093 := by
  unfold tailWord_1040077
  simp only [CollatzResearch.WordTrace]
  refine ⟨37934724652986134854782485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25289816435324089903188323 37934724652986134854782485)
  ·
    refine ⟨1778190218108725071317929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37934724652986134854782485 1778190218108725071317929)
    ·
      refine ⟨1333642663581543803488447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1778190218108725071317929 1333642663581543803488447)
      ·
        refine ⟨2000463995372315705232671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333642663581543803488447 2000463995372315705232671)
        ·
          refine ⟨3000695993058473557849007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000463995372315705232671 3000695993058473557849007)
          ·
            refine ⟨4501043989587710336773511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000695993058473557849007 4501043989587710336773511)
            ·
              refine ⟨6751565984381565505160267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501043989587710336773511 6751565984381565505160267)
              ·
                refine ⟨10127348976572348257740401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751565984381565505160267 10127348976572348257740401)
                ·
                  refine ⟨7595511732429261193305301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127348976572348257740401 7595511732429261193305301)
                  ·
                    refine ⟨178019806228810809218093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7595511732429261193305301 178019806228810809218093)
                    ·
                      rfl

theorem cell23_1040077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1040077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040077 prefixEnd_1040077 := by exact prefixLift 1040077
  have htrace : WordTrace (prefixWord ++ tailWord_1040077) baseStart_1040077 baseEnd_1040077 := by
    simpa [prefixWord, tailWord_1040077, baseEnd_1040077] using wordTrace_append hprefix tailTrace_1040077
  have hstable : (prefixWord ++ tailWord_1040077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040077).length < 2 ^ (prefixWord ++ tailWord_1040077).sum := by decide
  have hdescent : baseEnd_1040077 < baseStart_1040077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040084 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1040084 : Nat := 118140960795 + 1040084 * 2 ^ 59
def prefixEnd_1040084 : Nat := 4983230072969 + 3 ^ 40 * 1040084 * 2
def baseEnd_1040084 : Nat := 534063013051013900266747

theorem tailTrace_1040084 : CollatzResearch.WordTrace tailWord_1040084 prefixEnd_1040084 534063013051013900266747 := by
  unfold tailWord_1040084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18967489981980387525143653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25289986642640516700191537 18967489981980387525143653)
  ·
    refine ⟨3556404371621322660964435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18967489981980387525143653 3556404371621322660964435)
    ·
      refine ⟨5334606557431983991446653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556404371621322660964435 5334606557431983991446653)
      ·
        refine ⟨2000477459036993996792495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5334606557431983991446653 2000477459036993996792495)
        ·
          refine ⟨3000716188555490995188743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000477459036993996792495 3000716188555490995188743)
          ·
            refine ⟨4501074282833236492783115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000716188555490995188743 4501074282833236492783115)
            ·
              refine ⟨6751611424249854739174673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501074282833236492783115 6751611424249854739174673)
              ·
                refine ⟨5063708568187391054381005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6751611424249854739174673 5063708568187391054381005)
                ·
                  refine ⟨1898890713070271645392877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5063708568187391054381005 1898890713070271645392877)
                  ·
                    refine ⟨712084017401351867022329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898890713070271645392877 712084017401351867022329)
                    ·
                      refine ⟨534063013051013900266747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712084017401351867022329 534063013051013900266747)
                      ·
                        rfl

theorem cell23_1040084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1040084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040084 prefixEnd_1040084 := by exact prefixLift 1040084
  have htrace : WordTrace (prefixWord ++ tailWord_1040084) baseStart_1040084 baseEnd_1040084 := by
    simpa [prefixWord, tailWord_1040084, baseEnd_1040084] using wordTrace_append hprefix tailTrace_1040084
  have hstable : (prefixWord ++ tailWord_1040084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040084).length < 2 ^ (prefixWord ++ tailWord_1040084).sum := by decide
  have hdescent : baseEnd_1040084 < baseStart_1040084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040090 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_1040090 : Nat := 118140960795 + 1040090 * 2 ^ 59
def prefixEnd_1040090 : Nat := 4983230072969 + 3 ^ 40 * 1040090 * 2
def baseEnd_1040090 : Nat := 178022031311646958930573

theorem tailTrace_1040090 : CollatzResearch.WordTrace tailWord_1040090 prefixEnd_1040090 178022031311646958930573 := by
  unfold tailWord_1040090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483799700484759518751431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25290132534626025383337149 9483799700484759518751431)
  ·
    refine ⟨14225699550727139278127147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483799700484759518751431 14225699550727139278127147)
    ·
      refine ⟨21338549326090708917190721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14225699550727139278127147 21338549326090708917190721)
      ·
        refine ⟨16003911994568031687893041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21338549326090708917190721 16003911994568031687893041)
        ·
          refine ⟨12002933995926023765919781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16003911994568031687893041 12002933995926023765919781)
          ·
            refine ⟨2250550124236129456109959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12002933995926023765919781 2250550124236129456109959)
            ·
              refine ⟨3375825186354194184164939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250550124236129456109959 3375825186354194184164939)
              ·
                refine ⟨5063737779531291276247409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375825186354194184164939 5063737779531291276247409)
                ·
                  refine ⟨3797803334648468457185557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5063737779531291276247409 3797803334648468457185557)
                  ·
                    refine ⟨178022031311646958930573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3797803334648468457185557 178022031311646958930573)
                    ·
                      rfl

theorem cell23_1040090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_1040090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040090 prefixEnd_1040090 := by exact prefixLift 1040090
  have htrace : WordTrace (prefixWord ++ tailWord_1040090) baseStart_1040090 baseEnd_1040090 := by
    simpa [prefixWord, tailWord_1040090, baseEnd_1040090] using wordTrace_append hprefix tailTrace_1040090
  have hstable : (prefixWord ++ tailWord_1040090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040090).length < 2 ^ (prefixWord ++ tailWord_1040090).sum := by decide
  have hdescent : baseEnd_1040090 < baseStart_1040090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040100 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1040100 : Nat := 118140960795 + 1040100 * 2 ^ 59
def prefixEnd_1040100 : Nat := 4983230072969 + 3 ^ 40 * 1040100 * 2
def baseEnd_1040100 : Nat := 534071228741485837666673

theorem tailTrace_1040100 : CollatzResearch.WordTrace tailWord_1040100 prefixEnd_1040100 534071228741485837666673 := by
  unfold tailWord_1040100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18967781765951404891434877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25290375687935206521913169 18967781765951404891434877)
  ·
    refine ⟨7112918162231776834288079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18967781765951404891434877 7112918162231776834288079)
    ·
      refine ⟨10669377243347665251432119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7112918162231776834288079 10669377243347665251432119)
      ·
        refine ⟨16004065865021497877148179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10669377243347665251432119 16004065865021497877148179)
        ·
          refine ⟨24006098797532246815722269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16004065865021497877148179 24006098797532246815722269)
          ·
            refine ⟨9002287049074592555895851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24006098797532246815722269 9002287049074592555895851)
            ·
              refine ⟨13503430573611888833843777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002287049074592555895851 13503430573611888833843777)
              ·
                refine ⟨10127572930208916625382833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13503430573611888833843777 10127572930208916625382833)
                ·
                  refine ⟨7595679697656687469037125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127572930208916625382833 7595679697656687469037125)
                  ·
                    refine ⟨1424189943310628900444461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7595679697656687469037125 1424189943310628900444461)
                    ·
                      refine ⟨534071228741485837666673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424189943310628900444461 534071228741485837666673)
                      ·
                        rfl

theorem cell23_1040100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1040100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040100 prefixEnd_1040100 := by exact prefixLift 1040100
  have htrace : WordTrace (prefixWord ++ tailWord_1040100) baseStart_1040100 baseEnd_1040100 := by
    simpa [prefixWord, tailWord_1040100, baseEnd_1040100] using wordTrace_append hprefix tailTrace_1040100
  have hstable : (prefixWord ++ tailWord_1040100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040100).length < 2 ^ (prefixWord ++ tailWord_1040100).sum := by decide
  have hdescent : baseEnd_1040100 < baseStart_1040100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040110 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1040110 : Nat := 118140960795 + 1040110 * 2 ^ 59
def prefixEnd_1040110 : Nat := 4983230072969 + 3 ^ 40 * 1040110 * 2
def baseEnd_1040110 : Nat := 534076363548030798541627

theorem tailTrace_1040110 : CollatzResearch.WordTrace tailWord_1040110 prefixEnd_1040110 534076363548030798541627 := by
  unfold tailWord_1040110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741991032733322686341723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25290618841244387660489189 4741991032733322686341723)
  ·
    refine ⟨7112986549099984029512585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4741991032733322686341723 7112986549099984029512585)
    ·
      refine ⟨5334739911824988022134439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7112986549099984029512585 5334739911824988022134439)
      ·
        refine ⟨8002109867737482033201659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5334739911824988022134439 8002109867737482033201659)
        ·
          refine ⟨12003164801606223049802489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002109867737482033201659 12003164801606223049802489)
          ·
            refine ⟨9002373601204667287351867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12003164801606223049802489 9002373601204667287351867)
            ·
              refine ⟨13503560401807000931027801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002373601204667287351867 13503560401807000931027801)
              ·
                refine ⟨10127670301355250698270851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13503560401807000931027801 10127670301355250698270851)
                ·
                  refine ⟨15191505452032876047406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10127670301355250698270851 15191505452032876047406277)
                  ·
                    refine ⟨2848407272256164258888677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15191505452032876047406277 2848407272256164258888677)
                    ·
                      refine ⟨534076363548030798541627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2848407272256164258888677 534076363548030798541627)
                      ·
                        rfl

theorem cell23_1040110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1040110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040110 prefixEnd_1040110 := by exact prefixLift 1040110
  have htrace : WordTrace (prefixWord ++ tailWord_1040110) baseStart_1040110 baseEnd_1040110 := by
    simpa [prefixWord, tailWord_1040110, baseEnd_1040110] using wordTrace_append hprefix tailTrace_1040110
  have hstable : (prefixWord ++ tailWord_1040110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040110).length < 2 ^ (prefixWord ++ tailWord_1040110).sum := by decide
  have hdescent : baseEnd_1040110 < baseStart_1040110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040114 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1040114 : Nat := 118140960795 + 1040114 * 2 ^ 59
def prefixEnd_1040114 : Nat := 4983230072969 + 3 ^ 40 * 1040114 * 2
def baseEnd_1040114 : Nat := 534078417470648782891609

theorem tailTrace_1040114 : CollatzResearch.WordTrace tailWord_1040114 prefixEnd_1040114 534078417470648782891609 := by
  unfold tailWord_1040114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484018538463022543469849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25290716102568060115919597 9484018538463022543469849)
  ·
    refine ⟨7113013903847266907602387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9484018538463022543469849 7113013903847266907602387)
    ·
      refine ⟨10669520855770900361403581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113013903847266907602387 10669520855770900361403581)
      ·
        refine ⟨4001070320914087635526343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10669520855770900361403581 4001070320914087635526343)
        ·
          refine ⟨6001605481371131453289515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001070320914087635526343 6001605481371131453289515)
          ·
            refine ⟨9002408222056697179934273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001605481371131453289515 9002408222056697179934273)
            ·
              refine ⟨6751806166542522884950705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9002408222056697179934273 6751806166542522884950705)
              ·
                refine ⟨5063854624906892163713029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6751806166542522884950705 5063854624906892163713029)
                ·
                  refine ⟨949472742170042280696193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5063854624906892163713029 949472742170042280696193)
                  ·
                    refine ⟨712104556627531710522145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 949472742170042280696193 712104556627531710522145)
                    ·
                      refine ⟨534078417470648782891609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712104556627531710522145 534078417470648782891609)
                      ·
                        rfl

theorem cell23_1040114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1040114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040114 prefixEnd_1040114 := by exact prefixLift 1040114
  have htrace : WordTrace (prefixWord ++ tailWord_1040114) baseStart_1040114 baseEnd_1040114 := by
    simpa [prefixWord, tailWord_1040114, baseEnd_1040114] using wordTrace_append hprefix tailTrace_1040114
  have hstable : (prefixWord ++ tailWord_1040114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040114).length < 2 ^ (prefixWord ++ tailWord_1040114).sum := by decide
  have hdescent : baseEnd_1040114 < baseStart_1040114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040118 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_1040118 : Nat := 118140960795 + 1040118 * 2 ^ 59
def prefixEnd_1040118 : Nat := 4983230072969 + 3 ^ 40 * 1040118 * 2
def baseEnd_1040118 : Nat := 534080471393266767241591

theorem tailTrace_1040118 : CollatzResearch.WordTrace tailWord_1040118 prefixEnd_1040118 534080471393266767241591 := by
  unfold tailWord_1040118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371013752864849928564063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25290813363891732571350005 2371013752864849928564063)
  ·
    refine ⟨3556520629297274892846095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2371013752864849928564063 3556520629297274892846095)
    ·
      refine ⟨5334780943945912339269143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556520629297274892846095 5334780943945912339269143)
      ·
        refine ⟨8002171415918868508903715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5334780943945912339269143 8002171415918868508903715)
        ·
          refine ⟨12003257123878302763355573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002171415918868508903715 12003257123878302763355573)
          ·
            refine ⟨1125305355363590884064585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12003257123878302763355573 1125305355363590884064585)
            ·
              refine ⟨843979016522693163048439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125305355363590884064585 843979016522693163048439)
              ·
                refine ⟨1265968524784039744572659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843979016522693163048439 1265968524784039744572659)
                ·
                  refine ⟨1898952787176059616858989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1265968524784039744572659 1898952787176059616858989)
                  ·
                    refine ⟨712107295191022356322121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1898952787176059616858989 712107295191022356322121)
                    ·
                      refine ⟨534080471393266767241591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712107295191022356322121 534080471393266767241591)
                      ·
                        rfl

theorem cell23_1040118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_1040118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040118 prefixEnd_1040118 := by exact prefixLift 1040118
  have htrace : WordTrace (prefixWord ++ tailWord_1040118) baseStart_1040118 baseEnd_1040118 := by
    simpa [prefixWord, tailWord_1040118, baseEnd_1040118] using wordTrace_append hprefix tailTrace_1040118
  have hstable : (prefixWord ++ tailWord_1040118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040118).length < 2 ^ (prefixWord ++ tailWord_1040118).sum := by decide
  have hdescent : baseEnd_1040118 < baseStart_1040118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040224 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1040224 : Nat := 118140960795 + 1040224 * 2 ^ 59
def prefixEnd_1040224 : Nat := 4983230072969 + 3 ^ 40 * 1040224 * 2
def baseEnd_1040224 : Nat := 534134900342643352516103

theorem tailTrace_1040224 : CollatzResearch.WordTrace tailWord_1040224 prefixEnd_1040224 534134900342643352516103 := by
  unfold tailWord_1040224
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970043091726789480191863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25293390788969052640255817 18970043091726789480191863)
  ·
    refine ⟨28455064637590184220287795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18970043091726789480191863 28455064637590184220287795)
    ·
      refine ⟨42682596956385276330431693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28455064637590184220287795 42682596956385276330431693)
      ·
        refine ⟨16005973858644478623911885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42682596956385276330431693 16005973858644478623911885)
        ·
          refine ⟨6002240196991679483966957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16005973858644478623911885 6002240196991679483966957)
          ·
            refine ⟨2250840073871879806487609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6002240196991679483966957 2250840073871879806487609)
            ·
              refine ⟨1688130055403909854865707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250840073871879806487609 1688130055403909854865707)
              ·
                refine ⟨2532195083105864782298561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688130055403909854865707 2532195083105864782298561)
                ·
                  refine ⟨1899146312329398586723921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2532195083105864782298561 1899146312329398586723921)
                  ·
                    refine ⟨1424359734247048940042941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899146312329398586723921 1424359734247048940042941)
                    ·
                      refine ⟨534134900342643352516103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424359734247048940042941 534134900342643352516103)
                      ·
                        rfl

theorem cell23_1040224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1040224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040224 prefixEnd_1040224 := by exact prefixLift 1040224
  have htrace : WordTrace (prefixWord ++ tailWord_1040224) baseStart_1040224 baseEnd_1040224 := by
    simpa [prefixWord, tailWord_1040224, baseEnd_1040224] using wordTrace_append hprefix tailTrace_1040224
  have hstable : (prefixWord ++ tailWord_1040224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040224).length < 2 ^ (prefixWord ++ tailWord_1040224).sum := by decide
  have hdescent : baseEnd_1040224 < baseStart_1040224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040247 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_1040247 : Nat := 118140960795 + 1040247 * 2 ^ 59
def prefixEnd_1040247 : Nat := 4983230072969 + 3 ^ 40 * 1040247 * 2
def baseEnd_1040247 : Nat := 534146710397696762528497

theorem tailTrace_1040247 : CollatzResearch.WordTrace tailWord_1040247 prefixEnd_1040247 534146710397696762528497 := by
  unfold tailWord_1040247
  simp only [CollatzResearch.WordTrace]
  refine ⟨37940925062370253888470995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25293950041580169258980663 37940925062370253888470995)
  ·
    refine ⟨56911387593555380832706493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37940925062370253888470995 56911387593555380832706493)
    ·
      refine ⟨21341770347583267812264935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56911387593555380832706493 21341770347583267812264935)
      ·
        refine ⟨32012655521374901718397403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21341770347583267812264935 32012655521374901718397403)
        ·
          refine ⟨48018983282062352577596105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32012655521374901718397403 48018983282062352577596105)
          ·
            refine ⟨36014237461546764433197079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48018983282062352577596105 36014237461546764433197079)
            ·
              refine ⟨54021356192320146649795619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36014237461546764433197079 54021356192320146649795619)
              ·
                refine ⟨81032034288480219974693429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54021356192320146649795619 81032034288480219974693429)
                ·
                  refine ⟨7596753214545020622627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81032034288480219974693429 7596753214545020622627509)
                  ·
                    refine ⟨712195613863595683371329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7596753214545020622627509 712195613863595683371329)
                    ·
                      refine ⟨534146710397696762528497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712195613863595683371329 534146710397696762528497)
                      ·
                        rfl

theorem cell23_1040247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_1040247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040247 prefixEnd_1040247 := by exact prefixLift 1040247
  have htrace : WordTrace (prefixWord ++ tailWord_1040247) baseStart_1040247 baseEnd_1040247 := by
    simpa [prefixWord, tailWord_1040247, baseEnd_1040247] using wordTrace_append hprefix tailTrace_1040247
  have hstable : (prefixWord ++ tailWord_1040247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040247).length < 2 ^ (prefixWord ++ tailWord_1040247).sum := by decide
  have hdescent : baseEnd_1040247 < baseStart_1040247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040274 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1040274 : Nat := 118140960795 + 1040274 * 2 ^ 59
def prefixEnd_1040274 : Nat := 4983230072969 + 3 ^ 40 * 1040274 * 2
def baseEnd_1040274 : Nat := 178053524791789385630291

theorem tailTrace_1040274 : CollatzResearch.WordTrace tailWord_1040274 prefixEnd_1040274 178053524791789385630291 := by
  unfold tailWord_1040274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485477458318109374925969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25294606555514958333135917 9485477458318109374925969)
  ·
    refine ⟨7114108093738582031194477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9485477458318109374925969 7114108093738582031194477)
    ·
      refine ⟨2667790535151968261697929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7114108093738582031194477 2667790535151968261697929)
      ·
        refine ⟨2000842901363976196273447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2667790535151968261697929 2000842901363976196273447)
        ·
          refine ⟨3001264352045964294410171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000842901363976196273447 3001264352045964294410171)
          ·
            refine ⟨4501896528068946441615257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001264352045964294410171 4501896528068946441615257)
            ·
              refine ⟨3376422396051709831211443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501896528068946441615257 3376422396051709831211443)
              ·
                refine ⟨5064633594077564746817165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376422396051709831211443 5064633594077564746817165)
                ·
                  refine ⟨1899237597779086780056437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5064633594077564746817165 1899237597779086780056437)
                  ·
                    refine ⟨178053524791789385630291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1899237597779086780056437 178053524791789385630291)
                    ·
                      rfl

theorem cell23_1040274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1040274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040274 prefixEnd_1040274 := by exact prefixLift 1040274
  have htrace : WordTrace (prefixWord ++ tailWord_1040274) baseStart_1040274 baseEnd_1040274 := by
    simpa [prefixWord, tailWord_1040274, baseEnd_1040274] using wordTrace_append hprefix tailTrace_1040274
  have hstable : (prefixWord ++ tailWord_1040274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040274).length < 2 ^ (prefixWord ++ tailWord_1040274).sum := by decide
  have hdescent : baseEnd_1040274 < baseStart_1040274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040277 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1040277 : Nat := 118140960795 + 1040277 * 2 ^ 59
def prefixEnd_1040277 : Nat := 4983230072969 + 3 ^ 40 * 1040277 * 2
def baseEnd_1040277 : Nat := 534162114817331645153359

theorem tailTrace_1040277 : CollatzResearch.WordTrace tailWord_1040277 prefixEnd_1040277 534162114817331645153359 := by
  unfold tailWord_1040277
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942019252261569012063085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25294679501507712674708723 37942019252261569012063085)
  ·
    refine ⟨14228257219598088379523657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37942019252261569012063085 14228257219598088379523657)
    ·
      refine ⟨10671192914698566284642743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14228257219598088379523657 10671192914698566284642743)
      ·
        refine ⟨16006789372047849426964115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671192914698566284642743 16006789372047849426964115)
        ·
          refine ⟨24010184058071774140446173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16006789372047849426964115 24010184058071774140446173)
          ·
            refine ⟨9003819021776915302667315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24010184058071774140446173 9003819021776915302667315)
            ·
              refine ⟨13505728532665372954000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9003819021776915302667315 13505728532665372954000973)
              ·
                refine ⟨5064648199749514857750365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13505728532665372954000973 5064648199749514857750365)
                ·
                  refine ⟨1899243074906068071656387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5064648199749514857750365 1899243074906068071656387)
                  ·
                    refine ⟨2848864612359102107484581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899243074906068071656387 2848864612359102107484581)
                    ·
                      refine ⟨534162114817331645153359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2848864612359102107484581 534162114817331645153359)
                      ·
                        rfl

theorem cell23_1040277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1040277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040277 prefixEnd_1040277 := by exact prefixLift 1040277
  have htrace : WordTrace (prefixWord ++ tailWord_1040277) baseStart_1040277 baseEnd_1040277 := by
    simpa [prefixWord, tailWord_1040277, baseEnd_1040277] using wordTrace_append hprefix tailTrace_1040277
  have hstable : (prefixWord ++ tailWord_1040277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040277).length < 2 ^ (prefixWord ++ tailWord_1040277).sum := by decide
  have hdescent : baseEnd_1040277 < baseStart_1040277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040297 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_1040297 : Nat := 118140960795 + 1040297 * 2 ^ 59
def prefixEnd_1040297 : Nat := 4983230072969 + 3 ^ 40 * 1040297 * 2
def baseEnd_1040297 : Nat := 534172384430421566903267

theorem tailTrace_1040297 : CollatzResearch.WordTrace tailWord_1040297 prefixEnd_1040297 534172384430421566903267 := by
  unfold tailWord_1040297
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942748712189112427791145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25295165808126074951860763 37942748712189112427791145)
  ·
    refine ⟨28457061534141834320843359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37942748712189112427791145 28457061534141834320843359)
    ·
      refine ⟨42685592301212751481265039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28457061534141834320843359 42685592301212751481265039)
      ·
        refine ⟨64028388451819127221897559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42685592301212751481265039 64028388451819127221897559)
        ·
          refine ⟨96042582677728690832846339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64028388451819127221897559 96042582677728690832846339)
          ·
            refine ⟨144063874016593036249269509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96042582677728690832846339 144063874016593036249269509)
            ·
              refine ⟨27011976378111194296738033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144063874016593036249269509 27011976378111194296738033)
              ·
                refine ⟨20258982283583395722553525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27011976378111194296738033 20258982283583395722553525)
                ·
                  refine ⟨1899279589085943348989393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20258982283583395722553525 1899279589085943348989393)
                  ·
                    refine ⟨1424459691814457511742045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899279589085943348989393 1424459691814457511742045)
                    ·
                      refine ⟨534172384430421566903267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424459691814457511742045 534172384430421566903267)
                      ·
                        rfl

theorem cell23_1040297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_1040297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040297 prefixEnd_1040297 := by exact prefixLift 1040297
  have htrace : WordTrace (prefixWord ++ tailWord_1040297) baseStart_1040297 baseEnd_1040297 := by
    simpa [prefixWord, tailWord_1040297, baseEnd_1040297] using wordTrace_append hprefix tailTrace_1040297
  have hstable : (prefixWord ++ tailWord_1040297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040297).length < 2 ^ (prefixWord ++ tailWord_1040297).sum := by decide
  have hdescent : baseEnd_1040297 < baseStart_1040297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040344 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1040344 : Nat := 118140960795 + 1040344 * 2 ^ 59
def prefixEnd_1040344 : Nat := 4983230072969 + 3 ^ 40 * 1040344 * 2
def baseEnd_1040344 : Nat := 534196518021182883015551

theorem tailTrace_1040344 : CollatzResearch.WordTrace tailWord_1040344 prefixEnd_1040344 534196518021182883015551 := by
  unfold tailWord_1040344
  simp only [CollatzResearch.WordTrace]
  refine ⟨18972231471509419727376043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25296308628679226303168057 18972231471509419727376043)
  ·
    refine ⟨28458347207264129591064065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18972231471509419727376043 28458347207264129591064065)
    ·
      refine ⟨21343760405448097193298049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28458347207264129591064065 21343760405448097193298049)
      ·
        refine ⟨16007820304086072894973537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21343760405448097193298049 16007820304086072894973537)
        ·
          refine ⟨12005865228064554671230153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16007820304086072894973537 12005865228064554671230153)
          ·
            refine ⟨9004398921048416003422615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12005865228064554671230153 9004398921048416003422615)
            ·
              refine ⟨13506598381572624005133923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004398921048416003422615 13506598381572624005133923)
              ·
                refine ⟨20259897572358936007700885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506598381572624005133923 20259897572358936007700885)
                ·
                  refine ⟨949682698704325125360979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20259897572358936007700885 949682698704325125360979)
                  ·
                    refine ⟨1424524048056487688041469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949682698704325125360979 1424524048056487688041469)
                    ·
                      refine ⟨534196518021182883015551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424524048056487688041469 534196518021182883015551)
                      ·
                        rfl

theorem cell23_1040344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1040344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040344 prefixEnd_1040344 := by exact prefixLift 1040344
  have htrace : WordTrace (prefixWord ++ tailWord_1040344) baseStart_1040344 baseEnd_1040344 := by
    simpa [prefixWord, tailWord_1040344, baseEnd_1040344] using wordTrace_append hprefix tailTrace_1040344
  have hstable : (prefixWord ++ tailWord_1040344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040344).length < 2 ^ (prefixWord ++ tailWord_1040344).sum := by decide
  have hdescent : baseEnd_1040344 < baseStart_1040344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040367 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_1040367 : Nat := 118140960795 + 1040367 * 2 ^ 59
def prefixEnd_1040367 : Nat := 4983230072969 + 3 ^ 40 * 1040367 * 2
def baseEnd_1040367 : Nat := 534208328076236293027945

theorem tailTrace_1040367 : CollatzResearch.WordTrace tailWord_1040367 prefixEnd_1040367 534208328076236293027945 := by
  unfold tailWord_1040367
  simp only [CollatzResearch.WordTrace]
  refine ⟨37945301821935514382839355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25296867881290342921892903 37945301821935514382839355)
  ·
    refine ⟨56917952732903271574259033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37945301821935514382839355 56917952732903271574259033)
    ·
      refine ⟨42688464549677453680694275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56917952732903271574259033 42688464549677453680694275)
      ·
        refine ⟨64032696824516180521041413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42688464549677453680694275 64032696824516180521041413)
        ·
          refine ⟨12006130654596783847695265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64032696824516180521041413 12006130654596783847695265)
          ·
            refine ⟨9004597990947587885771449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12006130654596783847695265 9004597990947587885771449)
            ·
              refine ⟨6753448493210690914328587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9004597990947587885771449 6753448493210690914328587)
              ·
                refine ⟨10130172739816036371492881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753448493210690914328587 10130172739816036371492881)
                ·
                  refine ⟨7597629554862027278619661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10130172739816036371492881 7597629554862027278619661)
                  ·
                    refine ⟨2849111083073260229482373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7597629554862027278619661 2849111083073260229482373)
                    ·
                      refine ⟨534208328076236293027945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2849111083073260229482373 534208328076236293027945)
                      ·
                        rfl

theorem cell23_1040367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_1040367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040367 prefixEnd_1040367 := by exact prefixLift 1040367
  have htrace : WordTrace (prefixWord ++ tailWord_1040367) baseStart_1040367 baseEnd_1040367 := by
    simpa [prefixWord, tailWord_1040367, baseEnd_1040367] using wordTrace_append hprefix tailTrace_1040367
  have hstable : (prefixWord ++ tailWord_1040367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040367).length < 2 ^ (prefixWord ++ tailWord_1040367).sum := by decide
  have hdescent : baseEnd_1040367 < baseStart_1040367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040405 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_1040405 : Nat := 118140960795 + 1040405 * 2 ^ 59
def prefixEnd_1040405 : Nat := 4983230072969 + 3 ^ 40 * 1040405 * 2
def baseEnd_1040405 : Nat := 534227840341107144352771

theorem tailTrace_1040405 : CollatzResearch.WordTrace tailWord_1040405 prefixEnd_1040405 534227840341107144352771 := by
  unfold tailWord_1040405
  simp only [CollatzResearch.WordTrace]
  refine ⟨37946687795797846872722669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25297791863865231248481779 37946687795797846872722669)
  ·
    refine ⟨14230007923424192577271001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37946687795797846872722669 14230007923424192577271001)
    ·
      refine ⟨10672505942568144432953251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14230007923424192577271001 10672505942568144432953251)
      ·
        refine ⟨16008758913852216649429877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672505942568144432953251 16008758913852216649429877)
        ·
          refine ⟨1500821148173645310884051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16008758913852216649429877 1500821148173645310884051)
          ·
            refine ⟨2251231722260467966326077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500821148173645310884051 2251231722260467966326077)
            ·
              refine ⟨844211895847675487372279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2251231722260467966326077 844211895847675487372279)
              ·
                refine ⟨1266317843771513231058419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844211895847675487372279 1266317843771513231058419)
                ·
                  refine ⟨1899476765657269846587629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266317843771513231058419 1899476765657269846587629)
                  ·
                    refine ⟨712303787121476192470361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899476765657269846587629 712303787121476192470361)
                    ·
                      refine ⟨534227840341107144352771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712303787121476192470361 534227840341107144352771)
                      ·
                        rfl

theorem cell23_1040405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_1040405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040405 prefixEnd_1040405 := by exact prefixLift 1040405
  have htrace : WordTrace (prefixWord ++ tailWord_1040405) baseStart_1040405 baseEnd_1040405 := by
    simpa [prefixWord, tailWord_1040405, baseEnd_1040405] using wordTrace_append hprefix tailTrace_1040405
  have hstable : (prefixWord ++ tailWord_1040405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040405).length < 2 ^ (prefixWord ++ tailWord_1040405).sum := by decide
  have hdescent : baseEnd_1040405 < baseStart_1040405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040434 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1040434 : Nat := 118140960795 + 1040434 * 2 ^ 59
def prefixEnd_1040434 : Nat := 4983230072969 + 3 ^ 40 * 1040434 * 2
def baseEnd_1040434 : Nat := 534242731280087530890137

theorem tailTrace_1040434 : CollatzResearch.WordTrace tailWord_1040434 prefixEnd_1040434 534242731280087530890137 := by
  unfold tailWord_1040434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486936378173196206382089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25298497008461856550352237 9486936378173196206382089)
  ·
    refine ⟨7115202283629897154786567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9486936378173196206382089 7115202283629897154786567)
    ·
      refine ⟨10672803425444845732179851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7115202283629897154786567 10672803425444845732179851)
      ·
        refine ⟨16009205138167268598269777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672803425444845732179851 16009205138167268598269777)
        ·
          refine ⟨12006903853625451448702333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16009205138167268598269777 12006903853625451448702333)
          ·
            refine ⟨4502588945109544293263375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12006903853625451448702333 4502588945109544293263375)
            ·
              refine ⟨6753883417664316439895063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502588945109544293263375 6753883417664316439895063)
              ·
                refine ⟨10130825126496474659842595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6753883417664316439895063 10130825126496474659842595)
                ·
                  refine ⟨15196237689744711989763893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130825126496474659842595 15196237689744711989763893)
                  ·
                    refine ⟨1424647283413566749040365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15196237689744711989763893 1424647283413566749040365)
                    ·
                      refine ⟨534242731280087530890137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424647283413566749040365 534242731280087530890137)
                      ·
                        rfl

theorem cell23_1040434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1040434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040434 prefixEnd_1040434 := by exact prefixLift 1040434
  have htrace : WordTrace (prefixWord ++ tailWord_1040434) baseStart_1040434 baseEnd_1040434 := by
    simpa [prefixWord, tailWord_1040434, baseEnd_1040434] using wordTrace_append hprefix tailTrace_1040434
  have hstable : (prefixWord ++ tailWord_1040434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040434).length < 2 ^ (prefixWord ++ tailWord_1040434).sum := by decide
  have hdescent : baseEnd_1040434 < baseStart_1040434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040447 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1040447 : Nat := 118140960795 + 1040447 * 2 ^ 59
def prefixEnd_1040447 : Nat := 4983230072969 + 3 ^ 40 * 1040447 * 2
def baseEnd_1040447 : Nat := 534249406528595980027577

theorem tailTrace_1040447 : CollatzResearch.WordTrace tailWord_1040447 prefixEnd_1040447 534249406528595980027577 := by
  unfold tailWord_1040447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948219661645688045751595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25298813107763792030501063 37948219661645688045751595)
  ·
    refine ⟨56922329492468532068627393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37948219661645688045751595 56922329492468532068627393)
    ·
      refine ⟨42691747119351399051470545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56922329492468532068627393 42691747119351399051470545)
      ·
        refine ⟨32018810339513549288602909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42691747119351399051470545 32018810339513549288602909)
        ·
          refine ⟨12007053877317580983226091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32018810339513549288602909 12007053877317580983226091)
          ·
            refine ⟨18010580815976371474839137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007053877317580983226091 18010580815976371474839137)
            ·
              refine ⟨13507935611982278606129353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18010580815976371474839137 13507935611982278606129353)
              ·
                refine ⟨10130951708986708954597015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13507935611982278606129353 10130951708986708954597015)
                ·
                  refine ⟨15196427563480063431895523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10130951708986708954597015 15196427563480063431895523)
                  ·
                    refine ⟨22794641345220095147843285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15196427563480063431895523 22794641345220095147843285)
                    ·
                      refine ⟨534249406528595980027577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22794641345220095147843285 534249406528595980027577)
                      ·
                        rfl

theorem cell23_1040447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1040447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040447 prefixEnd_1040447 := by exact prefixLift 1040447
  have htrace : WordTrace (prefixWord ++ tailWord_1040447) baseStart_1040447 baseEnd_1040447 := by
    simpa [prefixWord, tailWord_1040447, baseEnd_1040447] using wordTrace_append hprefix tailTrace_1040447
  have hstable : (prefixWord ++ tailWord_1040447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040447).length < 2 ^ (prefixWord ++ tailWord_1040447).sum := by decide
  have hdescent : baseEnd_1040447 < baseStart_1040447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040474 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1040474 : Nat := 118140960795 + 1040474 * 2 ^ 59
def prefixEnd_1040474 : Nat := 4983230072969 + 3 ^ 40 * 1040474 * 2
def baseEnd_1040474 : Nat := 534263270506267374389953

theorem tailTrace_1040474 : CollatzResearch.WordTrace tailWord_1040474 prefixEnd_1040474 534263270506267374389953 := by
  unfold tailWord_1040474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9487301108136967914246119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25299469621698581104656317 9487301108136967914246119)
  ·
    refine ⟨14230951662205451871369179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9487301108136967914246119 14230951662205451871369179)
    ·
      refine ⟨21346427493308177807053769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14230951662205451871369179 21346427493308177807053769)
      ·
        refine ⟨16009820619981133355290327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21346427493308177807053769 16009820619981133355290327)
        ·
          refine ⟨24014730929971700032935491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16009820619981133355290327 24014730929971700032935491)
          ·
            refine ⟨36022096394957550049403237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24014730929971700032935491 36022096394957550049403237)
            ·
              refine ⟨6754143074054540634263107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36022096394957550049403237 6754143074054540634263107)
              ·
                refine ⟨10131214611081810951394661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754143074054540634263107 10131214611081810951394661)
                ·
                  refine ⟨1899602739577839553386499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10131214611081810951394661 1899602739577839553386499)
                  ·
                    refine ⟨2849404109366759330079749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899602739577839553386499 2849404109366759330079749)
                    ·
                      refine ⟨534263270506267374389953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2849404109366759330079749 534263270506267374389953)
                      ·
                        rfl

theorem cell23_1040474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1040474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040474 prefixEnd_1040474 := by exact prefixLift 1040474
  have htrace : WordTrace (prefixWord ++ tailWord_1040474) baseStart_1040474 baseEnd_1040474 := by
    simpa [prefixWord, tailWord_1040474, baseEnd_1040474] using wordTrace_append hprefix tailTrace_1040474
  have hstable : (prefixWord ++ tailWord_1040474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040474).length < 2 ^ (prefixWord ++ tailWord_1040474).sum := by decide
  have hdescent : baseEnd_1040474 < baseStart_1040474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040507 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_1040507 : Nat := 118140960795 + 1040507 * 2 ^ 59
def prefixEnd_1040507 : Nat := 4983230072969 + 3 ^ 40 * 1040507 * 2
def baseEnd_1040507 : Nat := 534280215367865745277301

theorem tailTrace_1040507 : CollatzResearch.WordTrace tailWord_1040507 prefixEnd_1040507 534280215367865745277301 := by
  unfold tailWord_1040507
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950408041428318292935775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300272027618878861957183 37950408041428318292935775)
  ·
    refine ⟨56925612062142477439403663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37950408041428318292935775 56925612062142477439403663)
    ·
      refine ⟨85388418093213716159105495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56925612062142477439403663 85388418093213716159105495)
      ·
        refine ⟨128082627139820574238658243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85388418093213716159105495 128082627139820574238658243)
        ·
          refine ⟨192123940709730861357987365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128082627139820574238658243 192123940709730861357987365)
          ·
            refine ⟨36023238883074536504622631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192123940709730861357987365 36023238883074536504622631)
            ·
              refine ⟨54034858324611804756933947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36023238883074536504622631 54034858324611804756933947)
              ·
                refine ⟨81052287486917707135400921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54034858324611804756933947 81052287486917707135400921)
                ·
                  refine ⟨60789215615188280351550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81052287486917707135400921 60789215615188280351550691)
                  ·
                    refine ⟨91183823422782420527326037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60789215615188280351550691 91183823422782420527326037)
                    ·
                      refine ⟨534280215367865745277301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 91183823422782420527326037 534280215367865745277301)
                      ·
                        rfl

theorem cell23_1040507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_1040507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040507 prefixEnd_1040507 := by exact prefixLift 1040507
  have htrace : WordTrace (prefixWord ++ tailWord_1040507) baseStart_1040507 baseEnd_1040507 := by
    simpa [prefixWord, tailWord_1040507, baseEnd_1040507] using wordTrace_append hprefix tailTrace_1040507
  have hstable : (prefixWord ++ tailWord_1040507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040507).length < 2 ^ (prefixWord ++ tailWord_1040507).sum := by decide
  have hdescent : baseEnd_1040507 < baseStart_1040507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040535 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 3, 4]
def baseStart_1040535 : Nat := 118140960795 + 1040535 * 2 ^ 59
def prefixEnd_1040535 : Nat := 4983230072969 + 3 ^ 40 * 1040535 * 2
def baseEnd_1040535 : Nat := 178098197608730545242391

theorem tailTrace_1040535 : CollatzResearch.WordTrace tailWord_1040535 prefixEnd_1040535 178098197608730545242391 := by
  unfold tailWord_1040535
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951429285326879074955059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300952856884586049970039 37951429285326879074955059)
  ·
    refine ⟨56927143927990318612432589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37951429285326879074955059 56927143927990318612432589)
    ·
      refine ⟨21347678972996369479662221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56927143927990318612432589 21347678972996369479662221)
      ·
        refine ⟨8005379614873638554873333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21347678972996369479662221 8005379614873638554873333)
        ·
          refine ⟨750504338894403614519375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8005379614873638554873333 750504338894403614519375)
          ·
            refine ⟨1125756508341605421779063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750504338894403614519375 1125756508341605421779063)
            ·
              refine ⟨1688634762512408132668595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125756508341605421779063 1688634762512408132668595)
              ·
                refine ⟨2532952143768612199002893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688634762512408132668595 2532952143768612199002893)
                ·
                  refine ⟨949857053913229574626085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2532952143768612199002893 949857053913229574626085)
                  ·
                    refine ⟨178098197608730545242391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 949857053913229574626085 178098197608730545242391)
                    ·
                      rfl

theorem cell23_1040535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_1040535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040535 prefixEnd_1040535 := by exact prefixLift 1040535
  have htrace : WordTrace (prefixWord ++ tailWord_1040535) baseStart_1040535 baseEnd_1040535 := by
    simpa [prefixWord, tailWord_1040535, baseEnd_1040535] using wordTrace_append hprefix tailTrace_1040535
  have hstable : (prefixWord ++ tailWord_1040535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040535).length < 2 ^ (prefixWord ++ tailWord_1040535).sum := by decide
  have hdescent : baseEnd_1040535 < baseStart_1040535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040568 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_1040568 : Nat := 118140960795 + 1040568 * 2 ^ 59
def prefixEnd_1040568 : Nat := 4983230072969 + 3 ^ 40 * 1040568 * 2
def baseEnd_1040568 : Nat := 534311537687790006614521

theorem tailTrace_1040568 : CollatzResearch.WordTrace tailWord_1040568 prefixEnd_1040568 534311537687790006614521 := by
  unfold tailWord_1040568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18976316447103662855453179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25301755262804883807270905 18976316447103662855453179)
  ·
    refine ⟨28464474670655494283179769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18976316447103662855453179 28464474670655494283179769)
    ·
      refine ⟨21348356002991620712384827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28464474670655494283179769 21348356002991620712384827)
      ·
        refine ⟨32022534004487431068577241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21348356002991620712384827 32022534004487431068577241)
        ·
          refine ⟨24016900503365573301432931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32022534004487431068577241 24016900503365573301432931)
          ·
            refine ⟨36025350755048359952149397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24016900503365573301432931 36025350755048359952149397)
            ·
              refine ⟨1688688316642891872757003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36025350755048359952149397 1688688316642891872757003)
              ·
                refine ⟨2533032474964337809135505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688688316642891872757003 2533032474964337809135505)
                ·
                  refine ⟨1899774356223253356851629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533032474964337809135505 1899774356223253356851629)
                  ·
                    refine ⟨712415383583720008819361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899774356223253356851629 712415383583720008819361)
                    ·
                      refine ⟨534311537687790006614521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712415383583720008819361 534311537687790006614521)
                      ·
                        rfl

theorem cell23_1040568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_1040568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040568 prefixEnd_1040568 := by exact prefixLift 1040568
  have htrace : WordTrace (prefixWord ++ tailWord_1040568) baseStart_1040568 baseEnd_1040568 := by
    simpa [prefixWord, tailWord_1040568, baseEnd_1040568] using wordTrace_append hprefix tailTrace_1040568
  have hstable : (prefixWord ++ tailWord_1040568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040568).length < 2 ^ (prefixWord ++ tailWord_1040568).sum := by decide
  have hdescent : baseEnd_1040568 < baseStart_1040568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040581 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_1040581 : Nat := 118140960795 + 1040581 * 2 ^ 59
def prefixEnd_1040581 : Nat := 4983230072969 + 3 ^ 40 * 1040581 * 2
def baseEnd_1040581 : Nat := 534318212936298455751961

theorem tailTrace_1040581 : CollatzResearch.WordTrace tailWord_1040581 prefixEnd_1040581 534318212936298455751961 := by
  unfold tailWord_1040581
  simp only [CollatzResearch.WordTrace]
  refine ⟨37953107043160228931129597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25302071362106819287419731 37953107043160228931129597)
  ·
    refine ⟨14232415141185085849173599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37953107043160228931129597 14232415141185085849173599)
    ·
      refine ⟨21348622711777628773760399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14232415141185085849173599 21348622711777628773760399)
      ·
        refine ⟨32022934067666443160640599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21348622711777628773760399 32022934067666443160640599)
        ·
          refine ⟨48034401101499664740960899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32022934067666443160640599 48034401101499664740960899)
          ·
            refine ⟨72051601652249497111441349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48034401101499664740960899 72051601652249497111441349)
            ·
              refine ⟨13509675309796780708395253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72051601652249497111441349 13509675309796780708395253)
              ·
                refine ⟨1266532060293448191412055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13509675309796780708395253 1266532060293448191412055)
                ·
                  refine ⟨1899798090440172287118083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266532060293448191412055 1899798090440172287118083)
                  ·
                    refine ⟨2849697135660258430677125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1899798090440172287118083 2849697135660258430677125)
                    ·
                      refine ⟨534318212936298455751961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2849697135660258430677125 534318212936298455751961)
                      ·
                        rfl

theorem cell23_1040581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_1040581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040581 prefixEnd_1040581 := by exact prefixLift 1040581
  have htrace : WordTrace (prefixWord ++ tailWord_1040581) baseStart_1040581 baseEnd_1040581 := by
    simpa [prefixWord, tailWord_1040581, baseEnd_1040581] using wordTrace_append hprefix tailTrace_1040581
  have hstable : (prefixWord ++ tailWord_1040581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040581).length < 2 ^ (prefixWord ++ tailWord_1040581).sum := by decide
  have hdescent : baseEnd_1040581 < baseStart_1040581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040601 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_1040601 : Nat := 118140960795 + 1040601 * 2 ^ 59
def prefixEnd_1040601 : Nat := 4983230072969 + 3 ^ 40 * 1040601 * 2
def baseEnd_1040601 : Nat := 534328482549388377501869

theorem tailTrace_1040601 : CollatzResearch.WordTrace tailWord_1040601 prefixEnd_1040601 534328482549388377501869 := by
  unfold tailWord_1040601
  simp only [CollatzResearch.WordTrace]
  refine ⟨37953836503087772346857657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25302557668725181564571771 37953836503087772346857657)
  ·
    refine ⟨28465377377315829260143243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37953836503087772346857657 28465377377315829260143243)
    ·
      refine ⟨42698066065973743890214865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28465377377315829260143243 42698066065973743890214865)
      ·
        refine ⟨32023549549480307917661149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42698066065973743890214865 32023549549480307917661149)
        ·
          refine ⟨12008831081055115469122931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32023549549480307917661149 12008831081055115469122931)
          ·
            refine ⟨18013246621582673203684397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12008831081055115469122931 18013246621582673203684397)
            ·
              refine ⟨6754967483093502451381649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18013246621582673203684397 6754967483093502451381649)
              ·
                refine ⟨5066225612320126838536237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754967483093502451381649 5066225612320126838536237)
                ·
                  refine ⟨1899834604620047564451089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5066225612320126838536237 1899834604620047564451089)
                  ·
                    refine ⟨1424875953465035673338317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899834604620047564451089 1424875953465035673338317)
                    ·
                      refine ⟨534328482549388377501869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424875953465035673338317 534328482549388377501869)
                      ·
                        rfl

theorem cell23_1040601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_1040601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040601 prefixEnd_1040601 := by exact prefixLift 1040601
  have htrace : WordTrace (prefixWord ++ tailWord_1040601) baseStart_1040601 baseEnd_1040601 := by
    simpa [prefixWord, tailWord_1040601, baseEnd_1040601] using wordTrace_append hprefix tailTrace_1040601
  have hstable : (prefixWord ++ tailWord_1040601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040601).length < 2 ^ (prefixWord ++ tailWord_1040601).sum := by decide
  have hdescent : baseEnd_1040601 < baseStart_1040601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040615 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1040615 : Nat := 118140960795 + 1040615 * 2 ^ 59
def prefixEnd_1040615 : Nat := 4983230072969 + 3 ^ 40 * 1040615 * 2
def baseEnd_1040615 : Nat := 534335671278551322726805

theorem tailTrace_1040615 : CollatzResearch.WordTrace tailWord_1040615 prefixEnd_1040615 534335671278551322726805 := by
  unfold tailWord_1040615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37954347125037052737867299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25302898083358035158578199 37954347125037052737867299)
  ·
    refine ⟨56931520687555579106800949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37954347125037052737867299 56931520687555579106800949)
    ·
      refine ⟨5337330064458335541262589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56931520687555579106800949 5337330064458335541262589)
      ·
        refine ⟨2001498774171875827973471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5337330064458335541262589 2001498774171875827973471)
        ·
          refine ⟨3002248161257813741960207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001498774171875827973471 3002248161257813741960207)
          ·
            refine ⟨4503372241886720612940311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002248161257813741960207 4503372241886720612940311)
            ·
              refine ⟨6755058362830080919410467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503372241886720612940311 6755058362830080919410467)
              ·
                refine ⟨10132587544245121379115701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755058362830080919410467 10132587544245121379115701)
                ·
                  refine ⟨949930082272980129292097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10132587544245121379115701 949930082272980129292097)
                  ·
                    refine ⟨712447561704735096969073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 949930082272980129292097 712447561704735096969073)
                    ·
                      refine ⟨534335671278551322726805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712447561704735096969073 534335671278551322726805)
                      ·
                        rfl

theorem cell23_1040615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1040615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040615 prefixEnd_1040615 := by exact prefixLift 1040615
  have htrace : WordTrace (prefixWord ++ tailWord_1040615) baseStart_1040615 baseEnd_1040615 := by
    simpa [prefixWord, tailWord_1040615, baseEnd_1040615] using wordTrace_append hprefix tailTrace_1040615
  have hstable : (prefixWord ++ tailWord_1040615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040615).length < 2 ^ (prefixWord ++ tailWord_1040615).sum := by decide
  have hdescent : baseEnd_1040615 < baseStart_1040615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040618 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1040618 : Nat := 118140960795 + 1040618 * 2 ^ 59
def prefixEnd_1040618 : Nat := 4983230072969 + 3 ^ 40 * 1040618 * 2
def baseEnd_1040618 : Nat := 534337211720514810989291

theorem tailTrace_1040618 : CollatzResearch.WordTrace tailWord_1040618 prefixEnd_1040618 534337211720514810989291 := by
  unfold tailWord_1040618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488614136006546062556627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25302971029350789500151005 9488614136006546062556627)
  ·
    refine ⟨14232921204009819093834941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488614136006546062556627 14232921204009819093834941)
    ·
      refine ⟨5337345451503682160188103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14232921204009819093834941 5337345451503682160188103)
      ·
        refine ⟨8006018177255523240282155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337345451503682160188103 8006018177255523240282155)
        ·
          refine ⟨12009027265883284860423233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006018177255523240282155 12009027265883284860423233)
          ·
            refine ⟨9006770449412463645317425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009027265883284860423233 9006770449412463645317425)
            ·
              refine ⟨6755077837059347733988069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9006770449412463645317425 6755077837059347733988069)
              ·
                refine ⟨1266577094448627700122763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6755077837059347733988069 1266577094448627700122763)
                ·
                  refine ⟨1899865641672941550184145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266577094448627700122763 1899865641672941550184145)
                  ·
                    refine ⟨1424899231254706162638109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1899865641672941550184145 1424899231254706162638109)
                    ·
                      refine ⟨534337211720514810989291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1424899231254706162638109 534337211720514810989291)
                      ·
                        rfl

theorem cell23_1040618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1040618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040618 prefixEnd_1040618 := by exact prefixLift 1040618
  have htrace : WordTrace (prefixWord ++ tailWord_1040618) baseStart_1040618 baseEnd_1040618 := by
    simpa [prefixWord, tailWord_1040618, baseEnd_1040618] using wordTrace_append hprefix tailTrace_1040618
  have hstable : (prefixWord ++ tailWord_1040618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040618).length < 2 ^ (prefixWord ++ tailWord_1040618).sum := by decide
  have hdescent : baseEnd_1040618 < baseStart_1040618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040642 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1040642 : Nat := 118140960795 + 1040642 * 2 ^ 59
def prefixEnd_1040642 : Nat := 4983230072969 + 3 ^ 40 * 1040642 * 2
def baseEnd_1040642 : Nat := 178116511752074239029727

theorem tailTrace_1040642 : CollatzResearch.WordTrace tailWord_1040642 prefixEnd_1040642 178116511752074239029727 := by
  unfold tailWord_1040642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488832973984809087275045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25303554597292824232733453 9488832973984809087275045)
  ·
    refine ⟨1779156182622151703864071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9488832973984809087275045 1779156182622151703864071)
    ·
      refine ⟨2668734273933227555796107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779156182622151703864071 2668734273933227555796107)
      ·
        refine ⟨4003101410899841333694161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668734273933227555796107 4003101410899841333694161)
        ·
          refine ⟨3002326058174881000270621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4003101410899841333694161 3002326058174881000270621)
          ·
            refine ⟨1125872271815580375101483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3002326058174881000270621 1125872271815580375101483)
            ·
              refine ⟨1688808407723370562652225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125872271815580375101483 1688808407723370562652225)
              ·
                refine ⟨1266606305792527921989169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688808407723370562652225 1266606305792527921989169)
                ·
                  refine ⟨949954729344395941491877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266606305792527921989169 949954729344395941491877)
                  ·
                    refine ⟨178116511752074239029727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 949954729344395941491877 178116511752074239029727)
                    ·
                      rfl

theorem cell23_1040642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1040642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040642 prefixEnd_1040642 := by exact prefixLift 1040642
  have htrace : WordTrace (prefixWord ++ tailWord_1040642) baseStart_1040642 baseEnd_1040642 := by
    simpa [prefixWord, tailWord_1040642, baseEnd_1040642] using wordTrace_append hprefix tailTrace_1040642
  have hstable : (prefixWord ++ tailWord_1040642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040642).length < 2 ^ (prefixWord ++ tailWord_1040642).sum := by decide
  have hdescent : baseEnd_1040642 < baseStart_1040642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040675 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 1, 3, 2]
def baseStart_1040675 : Nat := 118140960795 + 1040675 * 2 ^ 59
def prefixEnd_1040675 : Nat := 4983230072969 + 3 ^ 40 * 1040675 * 2
def baseEnd_1040675 : Nat := 534366480117821087976529

theorem tailTrace_1040675 : CollatzResearch.WordTrace tailWord_1040675 prefixEnd_1040675 534366480117821087976529 := by
  unfold tailWord_1040675
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956535504819682985051479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25304357003213121990034319 37956535504819682985051479)
  ·
    refine ⟨56934803257229524477577219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37956535504819682985051479 56934803257229524477577219)
    ·
      refine ⟨85402204885844286716365829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56934803257229524477577219 85402204885844286716365829)
      ·
        refine ⟨16012913416095803759318593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85402204885844286716365829 16012913416095803759318593)
        ·
          refine ⟨12009685062071852819488945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16012913416095803759318593 12009685062071852819488945)
          ·
            refine ⟨9007263796553889614616709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009685062071852819488945 9007263796553889614616709)
            ·
              refine ⟨1688861961853854302740633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9007263796553889614616709 1688861961853854302740633)
              ·
                refine ⟨1266646471390390727055475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688861961853854302740633 1266646471390390727055475)
                ·
                  refine ⟨1899969707085586090583213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266646471390390727055475 1899969707085586090583213)
                  ·
                    refine ⟨712488640157094783968705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1899969707085586090583213 712488640157094783968705)
                    ·
                      refine ⟨534366480117821087976529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712488640157094783968705 534366480117821087976529)
                      ·
                        rfl

theorem cell23_1040675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_1040675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040675 prefixEnd_1040675 := by exact prefixLift 1040675
  have htrace : WordTrace (prefixWord ++ tailWord_1040675) baseStart_1040675 baseEnd_1040675 := by
    simpa [prefixWord, tailWord_1040675, baseEnd_1040675] using wordTrace_append hprefix tailTrace_1040675
  have hstable : (prefixWord ++ tailWord_1040675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040675).length < 2 ^ (prefixWord ++ tailWord_1040675).sum := by decide
  have hdescent : baseEnd_1040675 < baseStart_1040675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040691 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_1040691 : Nat := 118140960795 + 1040691 * 2 ^ 59
def prefixEnd_1040691 : Nat := 4983230072969 + 3 ^ 40 * 1040691 * 2
def baseEnd_1040691 : Nat := 534374695808293025376455

theorem tailTrace_1040691 : CollatzResearch.WordTrace tailWord_1040691 prefixEnd_1040691 534374695808293025376455 := by
  unfold tailWord_1040691
  simp only [CollatzResearch.WordTrace]
  refine ⟨37957119072761717717633927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25304746048507811811755951 37957119072761717717633927)
  ·
    refine ⟨56935678609142576576450891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37957119072761717717633927 56935678609142576576450891)
    ·
      refine ⟨85403517913713864864676337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56935678609142576576450891 85403517913713864864676337)
      ·
        refine ⟨64052638435285398648507253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85403517913713864864676337 64052638435285398648507253)
        ·
          refine ⟨6004934853308006123297555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64052638435285398648507253 6004934853308006123297555)
          ·
            refine ⟨9007402279962009184946333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004934853308006123297555 9007402279962009184946333)
            ·
              refine ⟨3377775854985753444354875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9007402279962009184946333 3377775854985753444354875)
              ·
                refine ⟨5066663782478630166532313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377775854985753444354875 5066663782478630166532313)
                ·
                  refine ⟨3799997836858972624899235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5066663782478630166532313 3799997836858972624899235)
                  ·
                    refine ⟨5699996755288458937348853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799997836858972624899235 5699996755288458937348853)
                    ·
                      refine ⟨534374695808293025376455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5699996755288458937348853 534374695808293025376455)
                      ·
                        rfl

theorem cell23_1040691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_1040691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040691 prefixEnd_1040691 := by exact prefixLift 1040691
  have htrace : WordTrace (prefixWord ++ tailWord_1040691) baseStart_1040691 baseEnd_1040691 := by
    simpa [prefixWord, tailWord_1040691, baseEnd_1040691] using wordTrace_append hprefix tailTrace_1040691
  have hstable : (prefixWord ++ tailWord_1040691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040691).length < 2 ^ (prefixWord ++ tailWord_1040691).sum := by decide
  have hdescent : baseEnd_1040691 < baseStart_1040691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040692 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1040692 : Nat := 118140960795 + 1040692 * 2 ^ 59
def prefixEnd_1040692 : Nat := 4983230072969 + 3 ^ 40 * 1040692 * 2
def baseEnd_1040692 : Nat := 534375209288947521463951

theorem tailTrace_1040692 : CollatzResearch.WordTrace tailWord_1040692 prefixEnd_1040692 534375209288947521463951 := by
  unfold tailWord_1040692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978577772879047444210165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25304770363838729925613553 18978577772879047444210165)
  ·
    refine ⟨1779241666207410697894703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18978577772879047444210165 1779241666207410697894703)
    ·
      refine ⟨2668862499311116046842055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779241666207410697894703 2668862499311116046842055)
      ·
        refine ⟨4003293748966674070263083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668862499311116046842055 4003293748966674070263083)
        ·
          refine ⟨6004940623450011105394625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003293748966674070263083 6004940623450011105394625)
          ·
            refine ⟨4503705467587508329045969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6004940623450011105394625 4503705467587508329045969)
            ·
              refine ⟨3377779100690631246784477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4503705467587508329045969 3377779100690631246784477)
              ·
                refine ⟨1266667162758986717544179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3377779100690631246784477 1266667162758986717544179)
                ·
                  refine ⟨1900000744138480076316269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266667162758986717544179 1900000744138480076316269)
                  ·
                    refine ⟨712500279051930028618601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900000744138480076316269 712500279051930028618601)
                    ·
                      refine ⟨534375209288947521463951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712500279051930028618601 534375209288947521463951)
                      ·
                        rfl

theorem cell23_1040692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1040692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040692 prefixEnd_1040692 := by exact prefixLift 1040692
  have htrace : WordTrace (prefixWord ++ tailWord_1040692) baseStart_1040692 baseEnd_1040692 := by
    simpa [prefixWord, tailWord_1040692, baseEnd_1040692] using wordTrace_append hprefix tailTrace_1040692
  have hstable : (prefixWord ++ tailWord_1040692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040692).length < 2 ^ (prefixWord ++ tailWord_1040692).sum := by decide
  have hdescent : baseEnd_1040692 < baseStart_1040692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040761 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1040761 : Nat := 118140960795 + 1040761 * 2 ^ 59
def prefixEnd_1040761 : Nat := 4983230072969 + 3 ^ 40 * 1040761 * 2
def baseEnd_1040761 : Nat := 534410639454107751501133

theorem tailTrace_1040761 : CollatzResearch.WordTrace tailWord_1040761 prefixEnd_1040761 534410639454107751501133 := by
  unfold tailWord_1040761
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959672182508119672682137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25306448121672079781788091 37959672182508119672682137)
  ·
    refine ⟨28469754136881089754511603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37959672182508119672682137 28469754136881089754511603)
    ·
      refine ⟨42704631205321634631767405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28469754136881089754511603 42704631205321634631767405)
      ·
        refine ⟨16014236701995612986912777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42704631205321634631767405 16014236701995612986912777)
        ·
          refine ⟨12010677526496709740184583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16014236701995612986912777 12010677526496709740184583)
          ·
            refine ⟨18016016289745064610276875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010677526496709740184583 18016016289745064610276875)
            ·
              refine ⟨27024024434617596915415313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016016289745064610276875 27024024434617596915415313)
              ·
                refine ⟨20268018325963197686561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27024024434617596915415313 20268018325963197686561485)
                ·
                  refine ⟨7600506872236199132460557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20268018325963197686561485 7600506872236199132460557)
                  ·
                    refine ⟨2850190077088574674672709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7600506872236199132460557 2850190077088574674672709)
                    ·
                      refine ⟨534410639454107751501133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2850190077088574674672709 534410639454107751501133)
                      ·
                        rfl

theorem cell23_1040761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1040761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040761 prefixEnd_1040761 := by exact prefixLift 1040761
  have htrace : WordTrace (prefixWord ++ tailWord_1040761) baseStart_1040761 baseEnd_1040761 := by
    simpa [prefixWord, tailWord_1040761, baseEnd_1040761] using wordTrace_append hprefix tailTrace_1040761
  have hstable : (prefixWord ++ tailWord_1040761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040761).length < 2 ^ (prefixWord ++ tailWord_1040761).sum := by decide
  have hdescent : baseEnd_1040761 < baseStart_1040761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040841 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_1040841 : Nat := 118140960795 + 1040841 * 2 ^ 59
def prefixEnd_1040841 : Nat := 4983230072969 + 3 ^ 40 * 1040841 * 2
def baseEnd_1040841 : Nat := 534451717906467438500765

theorem tailTrace_1040841 : CollatzResearch.WordTrace tailWord_1040841 prefixEnd_1040841 534451717906467438500765 := by
  unfold tailWord_1040841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962590022218293335594377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25308393348145528890396251 37962590022218293335594377)
  ·
    refine ⟨28471942516663720001695783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37962590022218293335594377 28471942516663720001695783)
    ·
      refine ⟨42707913774995580002543675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28471942516663720001695783 42707913774995580002543675)
      ·
        refine ⟨64061870662493370003815513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42707913774995580002543675 64061870662493370003815513)
        ·
          refine ⟨48046402996870027502861635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64061870662493370003815513 48046402996870027502861635)
          ·
            refine ⟨72069604495305041254292453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48046402996870027502861635 72069604495305041254292453)
            ·
              refine ⟨13513050842869695235179835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72069604495305041254292453 13513050842869695235179835)
              ·
                refine ⟨20269576264304542852769753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513050842869695235179835 20269576264304542852769753)
                ·
                  refine ⟨15202182198228407139577315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20269576264304542852769753 15202182198228407139577315)
                  ·
                    refine ⟨22803273297342610709365973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15202182198228407139577315 22803273297342610709365973)
                    ·
                      refine ⟨534451717906467438500765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22803273297342610709365973 534451717906467438500765)
                      ·
                        rfl

theorem cell23_1040841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_1040841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040841 prefixEnd_1040841 := by exact prefixLift 1040841
  have htrace : WordTrace (prefixWord ++ tailWord_1040841) baseStart_1040841 baseEnd_1040841 := by
    simpa [prefixWord, tailWord_1040841, baseEnd_1040841] using wordTrace_append hprefix tailTrace_1040841
  have hstable : (prefixWord ++ tailWord_1040841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040841).length < 2 ^ (prefixWord ++ tailWord_1040841).sum := by decide
  have hdescent : baseEnd_1040841 < baseStart_1040841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040868 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1040868 : Nat := 118140960795 + 1040868 * 2 ^ 59
def prefixEnd_1040868 : Nat := 4983230072969 + 3 ^ 40 * 1040868 * 2
def baseEnd_1040868 : Nat := 534465581884138832863141

theorem tailTrace_1040868 : CollatzResearch.WordTrace tailWord_1040868 prefixEnd_1040868 534465581884138832863141 := by
  unfold tailWord_1040868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18981787396560238473413629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25309049862080317964551505 18981787396560238473413629)
  ·
    refine ⟨7118170273710089427530111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18981787396560238473413629 7118170273710089427530111)
    ·
      refine ⟨10677255410565134141295167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7118170273710089427530111 10677255410565134141295167)
      ·
        refine ⟨16015883115847701211942751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677255410565134141295167 16015883115847701211942751)
        ·
          refine ⟨24023824673771551817914127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16015883115847701211942751 24023824673771551817914127)
          ·
            refine ⟨36035737010657327726871191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24023824673771551817914127 36035737010657327726871191)
            ·
              refine ⟨54053605515985991590306787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36035737010657327726871191 54053605515985991590306787)
              ·
                refine ⟨81080408273978987385460181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54053605515985991590306787 81080408273978987385460181)
                ·
                  refine ⟨1900322068921382516846723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 81080408273978987385460181 1900322068921382516846723)
                  ·
                    refine ⟨2850483103382073775270085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900322068921382516846723 2850483103382073775270085)
                    ·
                      refine ⟨534465581884138832863141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2850483103382073775270085 534465581884138832863141)
                      ·
                        rfl

theorem cell23_1040868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1040868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040868 prefixEnd_1040868 := by exact prefixLift 1040868
  have htrace : WordTrace (prefixWord ++ tailWord_1040868) baseStart_1040868 baseEnd_1040868 := by
    simpa [prefixWord, tailWord_1040868, baseEnd_1040868] using wordTrace_append hprefix tailTrace_1040868
  have hstable : (prefixWord ++ tailWord_1040868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040868).length < 2 ^ (prefixWord ++ tailWord_1040868).sum := by decide
  have hdescent : baseEnd_1040868 < baseStart_1040868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040872 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1040872 : Nat := 118140960795 + 1040872 * 2 ^ 59
def prefixEnd_1040872 : Nat := 4983230072969 + 3 ^ 40 * 1040872 * 2
def baseEnd_1040872 : Nat := 534467635806756817213123

theorem tailTrace_1040872 : CollatzResearch.WordTrace tailWord_1040872 prefixEnd_1040872 534467635806756817213123 := by
  unfold tailWord_1040872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18981860342552992814986435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25309147123403990419981913 18981860342552992814986435)
  ·
    refine ⟨28472790513829489222479653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18981860342552992814986435 28472790513829489222479653)
    ·
      refine ⟨5338648221343029229214935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28472790513829489222479653 5338648221343029229214935)
      ·
        refine ⟨8007972332014543843822403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338648221343029229214935 8007972332014543843822403)
        ·
          refine ⟨12011958498021815765733605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007972332014543843822403 12011958498021815765733605)
          ·
            refine ⟨2252242218379090456075051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12011958498021815765733605 2252242218379090456075051)
            ·
              refine ⟨3378363327568635684112577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252242218379090456075051 3378363327568635684112577)
              ·
                refine ⟨2533772495676476763084433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378363327568635684112577 2533772495676476763084433)
                ·
                  refine ⟨1900329371757357572313325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2533772495676476763084433 1900329371757357572313325)
                  ·
                    refine ⟨712623514409009089617497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1900329371757357572313325 712623514409009089617497)
                    ·
                      refine ⟨534467635806756817213123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712623514409009089617497 534467635806756817213123)
                      ·
                        rfl

theorem cell23_1040872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1040872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040872 prefixEnd_1040872 := by exact prefixLift 1040872
  have htrace : WordTrace (prefixWord ++ tailWord_1040872) baseStart_1040872 baseEnd_1040872 := by
    simpa [prefixWord, tailWord_1040872, baseEnd_1040872] using wordTrace_append hprefix tailTrace_1040872
  have hstable : (prefixWord ++ tailWord_1040872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040872).length < 2 ^ (prefixWord ++ tailWord_1040872).sum := by decide
  have hdescent : baseEnd_1040872 < baseStart_1040872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040888 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1040888 : Nat := 118140960795 + 1040888 * 2 ^ 59
def prefixEnd_1040888 : Nat := 4983230072969 + 3 ^ 40 * 1040888 * 2
def baseEnd_1040888 : Nat := 534475851497228754613049

theorem tailTrace_1040888 : CollatzResearch.WordTrace tailWord_1040888 prefixEnd_1040888 534475851497228754613049 := by
  unfold tailWord_1040888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982152126524010181277659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25309536168698680241703545 18982152126524010181277659)
  ·
    refine ⟨28473228189786015271916489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982152126524010181277659 28473228189786015271916489)
    ·
      refine ⟨21354921142339511453937367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28473228189786015271916489 21354921142339511453937367)
      ·
        refine ⟨32032381713509267180906051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21354921142339511453937367 32032381713509267180906051)
        ·
          refine ⟨48048572570263900771359077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32032381713509267180906051 48048572570263900771359077)
          ·
            refine ⟨9009107356924481394629827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48048572570263900771359077 9009107356924481394629827)
            ·
              refine ⟨13513661035386722091944741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009107356924481394629827 13513661035386722091944741)
              ·
                refine ⟨2533811444135010392239639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13513661035386722091944741 2533811444135010392239639)
                ·
                  refine ⟨3800717166202515588359459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533811444135010392239639 3800717166202515588359459)
                  ·
                    refine ⟨5701075749303773382539189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3800717166202515588359459 5701075749303773382539189)
                    ·
                      refine ⟨534475851497228754613049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5701075749303773382539189 534475851497228754613049)
                      ·
                        rfl

theorem cell23_1040888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1040888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040888 prefixEnd_1040888 := by exact prefixLift 1040888
  have htrace : WordTrace (prefixWord ++ tailWord_1040888) baseStart_1040888 baseEnd_1040888 := by
    simpa [prefixWord, tailWord_1040888, baseEnd_1040888] using wordTrace_append hprefix tailTrace_1040888
  have hstable : (prefixWord ++ tailWord_1040888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040888).length < 2 ^ (prefixWord ++ tailWord_1040888).sum := by decide
  have hdescent : baseEnd_1040888 < baseStart_1040888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040895 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 2, 4]
def baseStart_1040895 : Nat := 118140960795 + 1040895 * 2 ^ 59
def prefixEnd_1040895 : Nat := 4983230072969 + 3 ^ 40 * 1040895 * 2
def baseEnd_1040895 : Nat := 178159815287270075741839

theorem tailTrace_1040895 : CollatzResearch.WordTrace tailWord_1040895 prefixEnd_1040895 178159815287270075741839 := by
  unfold tailWord_1040895
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964559564022660558060139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25309706376015107038706759 37964559564022660558060139)
  ·
    refine ⟨56946839346033990837090209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37964559564022660558060139 56946839346033990837090209)
    ·
      refine ⟨42710129509525493127817657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56946839346033990837090209 42710129509525493127817657)
      ·
        refine ⟨32032597132144119845863243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42710129509525493127817657 32032597132144119845863243)
        ·
          refine ⟨48048895698216179768794865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32032597132144119845863243 48048895698216179768794865)
          ·
            refine ⟨36036671773662134826596149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48048895698216179768794865 36036671773662134826596149)
            ·
              refine ⟨3378437978780825139993389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36036671773662134826596149 3378437978780825139993389)
              ·
                refine ⟨1266914242042809427497521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3378437978780825139993389 1266914242042809427497521)
                ·
                  refine ⟨950185681532107070623141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266914242042809427497521 950185681532107070623141)
                  ·
                    refine ⟨178159815287270075741839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950185681532107070623141 178159815287270075741839)
                    ·
                      rfl

theorem cell23_1040895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_1040895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040895 prefixEnd_1040895 := by exact prefixLift 1040895
  have htrace : WordTrace (prefixWord ++ tailWord_1040895) baseStart_1040895 baseEnd_1040895 := by
    simpa [prefixWord, tailWord_1040895, baseEnd_1040895] using wordTrace_append hprefix tailTrace_1040895
  have hstable : (prefixWord ++ tailWord_1040895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040895).length < 2 ^ (prefixWord ++ tailWord_1040895).sum := by decide
  have hdescent : baseEnd_1040895 < baseStart_1040895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040905 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_1040905 : Nat := 118140960795 + 1040905 * 2 ^ 59
def prefixEnd_1040905 : Nat := 4983230072969 + 3 ^ 40 * 1040905 * 2
def baseEnd_1040905 : Nat := 534484580668355188100471

theorem tailTrace_1040905 : CollatzResearch.WordTrace tailWord_1040905 prefixEnd_1040905 534484580668355188100471 := by
  unfold tailWord_1040905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964924293986432265924169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25309949529324288177282779 37964924293986432265924169)
  ·
    refine ⟨28473693220489824199443127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37964924293986432265924169 28473693220489824199443127)
    ·
      refine ⟨42710539830734736299164691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473693220489824199443127 42710539830734736299164691)
      ·
        refine ⟨64065809746102104448747037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42710539830734736299164691 64065809746102104448747037)
        ·
          refine ⟨24024678654788289168280139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64065809746102104448747037 24024678654788289168280139)
          ·
            refine ⟨36037017982182433752420209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24024678654788289168280139 36037017982182433752420209)
            ·
              refine ⟨27027763486636825314315157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36037017982182433752420209 27027763486636825314315157)
              ·
                refine ⟨1266926413436101186608523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27027763486636825314315157 1266926413436101186608523)
                ·
                  refine ⟨1900389620154151779912785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1266926413436101186608523 1900389620154151779912785)
                  ·
                    refine ⟨1425292215115613834934589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1900389620154151779912785 1425292215115613834934589)
                    ·
                      refine ⟨534484580668355188100471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1425292215115613834934589 534484580668355188100471)
                      ·
                        rfl

theorem cell23_1040905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_1040905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040905 prefixEnd_1040905 := by exact prefixLift 1040905
  have htrace : WordTrace (prefixWord ++ tailWord_1040905) baseStart_1040905 baseEnd_1040905 := by
    simpa [prefixWord, tailWord_1040905, baseEnd_1040905] using wordTrace_append hprefix tailTrace_1040905
  have hstable : (prefixWord ++ tailWord_1040905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040905).length < 2 ^ (prefixWord ++ tailWord_1040905).sum := by decide
  have hdescent : baseEnd_1040905 < baseStart_1040905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040908 : List Nat := [2, 2, 1, 2, 4, 1, 2, 9]
def baseStart_1040908 : Nat := 118140960795 + 1040908 * 2 ^ 59
def prefixEnd_1040908 : Nat := 4983230072969 + 3 ^ 40 * 1040908 * 2
def baseEnd_1040908 : Nat := 19795782263345136161591

theorem tailTrace_1040908 : CollatzResearch.WordTrace tailWord_1040908 prefixEnd_1040908 19795782263345136161591 := by
  unfold tailWord_1040908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982516856487781889141689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25310022475317042518855585 18982516856487781889141689)
  ·
    refine ⟨14236887642365836416856267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18982516856487781889141689 14236887642365836416856267)
    ·
      refine ⟨21355331463548754625284401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14236887642365836416856267 21355331463548754625284401)
      ·
        refine ⟨16016498597661565968963301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21355331463548754625284401 16016498597661565968963301)
        ·
          refine ⟨3003093487061543619180619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16016498597661565968963301 3003093487061543619180619)
          ·
            refine ⟨4504640230592315428770929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003093487061543619180619 4504640230592315428770929)
            ·
              refine ⟨3378480172944236571578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504640230592315428770929 3378480172944236571578197)
              ·
                refine ⟨19795782263345136161591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3378480172944236571578197 19795782263345136161591)
                ·
                  rfl

theorem cell23_1040908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 9].length) (baseStart_1040908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040908 prefixEnd_1040908 := by exact prefixLift 1040908
  have htrace : WordTrace (prefixWord ++ tailWord_1040908) baseStart_1040908 baseEnd_1040908 := by
    simpa [prefixWord, tailWord_1040908, baseEnd_1040908] using wordTrace_append hprefix tailTrace_1040908
  have hstable : (prefixWord ++ tailWord_1040908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040908).length < 2 ^ (prefixWord ++ tailWord_1040908).sum := by decide
  have hdescent : baseEnd_1040908 < baseStart_1040908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040942 : List Nat := [4, 1, 3, 1, 3, 2, 1, 8]
def baseStart_1040942 : Nat := 118140960795 + 1040942 * 2 ^ 59
def prefixEnd_1040942 : Nat := 4983230072969 + 3 ^ 40 * 1040942 * 2
def baseEnd_1040942 : Nat := 19796428868613760864363

theorem tailTrace_1040942 : CollatzResearch.WordTrace tailWord_1040942 prefixEnd_1040942 19796428868613760864363 := by
  unfold tailWord_1040942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745784224356548448127635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25310849196568258390014053 4745784224356548448127635)
  ·
    refine ⟨7118676336534822672191453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4745784224356548448127635 7118676336534822672191453)
    ·
      refine ⟨2669503626200558502071795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7118676336534822672191453 2669503626200558502071795)
      ·
        refine ⟨4004255439300837753107693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669503626200558502071795 4004255439300837753107693)
        ·
          refine ⟨1501595789737814157415385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004255439300837753107693 1501595789737814157415385)
          ·
            refine ⟨1126196842303360618061539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501595789737814157415385 1126196842303360618061539)
            ·
              refine ⟨1689295263455040927092309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126196842303360618061539 1689295263455040927092309)
              ·
                refine ⟨19796428868613760864363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1689295263455040927092309 19796428868613760864363)
                ·
                  rfl

theorem cell23_1040942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_1040942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040942 prefixEnd_1040942 := by exact prefixLift 1040942
  have htrace : WordTrace (prefixWord ++ tailWord_1040942) baseStart_1040942 baseEnd_1040942 := by
    simpa [prefixWord, tailWord_1040942, baseEnd_1040942] using wordTrace_append hprefix tailTrace_1040942
  have hstable : (prefixWord ++ tailWord_1040942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040942).length < 2 ^ (prefixWord ++ tailWord_1040942).sum := by decide
  have hdescent : baseEnd_1040942 < baseStart_1040942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040952 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_1040952 : Nat := 118140960795 + 1040952 * 2 ^ 59
def prefixEnd_1040952 : Nat := 4983230072969 + 3 ^ 40 * 1040952 * 2
def baseEnd_1040952 : Nat := 534508714259116504212755

theorem tailTrace_1040952 : CollatzResearch.WordTrace tailWord_1040952 prefixEnd_1040952 534508714259116504212755 := by
  unfold tailWord_1040952
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983319262408079646442555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25311092349877439528590073 18983319262408079646442555)
  ·
    refine ⟨28474978893612119469663833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18983319262408079646442555 28474978893612119469663833)
    ·
      refine ⟨21356234170209089602247875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28474978893612119469663833 21356234170209089602247875)
      ·
        refine ⟨32034351255313634403371813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21356234170209089602247875 32034351255313634403371813)
        ·
          refine ⟨6006440860371306450632215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32034351255313634403371813 6006440860371306450632215)
          ·
            refine ⟨9009661290556959675948323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006440860371306450632215 9009661290556959675948323)
            ·
              refine ⟨13514491935835439513922485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009661290556959675948323 13514491935835439513922485)
              ·
                refine ⟨1266983618984572454430233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13514491935835439513922485 1266983618984572454430233)
                ·
                  refine ⟨950237714238429340822675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1266983618984572454430233 950237714238429340822675)
                  ·
                    refine ⟨1425356571357644011234013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 950237714238429340822675 1425356571357644011234013)
                    ·
                      refine ⟨534508714259116504212755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1425356571357644011234013 534508714259116504212755)
                      ·
                        rfl

theorem cell23_1040952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_1040952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1040952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1040952 prefixEnd_1040952 := by exact prefixLift 1040952
  have htrace : WordTrace (prefixWord ++ tailWord_1040952) baseStart_1040952 baseEnd_1040952 := by
    simpa [prefixWord, tailWord_1040952, baseEnd_1040952] using wordTrace_append hprefix tailTrace_1040952
  have hstable : (prefixWord ++ tailWord_1040952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040952).length < 2 ^ (prefixWord ++ tailWord_1040952).sum := by decide
  have hdescent : baseEnd_1040952 < baseStart_1040952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041018 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1041018 : Nat := 118140960795 + 1041018 * 2 ^ 59
def prefixEnd_1041018 : Nat := 4983230072969 + 3 ^ 40 * 1041018 * 2
def baseEnd_1041018 : Nat := 534542603982313245987451

theorem tailTrace_1041018 : CollatzResearch.WordTrace tailWord_1041018 prefixEnd_1041018 534542603982313245987451 := by
  unfold tailWord_1041018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492261435644263141196927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25312697161718035043191805 9492261435644263141196927)
  ·
    refine ⟨14238392153466394711795391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9492261435644263141196927 14238392153466394711795391)
    ·
      refine ⟨21357588230199592067693087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14238392153466394711795391 21357588230199592067693087)
      ·
        refine ⟨32036382345299388101539631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21357588230199592067693087 32036382345299388101539631)
        ·
          refine ⟨48054573517949082152309447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32036382345299388101539631 48054573517949082152309447)
          ·
            refine ⟨72081860276923623228464171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48054573517949082152309447 72081860276923623228464171)
            ·
              refine ⟨108122790415385434842696257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72081860276923623228464171 108122790415385434842696257)
              ·
                refine ⟨81092092811539076132022193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108122790415385434842696257 81092092811539076132022193)
                ·
                  refine ⟨60819069608654307099016645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81092092811539076132022193 60819069608654307099016645)
                  ·
                    refine ⟨11403575551622682581065621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60819069608654307099016645 11403575551622682581065621)
                    ·
                      refine ⟨534542603982313245987451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11403575551622682581065621 534542603982313245987451)
                      ·
                        rfl

theorem cell23_1041018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1041018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041018 prefixEnd_1041018 := by exact prefixLift 1041018
  have htrace : WordTrace (prefixWord ++ tailWord_1041018) baseStart_1041018 baseEnd_1041018 := by
    simpa [prefixWord, tailWord_1041018, baseEnd_1041018] using wordTrace_append hprefix tailTrace_1041018
  have hstable : (prefixWord ++ tailWord_1041018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041018).length < 2 ^ (prefixWord ++ tailWord_1041018).sum := by decide
  have hdescent : baseEnd_1041018 < baseStart_1041018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041082 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_1041082 : Nat := 118140960795 + 1041082 * 2 ^ 59
def prefixEnd_1041082 : Nat := 4983230072969 + 3 ^ 40 * 1041082 * 2
def baseEnd_1041082 : Nat := 534575466744200995587157

theorem tailTrace_1041082 : CollatzResearch.WordTrace tailWord_1041082 prefixEnd_1041082 534575466744200995587157 := by
  unfold tailWord_1041082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492845003586297873779375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25314253342896794330078333 9492845003586297873779375)
  ·
    refine ⟨14239267505379446810669063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9492845003586297873779375 14239267505379446810669063)
    ·
      refine ⟨21358901258069170216003595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14239267505379446810669063 21358901258069170216003595)
      ·
        refine ⟨32038351887103755324005393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21358901258069170216003595 32038351887103755324005393)
        ·
          refine ⟨24028763915327816493004045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32038351887103755324005393 24028763915327816493004045)
          ·
            refine ⟨9010786468247931184876517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24028763915327816493004045 9010786468247931184876517)
            ·
              refine ⟨1689522462796487097164347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9010786468247931184876517 1689522462796487097164347)
              ·
                refine ⟨2534283694194730645746521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689522462796487097164347 2534283694194730645746521)
                ·
                  refine ⟨1900712770646047984309891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2534283694194730645746521 1900712770646047984309891)
                  ·
                    refine ⟨2851069155969071976464837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900712770646047984309891 2851069155969071976464837)
                    ·
                      refine ⟨534575466744200995587157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2851069155969071976464837 534575466744200995587157)
                      ·
                        rfl

theorem cell23_1041082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_1041082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041082 prefixEnd_1041082 := by exact prefixLift 1041082
  have htrace : WordTrace (prefixWord ++ tailWord_1041082) baseStart_1041082 baseEnd_1041082 := by
    simpa [prefixWord, tailWord_1041082, baseEnd_1041082] using wordTrace_append hprefix tailTrace_1041082
  have hstable : (prefixWord ++ tailWord_1041082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041082).length < 2 ^ (prefixWord ++ tailWord_1041082).sum := by decide
  have hdescent : baseEnd_1041082 < baseStart_1041082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041116 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1041116 : Nat := 118140960795 + 1041116 * 2 ^ 59
def prefixEnd_1041116 : Nat := 4983230072969 + 3 ^ 40 * 1041116 * 2
def baseEnd_1041116 : Nat := 534592925086453862562001

theorem tailTrace_1041116 : CollatzResearch.WordTrace tailWord_1041116 prefixEnd_1041116 534592925086453862562001 := by
  unfold tailWord_1041116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18986310048111007650927601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25315080064148010201236801 18986310048111007650927601)
  ·
    refine ⟨14239732536083255738195701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18986310048111007650927601 14239732536083255738195701)
    ·
      refine ⟨1334974925257805225455847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14239732536083255738195701 1334974925257805225455847)
      ·
        refine ⟨2002462387886707838183771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334974925257805225455847 2002462387886707838183771)
        ·
          refine ⟨3003693581830061757275657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002462387886707838183771 3003693581830061757275657)
          ·
            refine ⟨2252770186372546317956743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003693581830061757275657 2252770186372546317956743)
            ·
              refine ⟨3379155279558819476935115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252770186372546317956743 3379155279558819476935115)
              ·
                refine ⟨5068732919338229215402673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379155279558819476935115 5068732919338229215402673)
                ·
                  refine ⟨3801549689503671911552005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068732919338229215402673 3801549689503671911552005)
                  ·
                    refine ⟨712790566781938483416001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801549689503671911552005 712790566781938483416001)
                    ·
                      refine ⟨534592925086453862562001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712790566781938483416001 534592925086453862562001)
                      ·
                        rfl

theorem cell23_1041116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1041116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041116 prefixEnd_1041116 := by exact prefixLift 1041116
  have htrace : WordTrace (prefixWord ++ tailWord_1041116) baseStart_1041116 baseEnd_1041116 := by
    simpa [prefixWord, tailWord_1041116, baseEnd_1041116] using wordTrace_append hprefix tailTrace_1041116
  have hstable : (prefixWord ++ tailWord_1041116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041116).length < 2 ^ (prefixWord ++ tailWord_1041116).sum := by decide
  have hdescent : baseEnd_1041116 < baseStart_1041116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041189 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_1041189 : Nat := 118140960795 + 1041189 * 2 ^ 59
def prefixEnd_1041189 : Nat := 4983230072969 + 3 ^ 40 * 1041189 * 2
def baseEnd_1041189 : Nat := 534630409174232076949165

theorem tailTrace_1041189 : CollatzResearch.WordTrace tailWord_1041189 prefixEnd_1041189 534630409174232076949165 := by
  unfold tailWord_1041189
  simp only [CollatzResearch.WordTrace]
  refine ⟨37975282624957548769262621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25316855083305032512841747 37975282624957548769262621)
  ·
    refine ⟨14240730984359080788473483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37975282624957548769262621 14240730984359080788473483)
    ·
      refine ⟨21361096476538621182710225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14240730984359080788473483 21361096476538621182710225)
      ·
        refine ⟨16020822357403965887032669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21361096476538621182710225 16020822357403965887032669)
        ·
          refine ⟨6007808384026487207637251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16020822357403965887032669 6007808384026487207637251)
          ·
            refine ⟨9011712576039730811455877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007808384026487207637251 9011712576039730811455877)
            ·
              refine ⟨1689696108007449527147977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9011712576039730811455877 1689696108007449527147977)
              ·
                refine ⟨1267272081005587145360983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689696108007449527147977 1267272081005587145360983)
                ·
                  refine ⟨1900908121508380718041475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267272081005587145360983 1900908121508380718041475)
                  ·
                    refine ⟨2851362182262571077062213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1900908121508380718041475 2851362182262571077062213)
                    ·
                      refine ⟨534630409174232076949165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2851362182262571077062213 534630409174232076949165)
                      ·
                        rfl

theorem cell23_1041189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_1041189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041189 prefixEnd_1041189 := by exact prefixLift 1041189
  have htrace : WordTrace (prefixWord ++ tailWord_1041189) baseStart_1041189 baseEnd_1041189 := by
    simpa [prefixWord, tailWord_1041189, baseEnd_1041189] using wordTrace_append hprefix tailTrace_1041189
  have hstable : (prefixWord ++ tailWord_1041189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041189).length < 2 ^ (prefixWord ++ tailWord_1041189).sum := by decide
  have hdescent : baseEnd_1041189 < baseStart_1041189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041192 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1041192 : Nat := 118140960795 + 1041192 * 2 ^ 59
def prefixEnd_1041192 : Nat := 4983230072969 + 3 ^ 40 * 1041192 * 2
def baseEnd_1041192 : Nat := 534631949616195565211651

theorem tailTrace_1041192 : CollatzResearch.WordTrace tailWord_1041192 prefixEnd_1041192 534631949616195565211651 := by
  unfold tailWord_1041192
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987696021973340140810915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25316928029297786854414553 18987696021973340140810915)
  ·
    refine ⟨28481544032960010211216373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18987696021973340140810915 28481544032960010211216373)
    ·
      refine ⟨2670144753090000957301535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28481544032960010211216373 2670144753090000957301535)
      ·
        refine ⟨4005217129635001435952303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670144753090000957301535 4005217129635001435952303)
        ·
          refine ⟨6007825694452502153928455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005217129635001435952303 6007825694452502153928455)
          ·
            refine ⟨9011738541678753230892683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007825694452502153928455 9011738541678753230892683)
            ·
              refine ⟨13517607812518129846339025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011738541678753230892683 13517607812518129846339025)
              ·
                refine ⟨10138205859388597384754269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13517607812518129846339025 10138205859388597384754269)
                ·
                  refine ⟨3801827197270724019282851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10138205859388597384754269 3801827197270724019282851)
                  ·
                    refine ⟨5702740795906086028924277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801827197270724019282851 5702740795906086028924277)
                    ·
                      refine ⟨534631949616195565211651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5702740795906086028924277 534631949616195565211651)
                      ·
                        rfl

theorem cell23_1041192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1041192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041192 prefixEnd_1041192 := by exact prefixLift 1041192
  have htrace : WordTrace (prefixWord ++ tailWord_1041192) baseStart_1041192 baseEnd_1041192 := by
    simpa [prefixWord, tailWord_1041192, baseEnd_1041192] using wordTrace_append hprefix tailTrace_1041192
  have hstable : (prefixWord ++ tailWord_1041192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041192).length < 2 ^ (prefixWord ++ tailWord_1041192).sum := by decide
  have hdescent : baseEnd_1041192 < baseStart_1041192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041202 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1041202 : Nat := 118140960795 + 1041202 * 2 ^ 59
def prefixEnd_1041202 : Nat := 4983230072969 + 3 ^ 40 * 1041202 * 2
def baseEnd_1041202 : Nat := 534637084422740526086605

theorem tailTrace_1041202 : CollatzResearch.WordTrace tailWord_1041202 prefixEnd_1041202 534637084422740526086605 := by
  unfold tailWord_1041202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493939193477612997371465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25317171182606967992990573 9493939193477612997371465)
  ·
    refine ⟨7120454395108209748028599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9493939193477612997371465 7120454395108209748028599)
    ·
      refine ⟨10680681592662314622042899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120454395108209748028599 10680681592662314622042899)
      ·
        refine ⟨16021022388993471933064349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680681592662314622042899 16021022388993471933064349)
        ·
          refine ⟨6007883395872551974899131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16021022388993471933064349 6007883395872551974899131)
          ·
            refine ⟨9011825093808827962348697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007883395872551974899131 9011825093808827962348697)
            ·
              refine ⟨6758868820356620971761523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011825093808827962348697 6758868820356620971761523)
              ·
                refine ⟨10138303230534931457642285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758868820356620971761523 10138303230534931457642285)
                ·
                  refine ⟨3801863711450599296615857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10138303230534931457642285 3801863711450599296615857)
                  ·
                    refine ⟨2851397783587949472461893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801863711450599296615857 2851397783587949472461893)
                    ·
                      refine ⟨534637084422740526086605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2851397783587949472461893 534637084422740526086605)
                      ·
                        rfl

theorem cell23_1041202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1041202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041202 prefixEnd_1041202 := by exact prefixLift 1041202
  have htrace : WordTrace (prefixWord ++ tailWord_1041202) baseStart_1041202 baseEnd_1041202 := by
    simpa [prefixWord, tailWord_1041202, baseEnd_1041202] using wordTrace_append hprefix tailTrace_1041202
  have hstable : (prefixWord ++ tailWord_1041202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041202).length < 2 ^ (prefixWord ++ tailWord_1041202).sum := by decide
  have hdescent : baseEnd_1041202 < baseStart_1041202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041217 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1041217 : Nat := 118140960795 + 1041217 * 2 ^ 59
def prefixEnd_1041217 : Nat := 4983230072969 + 3 ^ 40 * 1041217 * 2
def baseEnd_1041217 : Nat := 534644786632557967399037

theorem tailTrace_1041217 : CollatzResearch.WordTrace tailWord_1041217 prefixEnd_1041217 534644786632557967399037 := by
  unfold tailWord_1041217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37976303868856109551281905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25317535912570739700854603 37976303868856109551281905)
  ·
    refine ⟨28482227901642082163461429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37976303868856109551281905 28482227901642082163461429)
    ·
      refine ⟨2670208865778945202824509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28482227901642082163461429 2670208865778945202824509)
      ·
        refine ⟨1001328324667104451059191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2670208865778945202824509 1001328324667104451059191)
        ·
          refine ⟨1501992487000656676588787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001328324667104451059191 1501992487000656676588787)
          ·
            refine ⟨2252988730500985014883181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501992487000656676588787 2252988730500985014883181)
            ·
              refine ⟨844870773937869380581193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2252988730500985014883181 844870773937869380581193)
              ·
                refine ⟨633653080453402035435895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844870773937869380581193 633653080453402035435895)
                ·
                  refine ⟨950479620680103053153843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633653080453402035435895 950479620680103053153843)
                  ·
                    refine ⟨1425719431020154579730765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 950479620680103053153843 1425719431020154579730765)
                    ·
                      refine ⟨534644786632557967399037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1425719431020154579730765 534644786632557967399037)
                      ·
                        rfl

theorem cell23_1041217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1041217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041217 prefixEnd_1041217 := by exact prefixLift 1041217
  have htrace : WordTrace (prefixWord ++ tailWord_1041217) baseStart_1041217 baseEnd_1041217 := by
    simpa [prefixWord, tailWord_1041217, baseEnd_1041217] using wordTrace_append hprefix tailTrace_1041217
  have hstable : (prefixWord ++ tailWord_1041217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041217).length < 2 ^ (prefixWord ++ tailWord_1041217).sum := by decide
  have hdescent : baseEnd_1041217 < baseStart_1041217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041233 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 2, 4]
def baseStart_1041233 : Nat := 118140960795 + 1041233 * 2 ^ 59
def prefixEnd_1041233 : Nat := 4983230072969 + 3 ^ 40 * 1041233 * 2
def baseEnd_1041233 : Nat := 178217667441009968266321

theorem tailTrace_1041233 : CollatzResearch.WordTrace tailWord_1041233 prefixEnd_1041233 178217667441009968266321 := by
  unfold tailWord_1041233
  simp only [CollatzResearch.WordTrace]
  refine ⟨37976887436798144283864353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25317924957865429522576235 37976887436798144283864353)
  ·
    refine ⟨28482665577598608212898265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37976887436798144283864353 28482665577598608212898265)
    ·
      refine ⟨21361999183198956159673699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28482665577598608212898265 21361999183198956159673699)
      ·
        refine ⟨32042998774798434239510549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21361999183198956159673699 32042998774798434239510549)
        ·
          refine ⟨1502015567568676604977057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32042998774798434239510549 1502015567568676604977057)
          ·
            refine ⟨1126511675676507453732793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502015567568676604977057 1126511675676507453732793)
            ·
              refine ⟨844883756757380590299595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126511675676507453732793 844883756757380590299595)
              ·
                refine ⟨1267325635136070885449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844883756757380590299595 1267325635136070885449393)
                ·
                  refine ⟨950494226352053164087045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1267325635136070885449393 950494226352053164087045)
                  ·
                    refine ⟨178217667441009968266321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950494226352053164087045 178217667441009968266321)
                    ·
                      rfl

theorem cell23_1041233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_1041233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041233 prefixEnd_1041233 := by exact prefixLift 1041233
  have htrace : WordTrace (prefixWord ++ tailWord_1041233) baseStart_1041233 baseEnd_1041233 := by
    simpa [prefixWord, tailWord_1041233, baseEnd_1041233] using wordTrace_append hprefix tailTrace_1041233
  have hstable : (prefixWord ++ tailWord_1041233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041233).length < 2 ^ (prefixWord ++ tailWord_1041233).sum := by decide
  have hdescent : baseEnd_1041233 < baseStart_1041233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041266 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1041266 : Nat := 118140960795 + 1041266 * 2 ^ 59
def prefixEnd_1041266 : Nat := 4983230072969 + 3 ^ 40 * 1041266 * 2
def baseEnd_1041266 : Nat := 534669947184628275686311

theorem tailTrace_1041266 : CollatzResearch.WordTrace tailWord_1041266 prefixEnd_1041266 534669947184628275686311 := by
  unfold tailWord_1041266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494522761419647729953913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25318727363785727279877101 9494522761419647729953913)
  ·
    refine ⟨7120892071064735797465435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9494522761419647729953913 7120892071064735797465435)
    ·
      refine ⟨10681338106597103696198153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120892071064735797465435 10681338106597103696198153)
      ·
        refine ⟨8011003579947827772148615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10681338106597103696198153 8011003579947827772148615)
        ·
          refine ⟨12016505369921741658222923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011003579947827772148615 12016505369921741658222923)
          ·
            refine ⟨18024758054882612487334385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12016505369921741658222923 18024758054882612487334385)
            ·
              refine ⟨13518568541161959365500789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18024758054882612487334385 13518568541161959365500789)
              ·
                refine ⟨1267365800733933690515699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13518568541161959365500789 1267365800733933690515699)
                ·
                  refine ⟨1901048701100900535773549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267365800733933690515699 1901048701100900535773549)
                  ·
                    refine ⟨712893262912837700915081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901048701100900535773549 712893262912837700915081)
                    ·
                      refine ⟨534669947184628275686311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 712893262912837700915081 534669947184628275686311)
                      ·
                        rfl

theorem cell23_1041266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1041266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041266 prefixEnd_1041266 := by exact prefixLift 1041266
  have htrace : WordTrace (prefixWord ++ tailWord_1041266) baseStart_1041266 baseEnd_1041266 := by
    simpa [prefixWord, tailWord_1041266, baseEnd_1041266] using wordTrace_append hprefix tailTrace_1041266
  have hstable : (prefixWord ++ tailWord_1041266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041266).length < 2 ^ (prefixWord ++ tailWord_1041266).sum := by decide
  have hdescent : baseEnd_1041266 < baseStart_1041266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041292 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1041292 : Nat := 118140960795 + 1041292 * 2 ^ 59
def prefixEnd_1041292 : Nat := 4983230072969 + 3 ^ 40 * 1041292 * 2
def baseEnd_1041292 : Nat := 534683297681645173961191

theorem tailTrace_1041292 : CollatzResearch.WordTrace tailWord_1041292 prefixEnd_1041292 534683297681645173961191 := by
  unfold tailWord_1041292
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989519671792198680131065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25319359562389598240174753 18989519671792198680131065)
  ·
    refine ⟨14242139753844149010098299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18989519671792198680131065 14242139753844149010098299)
    ·
      refine ⟨21363209630766223515147449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242139753844149010098299 21363209630766223515147449)
      ·
        refine ⟨16022407223074667636360587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21363209630766223515147449 16022407223074667636360587)
        ·
          refine ⟨24033610834612001454540881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16022407223074667636360587 24033610834612001454540881)
          ·
            refine ⟨18025208125959001090905661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24033610834612001454540881 18025208125959001090905661)
            ·
              refine ⟨6759453047234625409089623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18025208125959001090905661 6759453047234625409089623)
              ·
                refine ⟨10139179570851938113634435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759453047234625409089623 10139179570851938113634435)
                ·
                  refine ⟨15208769356277907170451653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139179570851938113634435 15208769356277907170451653)
                  ·
                    refine ⟨2851644254302107594459685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15208769356277907170451653 2851644254302107594459685)
                    ·
                      refine ⟨534683297681645173961191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2851644254302107594459685 534683297681645173961191)
                      ·
                        rfl

theorem cell23_1041292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1041292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041292 prefixEnd_1041292 := by exact prefixLift 1041292
  have htrace : WordTrace (prefixWord ++ tailWord_1041292) baseStart_1041292 baseEnd_1041292 := by
    simpa [prefixWord, tailWord_1041292, baseEnd_1041292] using wordTrace_append hprefix tailTrace_1041292
  have hstable : (prefixWord ++ tailWord_1041292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041292).length < 2 ^ (prefixWord ++ tailWord_1041292).sum := by decide
  have hdescent : baseEnd_1041292 < baseStart_1041292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041366 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1041366 : Nat := 118140960795 + 1041366 * 2 ^ 59
def prefixEnd_1041366 : Nat := 4983230072969 + 3 ^ 40 * 1041366 * 2
def baseEnd_1041366 : Nat := 178240431750025961478617

theorem tailTrace_1041366 : CollatzResearch.WordTrace tailWord_1041366 prefixEnd_1041366 178240431750025961478617 := by
  unfold tailWord_1041366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373858646582269249903497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25321158896877538665637301 2373858646582269249903497)
  ·
    refine ⟨1780393984936701937427623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2373858646582269249903497 1780393984936701937427623)
    ·
      refine ⟨2670590977405052906141435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780393984936701937427623 2670590977405052906141435)
      ·
        refine ⟨4005886466107579359212153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670590977405052906141435 4005886466107579359212153)
        ·
          refine ⟨3004414849580684519409115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005886466107579359212153 3004414849580684519409115)
          ·
            refine ⟨4506622274371026779113673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004414849580684519409115 4506622274371026779113673)
            ·
              refine ⟨3379966705778270084335255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506622274371026779113673 3379966705778270084335255)
              ·
                refine ⟨5069950058667405126502883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379966705778270084335255 5069950058667405126502883)
                ·
                  refine ⟨7604925088001107689754325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069950058667405126502883 7604925088001107689754325)
                  ·
                    refine ⟨178240431750025961478617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7604925088001107689754325 178240431750025961478617)
                    ·
                      rfl

theorem cell23_1041366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1041366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041366 prefixEnd_1041366 := by exact prefixLift 1041366
  have htrace : WordTrace (prefixWord ++ tailWord_1041366) baseStart_1041366 baseEnd_1041366 := by
    simpa [prefixWord, tailWord_1041366, baseEnd_1041366] using wordTrace_append hprefix tailTrace_1041366
  have hstable : (prefixWord ++ tailWord_1041366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041366).length < 2 ^ (prefixWord ++ tailWord_1041366).sum := by decide
  have hdescent : baseEnd_1041366 < baseStart_1041366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041369 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_1041369 : Nat := 118140960795 + 1041369 * 2 ^ 59
def prefixEnd_1041369 : Nat := 4983230072969 + 3 ^ 40 * 1041369 * 2
def baseEnd_1041369 : Nat := 534722835692041372698337

theorem tailTrace_1041369 : CollatzResearch.WordTrace tailWord_1041369 prefixEnd_1041369 534722835692041372698337 := by
  unfold tailWord_1041369
  simp only [CollatzResearch.WordTrace]
  refine ⟨37981847764305439510815161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25321231842870293007210107 37981847764305439510815161)
  ·
    refine ⟨28486385823229079633111371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37981847764305439510815161 28486385823229079633111371)
    ·
      refine ⟨42729578734843619449667057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28486385823229079633111371 42729578734843619449667057)
      ·
        refine ⟨32047184051132714587250293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42729578734843619449667057 32047184051132714587250293)
        ·
          refine ⟨3004423504793691992554715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32047184051132714587250293 3004423504793691992554715)
          ·
            refine ⟨4506635257190537988832073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004423504793691992554715 4506635257190537988832073)
            ·
              refine ⟨3379976442892903491624055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506635257190537988832073 3379976442892903491624055)
              ·
                refine ⟨5069964664339355237436083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379976442892903491624055 5069964664339355237436083)
                ·
                  refine ⟨7604946996509032856154125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069964664339355237436083 7604946996509032856154125)
                  ·
                    refine ⟨2851855123690887321057797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7604946996509032856154125 2851855123690887321057797)
                    ·
                      refine ⟨534722835692041372698337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2851855123690887321057797 534722835692041372698337)
                      ·
                        rfl

theorem cell23_1041369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_1041369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041369 prefixEnd_1041369 := by exact prefixLift 1041369
  have htrace : WordTrace (prefixWord ++ tailWord_1041369) baseStart_1041369 baseEnd_1041369 := by
    simpa [prefixWord, tailWord_1041369, baseEnd_1041369] using wordTrace_append hprefix tailTrace_1041369
  have hstable : (prefixWord ++ tailWord_1041369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041369).length < 2 ^ (prefixWord ++ tailWord_1041369).sum := by decide
  have hdescent : baseEnd_1041369 < baseStart_1041369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041386 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1041386 : Nat := 118140960795 + 1041386 * 2 ^ 59
def prefixEnd_1041386 : Nat := 4983230072969 + 3 ^ 40 * 1041386 * 2
def baseEnd_1041386 : Nat := 534731564863167806185759

theorem tailTrace_1041386 : CollatzResearch.WordTrace tailWord_1041386 prefixEnd_1041386 534731564863167806185759 := by
  unfold tailWord_1041386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495616951310962853546003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25321645203495900942789341 9495616951310962853546003)
  ·
    refine ⟨14243425426966444280319005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495616951310962853546003 14243425426966444280319005)
    ·
      refine ⟨5341284535112416605119627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14243425426966444280319005 5341284535112416605119627)
      ·
        refine ⟨8011926802668624907679441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341284535112416605119627 8011926802668624907679441)
        ·
          refine ⟨6008945102001468680759581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011926802668624907679441 6008945102001468680759581)
          ·
            refine ⟨2253354413250550755284843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6008945102001468680759581 2253354413250550755284843)
            ·
              refine ⟨3380031619875826132927265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253354413250550755284843 3380031619875826132927265)
              ·
                refine ⟨2535023714906869599695449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380031619875826132927265 2535023714906869599695449)
                ·
                  refine ⟨1901267786180152199771587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2535023714906869599695449 1901267786180152199771587)
                  ·
                    refine ⟨2851901679270228299657381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1901267786180152199771587 2851901679270228299657381)
                    ·
                      refine ⟨534731564863167806185759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2851901679270228299657381 534731564863167806185759)
                      ·
                        rfl

theorem cell23_1041386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1041386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041386 prefixEnd_1041386 := by exact prefixLift 1041386
  have htrace : WordTrace (prefixWord ++ tailWord_1041386) baseStart_1041386 baseEnd_1041386 := by
    simpa [prefixWord, tailWord_1041386, baseEnd_1041386] using wordTrace_append hprefix tailTrace_1041386
  have hstable : (prefixWord ++ tailWord_1041386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041386).length < 2 ^ (prefixWord ++ tailWord_1041386).sum := by decide
  have hdescent : baseEnd_1041386 < baseStart_1041386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041447 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1041447 : Nat := 118140960795 + 1041447 * 2 ^ 59
def prefixEnd_1041447 : Nat := 4983230072969 + 3 ^ 40 * 1041447 * 2
def baseEnd_1041447 : Nat := 178254295727697355840993

theorem tailTrace_1041447 : CollatzResearch.WordTrace tailWord_1041447 prefixEnd_1041447 178254295727697355840993 := by
  unfold tailWord_1041447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37984692658022858832154595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25323128438681905888103063 37984692658022858832154595)
  ·
    refine ⟨56977038987034288248231893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37984692658022858832154595 56977038987034288248231893)
    ·
      refine ⟨1335399351258616130817935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56977038987034288248231893 1335399351258616130817935)
      ·
        refine ⟨2003099026887924196226903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335399351258616130817935 2003099026887924196226903)
        ·
          refine ⟨3004648540331886294340355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003099026887924196226903 3004648540331886294340355)
          ·
            refine ⟨4506972810497829441510533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004648540331886294340355 4506972810497829441510533)
            ·
              refine ⟨845057401968343020283225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4506972810497829441510533 845057401968343020283225)
              ·
                refine ⟨633793051476257265212419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845057401968343020283225 633793051476257265212419)
                ·
                  refine ⟨950689577214385897818629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633793051476257265212419 950689577214385897818629)
                  ·
                    refine ⟨178254295727697355840993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950689577214385897818629 178254295727697355840993)
                    ·
                      rfl

theorem cell23_1041447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1041447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041447 prefixEnd_1041447 := by exact prefixLift 1041447
  have htrace : WordTrace (prefixWord ++ tailWord_1041447) baseStart_1041447 baseEnd_1041447 := by
    simpa [prefixWord, tailWord_1041447, baseEnd_1041447] using wordTrace_append hprefix tailTrace_1041447
  have hstable : (prefixWord ++ tailWord_1041447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041447).length < 2 ^ (prefixWord ++ tailWord_1041447).sum := by decide
  have hdescent : baseEnd_1041447 < baseStart_1041447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041470 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1041470 : Nat := 118140960795 + 1041470 * 2 ^ 59
def prefixEnd_1041470 : Nat := 4983230072969 + 3 ^ 40 * 1041470 * 2
def baseEnd_1041470 : Nat := 534774697238145477535373

theorem tailTrace_1041470 : CollatzResearch.WordTrace tailWord_1041470 prefixEnd_1041470 534774697238145477535373 := by
  unfold tailWord_1041470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748191442117441720030233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25323687691293022506827909 4748191442117441720030233)
  ·
    refine ⟨3561143581588081290022675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4748191442117441720030233 3561143581588081290022675)
    ·
      refine ⟨5341715372382121935034013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3561143581588081290022675 5341715372382121935034013)
      ·
        refine ⟨2003143264643295725637755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5341715372382121935034013 2003143264643295725637755)
        ·
          refine ⟨3004714896964943588456633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003143264643295725637755 3004714896964943588456633)
          ·
            refine ⟨2253536172723707691342475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004714896964943588456633 2253536172723707691342475)
            ·
              refine ⟨3380304259085561537013713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253536172723707691342475 3380304259085561537013713)
              ·
                refine ⟨2535228194314171152760285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380304259085561537013713 2535228194314171152760285)
                ·
                  refine ⟨950710572867814182285107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2535228194314171152760285 950710572867814182285107)
                  ·
                    refine ⟨1426065859301721273427661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 950710572867814182285107 1426065859301721273427661)
                    ·
                      refine ⟨534774697238145477535373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426065859301721273427661 534774697238145477535373)
                      ·
                        rfl

theorem cell23_1041470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1041470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041470 prefixEnd_1041470 := by exact prefixLift 1041470
  have htrace : WordTrace (prefixWord ++ tailWord_1041470) baseStart_1041470 baseEnd_1041470 := by
    simpa [prefixWord, tailWord_1041470, baseEnd_1041470] using wordTrace_append hprefix tailTrace_1041470
  have hstable : (prefixWord ++ tailWord_1041470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041470).length < 2 ^ (prefixWord ++ tailWord_1041470).sum := by decide
  have hdescent : baseEnd_1041470 < baseStart_1041470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041486 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1041486 : Nat := 118140960795 + 1041486 * 2 ^ 59
def prefixEnd_1041486 : Nat := 4983230072969 + 3 ^ 40 * 1041486 * 2
def baseEnd_1041486 : Nat := 178260970976205804978433

theorem tailTrace_1041486 : CollatzResearch.WordTrace tailWord_1041486 prefixEnd_1041486 178260970976205804978433 := by
  unfold tailWord_1041486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748264388110196061603039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25324076736587712328549541 4748264388110196061603039)
  ·
    refine ⟨7122396582165294092404559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748264388110196061603039 7122396582165294092404559)
    ·
      refine ⟨10683594873247941138606839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122396582165294092404559 10683594873247941138606839)
      ·
        refine ⟨16025392309871911707910259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683594873247941138606839 16025392309871911707910259)
        ·
          refine ⟨24038088464807867561865389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16025392309871911707910259 24038088464807867561865389)
          ·
            refine ⟨9014283174302950335699521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24038088464807867561865389 9014283174302950335699521)
            ·
              refine ⟨6760712380727212751774641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014283174302950335699521 6760712380727212751774641)
              ·
                refine ⟨5070534285545409563830981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6760712380727212751774641 5070534285545409563830981)
                ·
                  refine ⟨950725178539764293218309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5070534285545409563830981 950725178539764293218309)
                  ·
                    refine ⟨178260970976205804978433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950725178539764293218309 178260970976205804978433)
                    ·
                      rfl

theorem cell23_1041486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1041486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041486 prefixEnd_1041486 := by exact prefixLift 1041486
  have htrace : WordTrace (prefixWord ++ tailWord_1041486) baseStart_1041486 baseEnd_1041486 := by
    simpa [prefixWord, tailWord_1041486, baseEnd_1041486] using wordTrace_append hprefix tailTrace_1041486
  have hstable : (prefixWord ++ tailWord_1041486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041486).length < 2 ^ (prefixWord ++ tailWord_1041486).sum := by decide
  have hdescent : baseEnd_1041486 < baseStart_1041486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041490 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1041490 : Nat := 118140960795 + 1041490 * 2 ^ 59
def prefixEnd_1041490 : Nat := 4983230072969 + 3 ^ 40 * 1041490 * 2
def baseEnd_1041490 : Nat := 178261655617078466428427

theorem tailTrace_1041490 : CollatzResearch.WordTrace tailWord_1041490 prefixEnd_1041490 178261655617078466428427 := by
  unfold tailWord_1041490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496565249216769293992481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25324173997911384783979949 9496565249216769293992481)
  ·
    refine ⟨7122423936912576970494361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9496565249216769293992481 7122423936912576970494361)
    ·
      refine ⟨5341817952684432727870771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7122423936912576970494361 5341817952684432727870771)
      ·
        refine ⟨8012726929026649091806157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341817952684432727870771 8012726929026649091806157)
        ·
          refine ⟨3004772598384993409427309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8012726929026649091806157 3004772598384993409427309)
          ·
            refine ⟨1126789724394372528535241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3004772598384993409427309 1126789724394372528535241)
            ·
              refine ⟨845092293295779396401431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126789724394372528535241 845092293295779396401431)
              ·
                refine ⟨1267638439943669094602147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845092293295779396401431 1267638439943669094602147)
                ·
                  refine ⟨1901457659915503641903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267638439943669094602147 1901457659915503641903221)
                  ·
                    refine ⟨178261655617078466428427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1901457659915503641903221 178261655617078466428427)
                    ·
                      rfl

theorem cell23_1041490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1041490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041490 prefixEnd_1041490 := by exact prefixLift 1041490
  have htrace : WordTrace (prefixWord ++ tailWord_1041490) baseStart_1041490 baseEnd_1041490 := by
    simpa [prefixWord, tailWord_1041490, baseEnd_1041490] using wordTrace_append hprefix tailTrace_1041490
  have hstable : (prefixWord ++ tailWord_1041490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041490).length < 2 ^ (prefixWord ++ tailWord_1041490).sum := by decide
  have hdescent : baseEnd_1041490 < baseStart_1041490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041493 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_1041493 : Nat := 118140960795 + 1041493 * 2 ^ 59
def prefixEnd_1041493 : Nat := 4983230072969 + 3 ^ 40 * 1041493 * 2
def baseEnd_1041493 : Nat := 534786507293198887547767

theorem tailTrace_1041493 : CollatzResearch.WordTrace tailWord_1041493 prefixEnd_1041493 534786507293198887547767 := by
  unfold tailWord_1041493
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986370415856208688329133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25324246943904139125552755 37986370415856208688329133)
  ·
    refine ⟨14244888905946078258123425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37986370415856208688329133 14244888905946078258123425)
    ·
      refine ⟨10683666679459558693592569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14244888905946078258123425 10683666679459558693592569)
      ·
        refine ⟨8012750009594669020194427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10683666679459558693592569 8012750009594669020194427)
        ·
          refine ⟨12019125014392003530291641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012750009594669020194427 12019125014392003530291641)
          ·
            refine ⟨9014343760794002647718731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12019125014392003530291641 9014343760794002647718731)
            ·
              refine ⟨13521515641191003971578097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014343760794002647718731 13521515641191003971578097)
              ·
                refine ⟨10141136730893252978683573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13521515641191003971578097 10141136730893252978683573)
                ·
                  refine ⟨950731568521242466751585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10141136730893252978683573 950731568521242466751585)
                  ·
                    refine ⟨713048676390931850063689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 950731568521242466751585 713048676390931850063689)
                    ·
                      refine ⟨534786507293198887547767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713048676390931850063689 534786507293198887547767)
                      ·
                        rfl

theorem cell23_1041493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_1041493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041493 prefixEnd_1041493 := by exact prefixLift 1041493
  have htrace : WordTrace (prefixWord ++ tailWord_1041493) baseStart_1041493 baseEnd_1041493 := by
    simpa [prefixWord, tailWord_1041493, baseEnd_1041493] using wordTrace_append hprefix tailTrace_1041493
  have hstable : (prefixWord ++ tailWord_1041493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041493).length < 2 ^ (prefixWord ++ tailWord_1041493).sum := by decide
  have hdescent : baseEnd_1041493 < baseStart_1041493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041539 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1041539 : Nat := 118140960795 + 1041539 * 2 ^ 59
def prefixEnd_1041539 : Nat := 4983230072969 + 3 ^ 40 * 1041539 * 2
def baseEnd_1041539 : Nat := 534810127403305707572555

theorem tailTrace_1041539 : CollatzResearch.WordTrace tailWord_1041539 prefixEnd_1041539 534810127403305707572555 := by
  unfold tailWord_1041539
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988048173689558544503671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25325365449126372363002447 37988048173689558544503671)
  ·
    refine ⟨56982072260534337816755507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37988048173689558544503671 56982072260534337816755507)
    ·
      refine ⟨85473108390801506725133261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56982072260534337816755507 85473108390801506725133261)
      ·
        refine ⟨32052415646550565021924973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85473108390801506725133261 32052415646550565021924973)
        ·
          refine ⟨12019655867456461883221865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32052415646550565021924973 12019655867456461883221865)
          ·
            refine ⟨9014741900592346412416399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12019655867456461883221865 9014741900592346412416399)
            ·
              refine ⟨13522112850888519618624599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014741900592346412416399 13522112850888519618624599)
              ·
                refine ⟨20283169276332779427936899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13522112850888519618624599 20283169276332779427936899)
                ·
                  refine ⟨30424753914499169141905349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20283169276332779427936899 30424753914499169141905349)
                  ·
                    refine ⟨5704641358968594214107253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30424753914499169141905349 5704641358968594214107253)
                    ·
                      refine ⟨534810127403305707572555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5704641358968594214107253 534810127403305707572555)
                      ·
                        rfl

theorem cell23_1041539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1041539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041539 prefixEnd_1041539 := by exact prefixLift 1041539
  have htrace : WordTrace (prefixWord ++ tailWord_1041539) baseStart_1041539 baseEnd_1041539 := by
    simpa [prefixWord, tailWord_1041539, baseEnd_1041539] using wordTrace_append hprefix tailTrace_1041539
  have hstable : (prefixWord ++ tailWord_1041539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041539).length < 2 ^ (prefixWord ++ tailWord_1041539).sum := by decide
  have hdescent : baseEnd_1041539 < baseStart_1041539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041586 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1041586 : Nat := 118140960795 + 1041586 * 2 ^ 59
def prefixEnd_1041586 : Nat := 4983230072969 + 3 ^ 40 * 1041586 * 2
def baseEnd_1041586 : Nat := 534834260994067023684839

theorem tailTrace_1041586 : CollatzResearch.WordTrace tailWord_1041586 prefixEnd_1041586 534834260994067023684839 := by
  unfold tailWord_1041586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497440601129821392866153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25326508269679523714309741 9497440601129821392866153)
  ·
    refine ⟨7123080450847366044649615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9497440601129821392866153 7123080450847366044649615)
    ·
      refine ⟨10684620676271049066974423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123080450847366044649615 10684620676271049066974423)
      ·
        refine ⟨16026931014406573600461635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10684620676271049066974423 16026931014406573600461635)
        ·
          refine ⟨24040396521609860400692453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026931014406573600461635 24040396521609860400692453)
          ·
            refine ⟨4507574347801848825129835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24040396521609860400692453 4507574347801848825129835)
            ·
              refine ⟨6761361521702773237694753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507574347801848825129835 6761361521702773237694753)
              ·
                refine ⟨5071021141277079928271065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761361521702773237694753 5071021141277079928271065)
                ·
                  refine ⟨3803265855957809946203299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071021141277079928271065 3803265855957809946203299)
                  ·
                    refine ⟨5704898783936714919304949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803265855957809946203299 5704898783936714919304949)
                    ·
                      refine ⟨534834260994067023684839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5704898783936714919304949 534834260994067023684839)
                      ·
                        rfl

theorem cell23_1041586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1041586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041586 prefixEnd_1041586 := by exact prefixLift 1041586
  have htrace : WordTrace (prefixWord ++ tailWord_1041586) baseStart_1041586 baseEnd_1041586 := by
    simpa [prefixWord, tailWord_1041586, baseEnd_1041586] using wordTrace_append hprefix tailTrace_1041586
  have hstable : (prefixWord ++ tailWord_1041586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041586).length < 2 ^ (prefixWord ++ tailWord_1041586).sum := by decide
  have hdescent : baseEnd_1041586 < baseStart_1041586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041600 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2]
def baseStart_1041600 : Nat := 118140960795 + 1041600 * 2 ^ 59
def prefixEnd_1041600 : Nat := 4983230072969 + 3 ^ 40 * 1041600 * 2
def baseEnd_1041600 : Nat := 534841449723229968909775

theorem tailTrace_1041600 : CollatzResearch.WordTrace tailWord_1041600 prefixEnd_1041600 534841449723229968909775 := by
  unfold tailWord_1041600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995136513234282981237127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25326848684312377308316169 18995136513234282981237127)
  ·
    refine ⟨28492704769851424471855691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18995136513234282981237127 28492704769851424471855691)
    ·
      refine ⟨42739057154777136707783537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28492704769851424471855691 42739057154777136707783537)
      ·
        refine ⟨32054292866082852530837653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42739057154777136707783537 32054292866082852530837653)
        ·
          refine ⟨1502544978097633712383015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32054292866082852530837653 1502544978097633712383015)
          ·
            refine ⟨2253817467146450568574523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502544978097633712383015 2253817467146450568574523)
            ·
              refine ⟨3380726200719675852861785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253817467146450568574523 3380726200719675852861785)
              ·
                refine ⟨2535544650539756889646339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380726200719675852861785 2535544650539756889646339)
                ·
                  refine ⟨3803316975809635334469509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535544650539756889646339 3803316975809635334469509)
                  ·
                    refine ⟨713121932964306625213033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803316975809635334469509 713121932964306625213033)
                    ·
                      refine ⟨534841449723229968909775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713121932964306625213033 534841449723229968909775)
                      ·
                        rfl

theorem cell23_1041600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_1041600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041600 prefixEnd_1041600 := by exact prefixLift 1041600
  have htrace : WordTrace (prefixWord ++ tailWord_1041600) baseStart_1041600 baseEnd_1041600 := by
    simpa [prefixWord, tailWord_1041600, baseEnd_1041600] using wordTrace_append hprefix tailTrace_1041600
  have hstable : (prefixWord ++ tailWord_1041600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041600).length < 2 ^ (prefixWord ++ tailWord_1041600).sum := by decide
  have hdescent : baseEnd_1041600 < baseStart_1041600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041604 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1041604 : Nat := 118140960795 + 1041604 * 2 ^ 59
def prefixEnd_1041604 : Nat := 4983230072969 + 3 ^ 40 * 1041604 * 2
def baseEnd_1041604 : Nat := 534843503645847953259757

theorem tailTrace_1041604 : CollatzResearch.WordTrace tailWord_1041604 prefixEnd_1041604 534843503645847953259757 := by
  unfold tailWord_1041604
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995209459227037322809933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25326945945636049763746577 18995209459227037322809933)
  ·
    refine ⟨7123203547210138996053725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18995209459227037322809933 7123203547210138996053725)
    ·
      refine ⟨2671201330203802123520147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7123203547210138996053725 2671201330203802123520147)
      ·
        refine ⟨4006801995305703185280221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671201330203802123520147 4006801995305703185280221)
        ·
          refine ⟨1502550748239638694480083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4006801995305703185280221 1502550748239638694480083)
          ·
            refine ⟨2253826122359458041720125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502550748239638694480083 2253826122359458041720125)
            ·
              refine ⟨845184795884796765645047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2253826122359458041720125 845184795884796765645047)
              ·
                refine ⟨1267777193827195148467571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845184795884796765645047 1267777193827195148467571)
                ·
                  refine ⟨1901665790740792722701357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267777193827195148467571 1901665790740792722701357)
                  ·
                    refine ⟨713124671527797271013009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1901665790740792722701357 713124671527797271013009)
                    ·
                      refine ⟨534843503645847953259757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713124671527797271013009 534843503645847953259757)
                      ·
                        rfl

theorem cell23_1041604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1041604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041604 prefixEnd_1041604 := by exact prefixLift 1041604
  have htrace : WordTrace (prefixWord ++ tailWord_1041604) baseStart_1041604 baseEnd_1041604 := by
    simpa [prefixWord, tailWord_1041604, baseEnd_1041604] using wordTrace_append hprefix tailTrace_1041604
  have hstable : (prefixWord ++ tailWord_1041604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041604).length < 2 ^ (prefixWord ++ tailWord_1041604).sum := by decide
  have hdescent : baseEnd_1041604 < baseStart_1041604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041609 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_1041609 : Nat := 118140960795 + 1041609 * 2 ^ 59
def prefixEnd_1041609 : Nat := 4983230072969 + 3 ^ 40 * 1041609 * 2
def baseEnd_1041609 : Nat := 534846071049120433697233

theorem tailTrace_1041609 : CollatzResearch.WordTrace tailWord_1041609 prefixEnd_1041609 534846071049120433697233 := by
  unfold tailWord_1041609
  simp only [CollatzResearch.WordTrace]
  refine ⟨37990601283435960499551881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25327067522290640333034587 37990601283435960499551881)
  ·
    refine ⟨28492950962576970374663911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37990601283435960499551881 28492950962576970374663911)
    ·
      refine ⟨42739426443865455561995867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28492950962576970374663911 42739426443865455561995867)
      ·
        refine ⟨64109139665798183342993801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42739426443865455561995867 64109139665798183342993801)
        ·
          refine ⟨48081854749348637507245351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64109139665798183342993801 48081854749348637507245351)
          ·
            refine ⟨72122782124022956260868027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48081854749348637507245351 72122782124022956260868027)
            ·
              refine ⟨108184173186034434391302041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72122782124022956260868027 108184173186034434391302041)
              ·
                refine ⟨81138129889525825793476531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108184173186034434391302041 81138129889525825793476531)
                ·
                  refine ⟨121707194834288738690214797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81138129889525825793476531 121707194834288738690214797)
                  ·
                    refine ⟨45640198062858277008830549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121707194834288738690214797 45640198062858277008830549)
                    ·
                      refine ⟨534846071049120433697233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45640198062858277008830549 534846071049120433697233)
                      ·
                        rfl

theorem cell23_1041609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_1041609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041609 prefixEnd_1041609 := by exact prefixLift 1041609
  have htrace : WordTrace (prefixWord ++ tailWord_1041609) baseStart_1041609 baseEnd_1041609 := by
    simpa [prefixWord, tailWord_1041609, baseEnd_1041609] using wordTrace_append hprefix tailTrace_1041609
  have hstable : (prefixWord ++ tailWord_1041609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041609).length < 2 ^ (prefixWord ++ tailWord_1041609).sum := by decide
  have hdescent : baseEnd_1041609 < baseStart_1041609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041633 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1041633 : Nat := 118140960795 + 1041633 * 2 ^ 59
def prefixEnd_1041633 : Nat := 4983230072969 + 3 ^ 40 * 1041633 * 2
def baseEnd_1041633 : Nat := 534858394584828339797123

theorem tailTrace_1041633 : CollatzResearch.WordTrace tailWord_1041633 prefixEnd_1041633 534858394584828339797123 := by
  unfold tailWord_1041633
  simp only [CollatzResearch.WordTrace]
  refine ⟨37991476635349012598425553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25327651090232675065617035 37991476635349012598425553)
  ·
    refine ⟨28493607476511759448819165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37991476635349012598425553 28493607476511759448819165)
    ·
      refine ⟨10685102803691909793307187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28493607476511759448819165 10685102803691909793307187)
      ·
        refine ⟨16027654205537864689960781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685102803691909793307187 16027654205537864689960781)
        ·
          refine ⟨6010370327076699258735293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16027654205537864689960781 6010370327076699258735293)
          ·
            refine ⟨2253888872653762222025735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6010370327076699258735293 2253888872653762222025735)
            ·
              refine ⟨3380833308980643333038603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253888872653762222025735 3380833308980643333038603)
              ·
                refine ⟨5071249963470964999557905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380833308980643333038603 5071249963470964999557905)
                ·
                  refine ⟨3803437472603223749668429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071249963470964999557905 3803437472603223749668429)
                  ·
                    refine ⟨1426289052226208906125661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3803437472603223749668429 1426289052226208906125661)
                    ·
                      refine ⟨534858394584828339797123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426289052226208906125661 534858394584828339797123)
                      ·
                        rfl

theorem cell23_1041633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1041633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041633 prefixEnd_1041633 := by exact prefixLift 1041633
  have htrace : WordTrace (prefixWord ++ tailWord_1041633) baseStart_1041633 baseEnd_1041633 := by
    simpa [prefixWord, tailWord_1041633, baseEnd_1041633] using wordTrace_append hprefix tailTrace_1041633
  have hstable : (prefixWord ++ tailWord_1041633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041633).length < 2 ^ (prefixWord ++ tailWord_1041633).sum := by decide
  have hdescent : baseEnd_1041633 < baseStart_1041633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041636 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_1041636 : Nat := 118140960795 + 1041636 * 2 ^ 59
def prefixEnd_1041636 : Nat := 4983230072969 + 3 ^ 40 * 1041636 * 2
def baseEnd_1041636 : Nat := 178286645008930609353203

theorem tailTrace_1041636 : CollatzResearch.WordTrace tailWord_1041636 prefixEnd_1041636 178286645008930609353203 := by
  unfold tailWord_1041636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995793027169072055392381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25327724036225429407189841 18995793027169072055392381)
  ·
    refine ⟨7123422385188402020772143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18995793027169072055392381 7123422385188402020772143)
    ·
      refine ⟨10685133577782603031158215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123422385188402020772143 10685133577782603031158215)
      ·
        refine ⟨16027700366673904546737323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685133577782603031158215 16027700366673904546737323)
        ·
          refine ⟨24041550550010856820105985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16027700366673904546737323 24041550550010856820105985)
          ·
            refine ⟨18031162912508142615079489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24041550550010856820105985 18031162912508142615079489)
            ·
              refine ⟨13523372184381106961309617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18031162912508142615079489 13523372184381106961309617)
              ·
                refine ⟨10142529138285830220982213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523372184381106961309617 10142529138285830220982213)
                ·
                  refine ⟨1901724213428593166434165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10142529138285830220982213 1901724213428593166434165)
                  ·
                    refine ⟨178286645008930609353203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1901724213428593166434165 178286645008930609353203)
                    ·
                      rfl

theorem cell23_1041636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_1041636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041636 prefixEnd_1041636 := by exact prefixLift 1041636
  have htrace : WordTrace (prefixWord ++ tailWord_1041636) baseStart_1041636 baseEnd_1041636 := by
    simpa [prefixWord, tailWord_1041636, baseEnd_1041636] using wordTrace_append hprefix tailTrace_1041636
  have hstable : (prefixWord ++ tailWord_1041636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041636).length < 2 ^ (prefixWord ++ tailWord_1041636).sum := by decide
  have hdescent : baseEnd_1041636 < baseStart_1041636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041646 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1041646 : Nat := 118140960795 + 1041646 * 2 ^ 59
def prefixEnd_1041646 : Nat := 4983230072969 + 3 ^ 40 * 1041646 * 2
def baseEnd_1041646 : Nat := 534865069833336788934563

theorem tailTrace_1041646 : CollatzResearch.WordTrace tailWord_1041646 prefixEnd_1041646 534865069833336788934563 := by
  unfold tailWord_1041646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748993848037739477331099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25327967189534610545765861 4748993848037739477331099)
  ·
    refine ⟨7123490772056609215996649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748993848037739477331099 7123490772056609215996649)
    ·
      refine ⟨5342618079042456911997487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7123490772056609215996649 5342618079042456911997487)
      ·
        refine ⟨8013927118563685367996231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5342618079042456911997487 8013927118563685367996231)
        ·
          refine ⟨12020890677845528051994347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013927118563685367996231 12020890677845528051994347)
          ·
            refine ⟨18031336016768292077991521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020890677845528051994347 18031336016768292077991521)
            ·
              refine ⟨13523502012576219058493641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18031336016768292077991521 13523502012576219058493641)
              ·
                refine ⟨10142626509432164293870231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523502012576219058493641 10142626509432164293870231)
                ·
                  refine ⟨15213939764148246440805347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10142626509432164293870231 15213939764148246440805347)
                  ·
                    refine ⟨22820909646222369661208021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15213939764148246440805347 22820909646222369661208021)
                    ·
                      refine ⟨534865069833336788934563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22820909646222369661208021 534865069833336788934563)
                      ·
                        rfl

theorem cell23_1041646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1041646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041646 prefixEnd_1041646 := by exact prefixLift 1041646
  have htrace : WordTrace (prefixWord ++ tailWord_1041646) baseStart_1041646 baseEnd_1041646 := by
    simpa [prefixWord, tailWord_1041646, baseEnd_1041646] using wordTrace_append hprefix tailTrace_1041646
  have hstable : (prefixWord ++ tailWord_1041646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041646).length < 2 ^ (prefixWord ++ tailWord_1041646).sum := by decide
  have hdescent : baseEnd_1041646 < baseStart_1041646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041673 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 4, 4, 2]
def baseStart_1041673 : Nat := 118140960795 + 1041673 * 2 ^ 59
def prefixEnd_1041673 : Nat := 4983230072969 + 3 ^ 40 * 1041673 * 2
def baseEnd_1041673 : Nat := 534878933811008183296939

theorem tailTrace_1041673 : CollatzResearch.WordTrace tailWord_1041673 prefixEnd_1041673 534878933811008183296939 := by
  unfold tailWord_1041673
  simp only [CollatzResearch.WordTrace]
  refine ⟨37992935555204099429881673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25328623703469399619921115 37992935555204099429881673)
  ·
    refine ⟨28494701666403074572411255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37992935555204099429881673 28494701666403074572411255)
    ·
      refine ⟨42742052499604611858616883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28494701666403074572411255 42742052499604611858616883)
      ·
        refine ⟨64113078749406917787925325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42742052499604611858616883 64113078749406917787925325)
        ·
          refine ⟨24042404531027594170471997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64113078749406917787925325 24042404531027594170471997)
          ·
            refine ⟨9015901699135347813926999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24042404531027594170471997 9015901699135347813926999)
            ·
              refine ⟨13523852548703021720890499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015901699135347813926999 13523852548703021720890499)
              ·
                refine ⟨20285778823054532581335749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523852548703021720890499 20285778823054532581335749)
                ·
                  refine ⟨3803583529322724859000453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20285778823054532581335749 3803583529322724859000453)
                  ·
                    refine ⟨713171911748010911062585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803583529322724859000453 713171911748010911062585)
                    ·
                      refine ⟨534878933811008183296939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713171911748010911062585 534878933811008183296939)
                      ·
                        rfl

theorem cell23_1041673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4, 2].length) (baseStart_1041673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041673 prefixEnd_1041673 := by exact prefixLift 1041673
  have htrace : WordTrace (prefixWord ++ tailWord_1041673) baseStart_1041673 baseEnd_1041673 := by
    simpa [prefixWord, tailWord_1041673, baseEnd_1041673] using wordTrace_append hprefix tailTrace_1041673
  have hstable : (prefixWord ++ tailWord_1041673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041673).length < 2 ^ (prefixWord ++ tailWord_1041673).sum := by decide
  have hdescent : baseEnd_1041673 < baseStart_1041673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041690 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_1041690 : Nat := 118140960795 + 1041690 * 2 ^ 59
def prefixEnd_1041690 : Nat := 4983230072969 + 3 ^ 40 * 1041690 * 2
def baseEnd_1041690 : Nat := 534887662982134616784361

theorem tailTrace_1041690 : CollatzResearch.WordTrace tailWord_1041690 prefixEnd_1041690 534887662982134616784361 := by
  unfold tailWord_1041690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498388899035627833312631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25329037064095007555500349 9498388899035627833312631)
  ·
    refine ⟨14247583348553441749968947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498388899035627833312631 14247583348553441749968947)
    ·
      refine ⟨21371375022830162624953421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14247583348553441749968947 21371375022830162624953421)
      ·
        refine ⟨8014265633561310984357533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21371375022830162624953421 8014265633561310984357533)
        ·
          refine ⟨3005349612585491619134075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8014265633561310984357533 3005349612585491619134075)
          ·
            refine ⟨4508024418878237428701113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005349612585491619134075 4508024418878237428701113)
            ·
              refine ⟨3381018314158678071525835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508024418878237428701113 3381018314158678071525835)
              ·
                refine ⟨5071527471238017107288753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381018314158678071525835 5071527471238017107288753)
                ·
                  refine ⟨3803645603428512830466565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071527471238017107288753 3803645603428512830466565)
                  ·
                    refine ⟨713183550642846155712481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803645603428512830466565 713183550642846155712481)
                    ·
                      refine ⟨534887662982134616784361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713183550642846155712481 534887662982134616784361)
                      ·
                        rfl

theorem cell23_1041690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_1041690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041690 prefixEnd_1041690 := by exact prefixLift 1041690
  have htrace : WordTrace (prefixWord ++ tailWord_1041690) baseStart_1041690 baseEnd_1041690 := by
    simpa [prefixWord, tailWord_1041690, baseEnd_1041690] using wordTrace_append hprefix tailTrace_1041690
  have hstable : (prefixWord ++ tailWord_1041690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041690).length < 2 ^ (prefixWord ++ tailWord_1041690).sum := by decide
  have hdescent : baseEnd_1041690 < baseStart_1041690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041717 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1041717 : Nat := 118140960795 + 1041717 * 2 ^ 59
def prefixEnd_1041717 : Nat := 4983230072969 + 3 ^ 40 * 1041717 * 2
def baseEnd_1041717 : Nat := 178300508986602003715579

theorem tailTrace_1041717 : CollatzResearch.WordTrace tailWord_1041717 prefixEnd_1041717 178300508986602003715579 := by
  unfold tailWord_1041717
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994540367044694944483405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25329693578029796629655603 37994540367044694944483405)
  ·
    refine ⟨14247952637641760604181277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37994540367044694944483405 14247952637641760604181277)
    ·
      refine ⟨5342982239115660226567979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14247952637641760604181277 5342982239115660226567979)
      ·
        refine ⟨8014473358673490339851969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5342982239115660226567979 8014473358673490339851969)
        ·
          refine ⟨6010855019005117754888977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8014473358673490339851969 6010855019005117754888977)
          ·
            refine ⟨4508141264253838316166733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010855019005117754888977 4508141264253838316166733)
            ·
              refine ⟨1690552974095189368562525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4508141264253838316166733 1690552974095189368562525)
              ·
                refine ⟨633957365285696013210947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1690552974095189368562525 633957365285696013210947)
                ·
                  refine ⟨950936047928544019816421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633957365285696013210947 950936047928544019816421)
                  ·
                    refine ⟨178300508986602003715579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 950936047928544019816421 178300508986602003715579)
                    ·
                      rfl

theorem cell23_1041717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1041717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041717 prefixEnd_1041717 := by exact prefixLift 1041717
  have htrace : WordTrace (prefixWord ++ tailWord_1041717) baseStart_1041717 baseEnd_1041717 := by
    simpa [prefixWord, tailWord_1041717, baseEnd_1041717] using wordTrace_append hprefix tailTrace_1041717
  have hstable : (prefixWord ++ tailWord_1041717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041717).length < 2 ^ (prefixWord ++ tailWord_1041717).sum := by decide
  have hdescent : baseEnd_1041717 < baseStart_1041717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041736 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1041736 : Nat := 118140960795 + 1041736 * 2 ^ 59
def prefixEnd_1041736 : Nat := 4983230072969 + 3 ^ 40 * 1041736 * 2
def baseEnd_1041736 : Nat := 534911283092241436809149

theorem tailTrace_1041736 : CollatzResearch.WordTrace tailWord_1041736 prefixEnd_1041736 534911283092241436809149 := by
  unfold tailWord_1041736
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997616676987930594712531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25330155569317240792950041 18997616676987930594712531)
  ·
    refine ⟨28496425015481895892068797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997616676987930594712531 28496425015481895892068797)
    ·
      refine ⟨10686159380805710959525799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28496425015481895892068797 10686159380805710959525799)
      ·
        refine ⟨16029239071208566439288699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686159380805710959525799 16029239071208566439288699)
        ·
          refine ⟨24043858606812849658933049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16029239071208566439288699 24043858606812849658933049)
          ·
            refine ⟨18032893955109637244199787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24043858606812849658933049 18032893955109637244199787)
            ·
              refine ⟨27049340932664455866299681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18032893955109637244199787 27049340932664455866299681)
              ·
                refine ⟨20287005699498341899724761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27049340932664455866299681 20287005699498341899724761)
                ·
                  refine ⟨15215254274623756424793571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20287005699498341899724761 15215254274623756424793571)
                  ·
                    refine ⟨22822881411935634637190357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15215254274623756424793571 22822881411935634637190357)
                    ·
                      refine ⟨534911283092241436809149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22822881411935634637190357 534911283092241436809149)
                      ·
                        rfl

theorem cell23_1041736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1041736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041736 prefixEnd_1041736 := by exact prefixLift 1041736
  have htrace : WordTrace (prefixWord ++ tailWord_1041736) baseStart_1041736 baseEnd_1041736 := by
    simpa [prefixWord, tailWord_1041736, baseEnd_1041736] using wordTrace_append hprefix tailTrace_1041736
  have hstable : (prefixWord ++ tailWord_1041736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041736).length < 2 ^ (prefixWord ++ tailWord_1041736).sum := by decide
  have hdescent : baseEnd_1041736 < baseStart_1041736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041760 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_1041760 : Nat := 118140960795 + 1041760 * 2 ^ 59
def prefixEnd_1041760 : Nat := 4983230072969 + 3 ^ 40 * 1041760 * 2
def baseEnd_1041760 : Nat := 178307868875983114303013

theorem tailTrace_1041760 : CollatzResearch.WordTrace tailWord_1041760 prefixEnd_1041760 178307868875983114303013 := by
  unfold tailWord_1041760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998054352944456644149367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25330739137259275525532489 18998054352944456644149367)
  ·
    refine ⟨28497081529416684966224051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18998054352944456644149367 28497081529416684966224051)
    ·
      refine ⟨42745622294125027449336077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28497081529416684966224051 42745622294125027449336077)
      ·
        refine ⟨16029608360296885293501029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42745622294125027449336077 16029608360296885293501029)
        ·
          refine ⟨3005551567555665992531443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16029608360296885293501029 3005551567555665992531443)
          ·
            refine ⟨4508327351333498988797165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005551567555665992531443 4508327351333498988797165)
            ·
              refine ⟨1690622756750062120798937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4508327351333498988797165 1690622756750062120798937)
              ·
                refine ⟨1267967067562546590599203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690622756750062120798937 1267967067562546590599203)
                ·
                  refine ⟨1901950601343819885898805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267967067562546590599203 1901950601343819885898805)
                  ·
                    refine ⟨178307868875983114303013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1901950601343819885898805 178307868875983114303013)
                    ·
                      rfl

theorem cell23_1041760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_1041760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041760 prefixEnd_1041760 := by exact prefixLift 1041760
  have htrace : WordTrace (prefixWord ++ tailWord_1041760) baseStart_1041760 baseEnd_1041760 := by
    simpa [prefixWord, tailWord_1041760, baseEnd_1041760] using wordTrace_append hprefix tailTrace_1041760
  have hstable : (prefixWord ++ tailWord_1041760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041760).length < 2 ^ (prefixWord ++ tailWord_1041760).sum := by decide
  have hdescent : baseEnd_1041760 < baseStart_1041760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041773 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1041773 : Nat := 118140960795 + 1041773 * 2 ^ 59
def prefixEnd_1041773 : Nat := 4983230072969 + 3 ^ 40 * 1041773 * 2
def baseEnd_1041773 : Nat := 178310093958819264015493

theorem tailTrace_1041773 : CollatzResearch.WordTrace tailWord_1041773 prefixEnd_1041773 178310093958819264015493 := by
  unfold tailWord_1041773
  simp only [CollatzResearch.WordTrace]
  refine ⟨37996582854841816508521973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25331055236561211005681315 37996582854841816508521973)
  ·
    refine ⟨3562179642641420297673935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37996582854841816508521973 3562179642641420297673935)
    ·
      refine ⟨5343269463962130446510903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3562179642641420297673935 5343269463962130446510903)
      ·
        refine ⟨8014904195943195669766355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343269463962130446510903 8014904195943195669766355)
        ·
          refine ⟨12022356293914793504649533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8014904195943195669766355 12022356293914793504649533)
          ·
            refine ⟨4508383610218047564243575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12022356293914793504649533 4508383610218047564243575)
            ·
              refine ⟨6762575415327071346365363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508383610218047564243575 6762575415327071346365363)
              ·
                refine ⟨10143863122990607019548045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762575415327071346365363 10143863122990607019548045)
                ·
                  refine ⟨3803948671121477632330517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10143863122990607019548045 3803948671121477632330517)
                  ·
                    refine ⟨178310093958819264015493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3803948671121477632330517 178310093958819264015493)
                    ·
                      rfl

theorem cell23_1041773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1041773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041773 prefixEnd_1041773 := by exact prefixLift 1041773
  have htrace : WordTrace (prefixWord ++ tailWord_1041773) baseStart_1041773 baseEnd_1041773 := by
    simpa [prefixWord, tailWord_1041773, baseEnd_1041773] using wordTrace_append hprefix tailTrace_1041773
  have hstable : (prefixWord ++ tailWord_1041773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041773).length < 2 ^ (prefixWord ++ tailWord_1041773).sum := by decide
  have hdescent : baseEnd_1041773 < baseStart_1041773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041800 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1041800 : Nat := 118140960795 + 1041800 * 2 ^ 59
def prefixEnd_1041800 : Nat := 4983230072969 + 3 ^ 40 * 1041800 * 2
def baseEnd_1041800 : Nat := 534944145854129186408855

theorem tailTrace_1041800 : CollatzResearch.WordTrace tailWord_1041800 prefixEnd_1041800 534944145854129186408855 := by
  unfold tailWord_1041800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998783812872000059877427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25331711750496000079836569 18998783812872000059877427)
  ·
    refine ⟨28498175719308000089816141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18998783812872000059877427 28498175719308000089816141)
    ·
      refine ⟨10686815894740500033681053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28498175719308000089816141 10686815894740500033681053)
      ·
        refine ⟨4007555960527687512630395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10686815894740500033681053 4007555960527687512630395)
        ·
          refine ⟨6011333940791531268945593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007555960527687512630395 6011333940791531268945593)
          ·
            refine ⟨4508500455593648451709195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011333940791531268945593 4508500455593648451709195)
            ·
              refine ⟨6762750683390472677563793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508500455593648451709195 6762750683390472677563793)
              ·
                refine ⟨5072063012542854508172845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762750683390472677563793 5072063012542854508172845)
                ·
                  refine ⟨1902023629703570440564817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5072063012542854508172845 1902023629703570440564817)
                  ·
                    refine ⟨1426517722277677830423613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1902023629703570440564817 1426517722277677830423613)
                    ·
                      refine ⟨534944145854129186408855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426517722277677830423613 534944145854129186408855)
                      ·
                        rfl

theorem cell23_1041800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1041800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041800 prefixEnd_1041800 := by exact prefixLift 1041800
  have htrace : WordTrace (prefixWord ++ tailWord_1041800) baseStart_1041800 baseEnd_1041800 := by
    simpa [prefixWord, tailWord_1041800, baseEnd_1041800] using wordTrace_append hprefix tailTrace_1041800
  have hstable : (prefixWord ++ tailWord_1041800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041800).length < 2 ^ (prefixWord ++ tailWord_1041800).sum := by decide
  have hdescent : baseEnd_1041800 < baseStart_1041800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041831 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_1041831 : Nat := 118140960795 + 1041831 * 2 ^ 59
def prefixEnd_1041831 : Nat := 4983230072969 + 3 ^ 40 * 1041831 * 2
def baseEnd_1041831 : Nat := 534960063754418565121213

theorem tailTrace_1041831 : CollatzResearch.WordTrace tailWord_1041831 prefixEnd_1041831 534960063754418565121213 := by
  unfold tailWord_1041831
  simp only [CollatzResearch.WordTrace]
  refine ⟨37998698288631692414133347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25332465525754461609422231 37998698288631692414133347)
  ·
    refine ⟨56998047432947538621200021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37998698288631692414133347 56998047432947538621200021)
    ·
      refine ⟨2671783473419415872868751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56998047432947538621200021 2671783473419415872868751)
      ·
        refine ⟨4007675210129123809303127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671783473419415872868751 4007675210129123809303127)
        ·
          refine ⟨6011512815193685713954691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007675210129123809303127 6011512815193685713954691)
          ·
            refine ⟨9017269222790528570932037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011512815193685713954691 9017269222790528570932037)
            ·
              refine ⟨1690737979273224107049757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9017269222790528570932037 1690737979273224107049757)
              ·
                refine ⟨634026742227459040143659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1690737979273224107049757 634026742227459040143659)
                ·
                  refine ⟨951040113341188560215489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634026742227459040143659 951040113341188560215489)
                  ·
                    refine ⟨713280085005891420161617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951040113341188560215489 713280085005891420161617)
                    ·
                      refine ⟨534960063754418565121213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713280085005891420161617 534960063754418565121213)
                      ·
                        rfl

theorem cell23_1041831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_1041831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041831 prefixEnd_1041831 := by exact prefixLift 1041831
  have htrace : WordTrace (prefixWord ++ tailWord_1041831) baseStart_1041831 baseEnd_1041831 := by
    simpa [prefixWord, tailWord_1041831, baseEnd_1041831] using wordTrace_append hprefix tailTrace_1041831
  have hstable : (prefixWord ++ tailWord_1041831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041831).length < 2 ^ (prefixWord ++ tailWord_1041831).sum := by decide
  have hdescent : baseEnd_1041831 < baseStart_1041831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
