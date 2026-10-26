import V185TrunkScan22Chunk293

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2622887 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2622887 : Nat := 118140960795 + 2622887 * 2 ^ 59
def prefixEnd_2622887 : Nat := 4983230072969 + 3 ^ 40 * 2622887 * 2
def baseEnd_2622887 : Nat := 897867822286256450833379

theorem tailTrace_2622887 : CollatzResearch.WordTrace tailWord_2622887 prefixEnd_2622887 897867822286256450833379 := by
  unfold tailWord_2622887
  simp only [CollatzResearch.WordTrace]
  refine ⟨95664548048735827281314915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63776365365823884854209943 95664548048735827281314915)
  ·
    refine ⟨143496822073103740921972373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95664548048735827281314915 143496822073103740921972373)
    ·
      refine ⟨6726413534676737855717455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 143496822073103740921972373 6726413534676737855717455)
      ·
        refine ⟨10089620302015106783576183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6726413534676737855717455 10089620302015106783576183)
        ·
          refine ⟨15134430453022660175364275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10089620302015106783576183 15134430453022660175364275)
          ·
            refine ⟨22701645679533990263046413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15134430453022660175364275 22701645679533990263046413)
            ·
              refine ⟨8513117129825246348642405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22701645679533990263046413 8513117129825246348642405)
              ·
                refine ⟨1596209461842233690370451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8513117129825246348642405 1596209461842233690370451)
                ·
                  refine ⟨2394314192763350535555677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596209461842233690370451 2394314192763350535555677)
                  ·
                    refine ⟨897867822286256450833379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394314192763350535555677 897867822286256450833379)
                    ·
                      rfl

theorem cell22_2622887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2622887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622887 prefixEnd_2622887 := by exact prefixLift 2622887
  have htrace : WordTrace (prefixWord ++ tailWord_2622887) baseStart_2622887 baseEnd_2622887 := by
    simpa [prefixWord, tailWord_2622887, baseEnd_2622887] using wordTrace_append hprefix tailTrace_2622887
  have hstable : (prefixWord ++ tailWord_2622887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622887).length < 2 ^ (prefixWord ++ tailWord_2622887).sum := by decide
  have hdescent : baseEnd_2622887 < baseStart_2622887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622945 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 4]
def baseStart_2622945 : Nat := 118140960795 + 2622945 * 2 ^ 59
def prefixEnd_2622945 : Nat := 4983230072969 + 3 ^ 40 * 2622945 * 2
def baseEnd_2622945 : Nat := 299295892290521210961067

theorem tailTrace_2622945 : CollatzResearch.WordTrace tailWord_2622945 prefixEnd_2622945 299295892290521210961067 := by
  unfold tailWord_2622945
  simp only [CollatzResearch.WordTrace]
  refine ⟨95666663482525703186926289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63777775655017135457950859 95666663482525703186926289)
  ·
    refine ⟨71749997611894277390194717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95666663482525703186926289 71749997611894277390194717)
    ·
      refine ⟨26906249104460354021323019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71749997611894277390194717 26906249104460354021323019)
      ·
        refine ⟨40359373656690531031984529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26906249104460354021323019 40359373656690531031984529)
        ·
          refine ⟨30269530242517898273988397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40359373656690531031984529 30269530242517898273988397)
          ·
            refine ⟨11351073840944211852745649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30269530242517898273988397 11351073840944211852745649)
            ·
              refine ⟨8513305380708158889559237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11351073840944211852745649 8513305380708158889559237)
              ·
                refine ⟨1596244758882779791792357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8513305380708158889559237 1596244758882779791792357)
                ·
                  refine ⟨299295892290521210961067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596244758882779791792357 299295892290521210961067)
                  ·
                    rfl

theorem cell22_2622945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_2622945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622945 prefixEnd_2622945 := by exact prefixLift 2622945
  have htrace : WordTrace (prefixWord ++ tailWord_2622945) baseStart_2622945 baseEnd_2622945 := by
    simpa [prefixWord, tailWord_2622945, baseEnd_2622945] using wordTrace_append hprefix tailTrace_2622945
  have hstable : (prefixWord ++ tailWord_2622945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622945).length < 2 ^ (prefixWord ++ tailWord_2622945).sum := by decide
  have hdescent : baseEnd_2622945 < baseStart_2622945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622958 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2622958 : Nat := 118140960795 + 2622958 * 2 ^ 59
def prefixEnd_2622958 : Nat := 4983230072969 + 3 ^ 40 * 2622958 * 2
def baseEnd_2622958 : Nat := 897892127037235932308161

theorem tailTrace_2622958 : CollatzResearch.WordTrace tailWord_2622958 prefixEnd_2622958 897892127037235932308161 := by
  unfold tailWord_2622958
  simp only [CollatzResearch.WordTrace]
  refine ⟨11958392203934825800893691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63778091754319070938099685 11958392203934825800893691)
  ·
    refine ⟨17937588305902238701340537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11958392203934825800893691 17937588305902238701340537)
    ·
      refine ⟨13453191229426679026005403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17937588305902238701340537 13453191229426679026005403)
      ·
        refine ⟨20179786844140018539008105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13453191229426679026005403 20179786844140018539008105)
        ·
          refine ⟨15134840133105013904256079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20179786844140018539008105 15134840133105013904256079)
          ·
            refine ⟨22702260199657520856384119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15134840133105013904256079 22702260199657520856384119)
            ·
              refine ⟨34053390299486281284576179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22702260199657520856384119 34053390299486281284576179)
              ·
                refine ⟨51080085449229421926864269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34053390299486281284576179 51080085449229421926864269)
                ·
                  refine ⟨19155032043461033222574101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51080085449229421926864269 19155032043461033222574101)
                  ·
                    refine ⟨897892127037235932308161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19155032043461033222574101 897892127037235932308161)
                    ·
                      rfl

theorem cell22_2622958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2622958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622958 prefixEnd_2622958 := by exact prefixLift 2622958
  have htrace : WordTrace (prefixWord ++ tailWord_2622958) baseStart_2622958 baseEnd_2622958 := by
    simpa [prefixWord, tailWord_2622958, baseEnd_2622958] using wordTrace_append hprefix tailTrace_2622958
  have hstable : (prefixWord ++ tailWord_2622958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622958).length < 2 ^ (prefixWord ++ tailWord_2622958).sum := by decide
  have hdescent : baseEnd_2622958 < baseStart_2622958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622960 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_2622960 : Nat := 118140960795 + 2622960 * 2 ^ 59
def prefixEnd_2622960 : Nat := 4983230072969 + 3 ^ 40 * 2622960 * 2
def baseEnd_2622960 : Nat := 897892811678108593758155

theorem tailTrace_2622960 : CollatzResearch.WordTrace tailWord_2622960 prefixEnd_2622960 897892811678108593758155 := by
  unfold tailWord_2622960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47833605288735680374361167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63778140384980907165814889 47833605288735680374361167)
  ·
    refine ⟨71750407933103520561541751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47833605288735680374361167 71750407933103520561541751)
    ·
      refine ⟨107625611899655280842312627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71750407933103520561541751 107625611899655280842312627)
      ·
        refine ⟨161438417849482921263468941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107625611899655280842312627 161438417849482921263468941)
        ·
          refine ⟨60539406693556095473800853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161438417849482921263468941 60539406693556095473800853)
          ·
            refine ⟨2837784688760441975334415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60539406693556095473800853 2837784688760441975334415)
            ·
              refine ⟨4256677033140662963001623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837784688760441975334415 4256677033140662963001623)
              ·
                refine ⟨6385015549710994444502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4256677033140662963001623 6385015549710994444502435)
                ·
                  refine ⟨9577523324566491666753653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385015549710994444502435 9577523324566491666753653)
                  ·
                    refine ⟨897892811678108593758155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9577523324566491666753653 897892811678108593758155)
                    ·
                      rfl

theorem cell22_2622960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_2622960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622960 prefixEnd_2622960 := by exact prefixLift 2622960
  have htrace : WordTrace (prefixWord ++ tailWord_2622960) baseStart_2622960 baseEnd_2622960 := by
    simpa [prefixWord, tailWord_2622960, baseEnd_2622960] using wordTrace_append hprefix tailTrace_2622960
  have hstable : (prefixWord ++ tailWord_2622960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622960).length < 2 ^ (prefixWord ++ tailWord_2622960).sum := by decide
  have hdescent : baseEnd_2622960 < baseStart_2622960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622973 : List Nat := [1, 4, 1, 1, 1, 5, 1, 8]
def baseStart_2622973 : Nat := 118140960795 + 2622973 * 2 ^ 59
def prefixEnd_2622973 : Nat := 4983230072969 + 3 ^ 40 * 2622973 * 2
def baseEnd_2622973 : Nat := 99766362427086765909235

theorem tailTrace_2622973 : CollatzResearch.WordTrace tailWord_2622973 prefixEnd_2622973 99766362427086765909235 := by
  unfold tailWord_2622973
  simp only [CollatzResearch.WordTrace]
  refine ⟨95667684726424263968945573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63778456484282842645963715 95667684726424263968945573)
  ·
    refine ⟨17937690886204549494177295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95667684726424263968945573 17937690886204549494177295)
    ·
      refine ⟨26906536329306824241265943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17937690886204549494177295 26906536329306824241265943)
      ·
        refine ⟨40359804493960236361898915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26906536329306824241265943 40359804493960236361898915)
        ·
          refine ⟨60539706740940354542848373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40359804493960236361898915 60539706740940354542848373)
          ·
            refine ⟨5675597506963158238392035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60539706740940354542848373 5675597506963158238392035)
            ·
              refine ⟨8513396260444737357588053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675597506963158238392035 8513396260444737357588053)
              ·
                refine ⟨99766362427086765909235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8513396260444737357588053 99766362427086765909235)
                ·
                  rfl

theorem cell22_2622973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 8].length) (baseStart_2622973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622973 prefixEnd_2622973 := by exact prefixLift 2622973
  have htrace : WordTrace (prefixWord ++ tailWord_2622973) baseStart_2622973 baseEnd_2622973 := by
    simpa [prefixWord, tailWord_2622973, baseEnd_2622973] using wordTrace_append hprefix tailTrace_2622973
  have hstable : (prefixWord ++ tailWord_2622973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622973).length < 2 ^ (prefixWord ++ tailWord_2622973).sum := by decide
  have hdescent : baseEnd_2622973 < baseStart_2622973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622990 : List Nat := [4, 1, 1, 2, 4, 2, 8]
def baseStart_2622990 : Nat := 118140960795 + 2622990 * 2 ^ 59
def prefixEnd_2622990 : Nat := 4983230072969 + 3 ^ 40 * 2622990 * 2
def baseEnd_2622990 : Nat := 33255669677451796870669

theorem tailTrace_2622990 : CollatzResearch.WordTrace tailWord_2622990 prefixEnd_2622990 33255669677451796870669 := by
  unfold tailWord_2622990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11958538095920334484039303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63778869844908450581542949 11958538095920334484039303)
  ·
    refine ⟨17937807143880501726058955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11958538095920334484039303 17937807143880501726058955)
    ·
      refine ⟨26906710715820752589088433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17937807143880501726058955 26906710715820752589088433)
      ·
        refine ⟨20180033036865564441816325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26906710715820752589088433 20180033036865564441816325)
        ·
          refine ⟨3783756194412293332840561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20180033036865564441816325 3783756194412293332840561)
          ·
            refine ⟨2837817145809219999630421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783756194412293332840561 2837817145809219999630421)
            ·
              refine ⟨33255669677451796870669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2837817145809219999630421 33255669677451796870669)
              ·
                rfl

theorem cell22_2622990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 8].length) (baseStart_2622990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622990 prefixEnd_2622990 := by exact prefixLift 2622990
  have htrace : WordTrace (prefixWord ++ tailWord_2622990) baseStart_2622990 baseEnd_2622990 := by
    simpa [prefixWord, tailWord_2622990, baseEnd_2622990] using wordTrace_append hprefix tailTrace_2622990
  have hstable : (prefixWord ++ tailWord_2622990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622990).length < 2 ^ (prefixWord ++ tailWord_2622990).sum := by decide
  have hdescent : baseEnd_2622990 < baseStart_2622990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622996 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2622996 : Nat := 118140960795 + 2622996 * 2 ^ 59
def prefixEnd_2622996 : Nat := 4983230072969 + 3 ^ 40 * 2622996 * 2
def baseEnd_2622996 : Nat := 299301711737938833286015

theorem tailTrace_2622996 : CollatzResearch.WordTrace tailWord_2622996 prefixEnd_2622996 299301711737938833286015 := by
  unfold tailWord_2622996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834261802670469448516421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63779015736893959264688561 47834261802670469448516421)
  ·
    refine ⟨8968924088000713021596829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47834261802670469448516421 8968924088000713021596829)
    ·
      refine ⟨3363346533000267383098811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8968924088000713021596829 3363346533000267383098811)
      ·
        refine ⟨5045019799500401074648217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363346533000267383098811 5045019799500401074648217)
        ·
          refine ⟨3783764849625300805986163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5045019799500401074648217 3783764849625300805986163)
          ·
            refine ⟨5675647274437951208979245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783764849625300805986163 5675647274437951208979245)
            ·
              refine ⟨2128367727914231703367217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5675647274437951208979245 2128367727914231703367217)
              ·
                refine ⟨1596275795935673777525413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128367727914231703367217 1596275795935673777525413)
                ·
                  refine ⟨299301711737938833286015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596275795935673777525413 299301711737938833286015)
                  ·
                    rfl

theorem cell22_2622996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2622996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622996 prefixEnd_2622996 := by exact prefixLift 2622996
  have htrace : WordTrace (prefixWord ++ tailWord_2622996) baseStart_2622996 baseEnd_2622996 := by
    simpa [prefixWord, tailWord_2622996, baseEnd_2622996] using wordTrace_append hprefix tailTrace_2622996
  have hstable : (prefixWord ++ tailWord_2622996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622996).length < 2 ^ (prefixWord ++ tailWord_2622996).sum := by decide
  have hdescent : baseEnd_2622996 < baseStart_2622996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623011 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 2, 3]
def baseStart_2623011 : Nat := 118140960795 + 2623011 * 2 ^ 59
def prefixEnd_2623011 : Nat := 4983230072969 + 3 ^ 40 * 2623011 * 2
def baseEnd_2623011 : Nat := 897910270020361460732999

theorem tailTrace_2623011 : CollatzResearch.WordTrace tailWord_2623011 prefixEnd_2623011 897910270020361460732999 := by
  unfold tailWord_2623011
  simp only [CollatzResearch.WordTrace]
  refine ⟨95669070700286596458828887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63779380466857730972552591 95669070700286596458828887)
  ·
    refine ⟨143503606050429894688243331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95669070700286596458828887 143503606050429894688243331)
    ·
      refine ⟨215255409075644842032364997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143503606050429894688243331 215255409075644842032364997)
      ·
        refine ⟨40360389201683407881068437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215255409075644842032364997 40360389201683407881068437)
        ·
          refine ⟨1891893243828909744425083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40360389201683407881068437 1891893243828909744425083)
          ·
            refine ⟨2837839865743364616637625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891893243828909744425083 2837839865743364616637625)
            ·
              refine ⟨2128379899307523462478219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2837839865743364616637625 2128379899307523462478219)
              ·
                refine ⟨3192569848961285193717329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128379899307523462478219 3192569848961285193717329)
                ·
                  refine ⟨2394427386720963895287997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3192569848961285193717329 2394427386720963895287997)
                  ·
                    refine ⟨897910270020361460732999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394427386720963895287997 897910270020361460732999)
                    ·
                      rfl

theorem cell22_2623011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 3].length) (baseStart_2623011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623011 prefixEnd_2623011 := by exact prefixLift 2623011
  have htrace : WordTrace (prefixWord ++ tailWord_2623011) baseStart_2623011 baseEnd_2623011 := by
    simpa [prefixWord, tailWord_2623011, baseEnd_2623011] using wordTrace_append hprefix tailTrace_2623011
  have hstable : (prefixWord ++ tailWord_2623011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623011).length < 2 ^ (prefixWord ++ tailWord_2623011).sum := by decide
  have hdescent : baseEnd_2623011 < baseStart_2623011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623080 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_2623080 : Nat := 118140960795 + 2623080 * 2 ^ 59
def prefixEnd_2623080 : Nat := 4983230072969 + 3 ^ 40 * 2623080 * 2
def baseEnd_2623080 : Nat := 299311296710156093585929

theorem tailTrace_2623080 : CollatzResearch.WordTrace tailWord_2623080 prefixEnd_2623080 299311296710156093585929 := by
  unfold tailWord_2623080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47835793668518310621545347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63781058224691080828727129 47835793668518310621545347)
  ·
    refine ⟨71753690502777465932318021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47835793668518310621545347 71753690502777465932318021)
    ·
      refine ⟨13453816969270774862309629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71753690502777465932318021 13453816969270774862309629)
      ·
        refine ⟨5045181363476540573366111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13453816969270774862309629 5045181363476540573366111)
        ·
          refine ⟨7567772045214810860049167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5045181363476540573366111 7567772045214810860049167)
          ·
            refine ⟨11351658067822216290073751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567772045214810860049167 11351658067822216290073751)
            ·
              refine ⟨17027487101733324435110627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11351658067822216290073751 17027487101733324435110627)
              ·
                refine ⟨25541230652599986652665941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17027487101733324435110627 25541230652599986652665941)
                ·
                  refine ⟨299311296710156093585929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25541230652599986652665941 299311296710156093585929)
                  ·
                    rfl

theorem cell22_2623080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_2623080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623080 prefixEnd_2623080 := by exact prefixLift 2623080
  have htrace : WordTrace (prefixWord ++ tailWord_2623080) baseStart_2623080 baseEnd_2623080 := by
    simpa [prefixWord, tailWord_2623080, baseEnd_2623080] using wordTrace_append hprefix tailTrace_2623080
  have hstable : (prefixWord ++ tailWord_2623080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623080).length < 2 ^ (prefixWord ++ tailWord_2623080).sum := by decide
  have hdescent : baseEnd_2623080 < baseStart_2623080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623095 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 4, 3]
def baseStart_2623095 : Nat := 118140960795 + 2623095 * 2 ^ 59
def prefixEnd_2623095 : Nat := 4983230072969 + 3 ^ 40 * 2623095 * 2
def baseEnd_2623095 : Nat := 897939024937013241632741

theorem tailTrace_2623095 : CollatzResearch.WordTrace tailWord_2623095 prefixEnd_2623095 897939024937013241632741 := by
  unfold tailWord_2623095
  simp only [CollatzResearch.WordTrace]
  refine ⟨95672134431982278804886739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63781422954654852536591159 95672134431982278804886739)
  ·
    refine ⟨143508201647973418207330109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95672134431982278804886739 143508201647973418207330109)
    ·
      refine ⟨53815575617990031827748791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143508201647973418207330109 53815575617990031827748791)
      ·
        refine ⟨80723363426985047741623187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53815575617990031827748791 80723363426985047741623187)
        ·
          refine ⟨121085045140477571612434781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80723363426985047741623187 121085045140477571612434781)
          ·
            refine ⟨45406891927679089354663043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121085045140477571612434781 45406891927679089354663043)
            ·
              refine ⟨68110337891518634031994565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45406891927679089354663043 68110337891518634031994565)
              ·
                refine ⟨12770688354659743880998981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68110337891518634031994565 12770688354659743880998981)
                ·
                  refine ⟨2394504066498701977687309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12770688354659743880998981 2394504066498701977687309)
                  ·
                    refine ⟨897939024937013241632741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394504066498701977687309 897939024937013241632741)
                    ·
                      rfl

theorem cell22_2623095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_2623095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623095 prefixEnd_2623095 := by exact prefixLift 2623095
  have htrace : WordTrace (prefixWord ++ tailWord_2623095) baseStart_2623095 baseEnd_2623095 := by
    simpa [prefixWord, tailWord_2623095, baseEnd_2623095] using wordTrace_append hprefix tailTrace_2623095
  have hstable : (prefixWord ++ tailWord_2623095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623095).length < 2 ^ (prefixWord ++ tailWord_2623095).sum := by decide
  have hdescent : baseEnd_2623095 < baseStart_2623095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623097 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 4]
def baseStart_2623097 : Nat := 118140960795 + 2623097 * 2 ^ 59
def prefixEnd_2623097 : Nat := 4983230072969 + 3 ^ 40 * 2623097 * 2
def baseEnd_2623097 : Nat := 299313236525961967694245

theorem tailTrace_2623097 : CollatzResearch.WordTrace tailWord_2623097 prefixEnd_2623097 299313236525961967694245 := by
  unfold tailWord_2623097
  simp only [CollatzResearch.WordTrace]
  refine ⟨95672207377975033146459545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63781471585316688764306363 95672207377975033146459545)
  ·
    refine ⟨71754155533481274859844659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95672207377975033146459545 71754155533481274859844659)
    ·
      refine ⟨107631233300221912289766989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71754155533481274859844659 107631233300221912289766989)
      ·
        refine ⟨40361712487583217108662621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107631233300221912289766989 40361712487583217108662621)
        ·
          refine ⟨15135642182843706415748483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40361712487583217108662621 15135642182843706415748483)
          ·
            refine ⟨22703463274265559623622725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15135642182843706415748483 22703463274265559623622725)
            ·
              refine ⟨4256899363924792429429261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22703463274265559623622725 4256899363924792429429261)
              ·
                refine ⟨1596337261471797161035973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256899363924792429429261 1596337261471797161035973)
                ·
                  refine ⟨299313236525961967694245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596337261471797161035973 299313236525961967694245)
                  ·
                    rfl

theorem cell22_2623097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_2623097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623097 prefixEnd_2623097 := by exact prefixLift 2623097
  have htrace : WordTrace (prefixWord ++ tailWord_2623097) baseStart_2623097 baseEnd_2623097 := by
    simpa [prefixWord, tailWord_2623097, baseEnd_2623097] using wordTrace_append hprefix tailTrace_2623097
  have hstable : (prefixWord ++ tailWord_2623097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623097).length < 2 ^ (prefixWord ++ tailWord_2623097).sum := by decide
  have hdescent : baseEnd_2623097 < baseStart_2623097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623123 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_2623123 : Nat := 118140960795 + 2623123 * 2 ^ 59
def prefixEnd_2623123 : Nat := 4983230072969 + 3 ^ 40 * 2623123 * 2
def baseEnd_2623123 : Nat := 897948609909230501932655

theorem tailTrace_2623123 : CollatzResearch.WordTrace tailWord_2623123 prefixEnd_2623123 897948609909230501932655 := by
  unfold tailWord_2623123
  simp only [CollatzResearch.WordTrace]
  refine ⟨95673155675880839586906023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63782103783920559724604015 95673155675880839586906023)
  ·
    refine ⟨143509733513821259380359035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95673155675880839586906023 143509733513821259380359035)
    ·
      refine ⟨215264600270731889070538553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143509733513821259380359035 215264600270731889070538553)
      ·
        refine ⟨161448450203048916802903915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215264600270731889070538553 161448450203048916802903915)
        ·
          refine ⟨242172675304573375204355873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161448450203048916802903915 242172675304573375204355873)
          ·
            refine ⟨181629506478430031403266905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242172675304573375204355873 181629506478430031403266905)
            ·
              refine ⟨136222129858822523552450179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181629506478430031403266905 136222129858822523552450179)
              ·
                refine ⟨204333194788233785328675269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136222129858822523552450179 204333194788233785328675269)
                ·
                  refine ⟨38312474022793834749126613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204333194788233785328675269 38312474022793834749126613)
                  ·
                    refine ⟨897948609909230501932655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38312474022793834749126613 897948609909230501932655)
                    ·
                      rfl

theorem cell22_2623123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_2623123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623123 prefixEnd_2623123 := by exact prefixLift 2623123
  have htrace : WordTrace (prefixWord ++ tailWord_2623123) baseStart_2623123 baseEnd_2623123 := by
    simpa [prefixWord, tailWord_2623123, baseEnd_2623123] using wordTrace_append hprefix tailTrace_2623123
  have hstable : (prefixWord ++ tailWord_2623123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623123).length < 2 ^ (prefixWord ++ tailWord_2623123).sum := by decide
  have hdescent : baseEnd_2623123 < baseStart_2623123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623232 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_2623232 : Nat := 118140960795 + 2623232 * 2 ^ 59
def prefixEnd_2623232 : Nat := 4983230072969 + 3 ^ 40 * 2623232 * 2
def baseEnd_2623232 : Nat := 299328640945596850319107

theorem tailTrace_2623232 : CollatzResearch.WordTrace tailWord_2623232 prefixEnd_2623232 299328640945596850319107 := by
  unfold tailWord_2623232
  simp only [CollatzResearch.WordTrace]
  refine ⟨47838565616242975601311975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63784754154990634135082633 47838565616242975601311975)
  ·
    refine ⟨71757848424364463401967963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47838565616242975601311975 71757848424364463401967963)
    ·
      refine ⟨107636772636546695102951945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71757848424364463401967963 107636772636546695102951945)
      ·
        refine ⟨80727579477410021327213959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107636772636546695102951945 80727579477410021327213959)
        ·
          refine ⟨121091369216115031990820939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80727579477410021327213959 121091369216115031990820939)
          ·
            refine ⟨181637053824172547986231409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121091369216115031990820939 181637053824172547986231409)
            ·
              refine ⟨136227790368129410989673557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181637053824172547986231409 136227790368129410989673557)
              ·
                refine ⟨1596419418376516535035237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 136227790368129410989673557 1596419418376516535035237)
                ·
                  refine ⟨299328640945596850319107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596419418376516535035237 299328640945596850319107)
                  ·
                    rfl

theorem cell22_2623232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_2623232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623232 prefixEnd_2623232 := by exact prefixLift 2623232
  have htrace : WordTrace (prefixWord ++ tailWord_2623232) baseStart_2623232 baseEnd_2623232 := by
    simpa [prefixWord, tailWord_2623232, baseEnd_2623232] using wordTrace_append hprefix tailTrace_2623232
  have hstable : (prefixWord ++ tailWord_2623232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623232).length < 2 ^ (prefixWord ++ tailWord_2623232).sum := by decide
  have hdescent : baseEnd_2623232 < baseStart_2623232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623281 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_2623281 : Nat := 118140960795 + 2623281 * 2 ^ 59
def prefixEnd_2623281 : Nat := 4983230072969 + 3 ^ 40 * 2623281 * 2
def baseEnd_2623281 : Nat := 898002696538170756482171

theorem tailTrace_2623281 : CollatzResearch.WordTrace tailWord_2623281 prefixEnd_2623281 898002696538170756482171 := by
  unfold tailWord_2623281
  simp only [CollatzResearch.WordTrace]
  refine ⟨95678918409308432571157697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63785945606205621714105131 95678918409308432571157697)
  ·
    refine ⟨71759188806981324428368273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95678918409308432571157697 71759188806981324428368273)
    ·
      refine ⟨53819391605235993321276205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71759188806981324428368273 53819391605235993321276205)
      ·
        refine ⟨20182271851963497495478577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53819391605235993321276205 20182271851963497495478577)
        ·
          refine ⟨15136703888972623121608933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20182271851963497495478577 15136703888972623121608933)
          ·
            refine ⟨2838131979182366835301675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15136703888972623121608933 2838131979182366835301675)
            ·
              refine ⟨4257197968773550252952513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838131979182366835301675 4257197968773550252952513)
              ·
                refine ⟨3192898476580162689714385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4257197968773550252952513 3192898476580162689714385)
                ·
                  refine ⟨2394673857435122017285789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3192898476580162689714385 2394673857435122017285789)
                  ·
                    refine ⟨898002696538170756482171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394673857435122017285789 898002696538170756482171)
                    ·
                      rfl

theorem cell22_2623281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_2623281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623281 prefixEnd_2623281 := by exact prefixLift 2623281
  have htrace : WordTrace (prefixWord ++ tailWord_2623281) baseStart_2623281 baseEnd_2623281 := by
    simpa [prefixWord, tailWord_2623281, baseEnd_2623281] using wordTrace_append hprefix tailTrace_2623281
  have hstable : (prefixWord ++ tailWord_2623281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623281).length < 2 ^ (prefixWord ++ tailWord_2623281).sum := by decide
  have hdescent : baseEnd_2623281 < baseStart_2623281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623446 : List Nat := [5, 2, 1, 1, 3, 1, 9]
def baseStart_2623446 : Nat := 118140960795 + 2623446 * 2 ^ 59
def prefixEnd_2623446 : Nat := 4983230072969 + 3 ^ 40 * 2623446 * 2
def baseEnd_2623446 : Nat := 33261451089265382448395

theorem tailTrace_2623446 : CollatzResearch.WordTrace tailWord_2623446 prefixEnd_2623446 33261451089265382448395 := by
  unfold tailWord_2623446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980308528356916609432137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63789957635807110500609461 5980308528356916609432137)
  ·
    refine ⟨4485231396267687457074103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5980308528356916609432137 4485231396267687457074103)
    ·
      refine ⟨6727847094401531185611155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485231396267687457074103 6727847094401531185611155)
      ·
        refine ⟨10091770641602296778416733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6727847094401531185611155 10091770641602296778416733)
        ·
          refine ⟨3784413990600861291906275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10091770641602296778416733 3784413990600861291906275)
          ·
            refine ⟨5676620985901291937859413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784413990600861291906275 5676620985901291937859413)
            ·
              refine ⟨33261451089265382448395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5676620985901291937859413 33261451089265382448395)
              ·
                rfl

theorem cell22_2623446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 9].length) (baseStart_2623446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623446 prefixEnd_2623446 := by exact prefixLift 2623446
  have htrace : WordTrace (prefixWord ++ tailWord_2623446) baseStart_2623446 baseEnd_2623446 := by
    simpa [prefixWord, tailWord_2623446, baseEnd_2623446] using wordTrace_append hprefix tailTrace_2623446
  have hstable : (prefixWord ++ tailWord_2623446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623446).length < 2 ^ (prefixWord ++ tailWord_2623446).sum := by decide
  have hdescent : baseEnd_2623446 < baseStart_2623446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623450 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_2623450 : Nat := 118140960795 + 2623450 * 2 ^ 59
def prefixEnd_2623450 : Nat := 4983230072969 + 3 ^ 40 * 2623450 * 2
def baseEnd_2623450 : Nat := 898060548691910649006653

theorem tailTrace_2623450 : CollatzResearch.WordTrace tailWord_2623450 prefixEnd_2623450 898060548691910649006653 := by
  unfold tailWord_2623450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23921270586424043608514951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63790054897130782956039869 23921270586424043608514951)
  ·
    refine ⟨35881905879636065412772427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23921270586424043608514951 35881905879636065412772427)
    ·
      refine ⟨53822858819454098119158641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35881905879636065412772427 53822858819454098119158641)
      ·
        refine ⟨40367144114590573589368981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53822858819454098119158641 40367144114590573589368981)
        ·
          refine ⟨1892209880371433137001671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40367144114590573589368981 1892209880371433137001671)
          ·
            refine ⟨2838314820557149705502507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892209880371433137001671 2838314820557149705502507)
            ·
              refine ⟨4257472230835724558253761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838314820557149705502507 4257472230835724558253761)
              ·
                refine ⟨3193104173126793418690321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4257472230835724558253761 3193104173126793418690321)
                ·
                  refine ⟨2394828129845095064017741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3193104173126793418690321 2394828129845095064017741)
                  ·
                    refine ⟨898060548691910649006653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394828129845095064017741 898060548691910649006653)
                    ·
                      rfl

theorem cell22_2623450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_2623450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623450 prefixEnd_2623450 := by exact prefixLift 2623450
  have htrace : WordTrace (prefixWord ++ tailWord_2623450) baseStart_2623450 baseEnd_2623450 := by
    simpa [prefixWord, tailWord_2623450, baseEnd_2623450] using wordTrace_append hprefix tailTrace_2623450
  have hstable : (prefixWord ++ tailWord_2623450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623450).length < 2 ^ (prefixWord ++ tailWord_2623450).sum := by decide
  have hdescent : baseEnd_2623450 < baseStart_2623450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623487 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_2623487 : Nat := 118140960795 + 2623487 * 2 ^ 59
def prefixEnd_2623487 : Nat := 4983230072969 + 3 ^ 40 * 2623487 * 2
def baseEnd_2623487 : Nat := 898073214548054885831539

theorem tailTrace_2623487 : CollatzResearch.WordTrace tailWord_2623487 prefixEnd_2623487 898073214548054885831539 := by
  unfold tailWord_2623487
  simp only [CollatzResearch.WordTrace]
  refine ⟨95686431846562129753156715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63790954564374753168771143 95686431846562129753156715)
  ·
    refine ⟨143529647769843194629735073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95686431846562129753156715 143529647769843194629735073)
    ·
      refine ⟨107647235827382395972301305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143529647769843194629735073 107647235827382395972301305)
      ·
        refine ⟨80735426870536796979225979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107647235827382395972301305 80735426870536796979225979)
        ·
          refine ⟨121103140305805195468838969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80735426870536796979225979 121103140305805195468838969)
          ·
            refine ⟨90827355229353896601629227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121103140305805195468838969 90827355229353896601629227)
            ·
              refine ⟨136241032844030844902443841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90827355229353896601629227 136241032844030844902443841)
              ·
                refine ⟨102180774633023133676832881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136241032844030844902443841 102180774633023133676832881)
                ·
                  refine ⟨76635580974767350257624661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102180774633023133676832881 76635580974767350257624661)
                  ·
                    refine ⟨898073214548054885831539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76635580974767350257624661 898073214548054885831539)
                    ·
                      rfl

theorem cell22_2623487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_2623487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623487 prefixEnd_2623487 := by exact prefixLift 2623487
  have htrace : WordTrace (prefixWord ++ tailWord_2623487) baseStart_2623487 baseEnd_2623487 := by
    simpa [prefixWord, tailWord_2623487, baseEnd_2623487] using wordTrace_append hprefix tailTrace_2623487
  have hstable : (prefixWord ++ tailWord_2623487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623487).length < 2 ^ (prefixWord ++ tailWord_2623487).sum := by decide
  have hdescent : baseEnd_2623487 < baseStart_2623487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623495 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2623495 : Nat := 118140960795 + 2623495 * 2 ^ 59
def prefixEnd_2623495 : Nat := 4983230072969 + 3 ^ 40 * 2623495 * 2
def baseEnd_2623495 : Nat := 898075953111545531631515

theorem tailTrace_2623495 : CollatzResearch.WordTrace tailWord_2623495 prefixEnd_2623495 898075953111545531631515 := by
  unfold tailWord_2623495
  simp only [CollatzResearch.WordTrace]
  refine ⟨95686723630533147119447939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63791149087022098079631959 95686723630533147119447939)
  ·
    refine ⟨143530085445799720679171909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95686723630533147119447939 143530085445799720679171909)
    ·
      refine ⟨26911891021087447627344733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143530085445799720679171909 26911891021087447627344733)
      ·
        refine ⟨10091959132907792860254275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26911891021087447627344733 10091959132907792860254275)
        ·
          refine ⟨15137938699361689290381413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10091959132907792860254275 15137938699361689290381413)
          ·
            refine ⟨2838363506130316741946515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15137938699361689290381413 2838363506130316741946515)
            ·
              refine ⟨4257545259195475112919773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838363506130316741946515 4257545259195475112919773)
              ·
                refine ⟨1596579472198303167344915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4257545259195475112919773 1596579472198303167344915)
                ·
                  refine ⟨2394869208297454751017373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596579472198303167344915 2394869208297454751017373)
                  ·
                    refine ⟨898075953111545531631515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394869208297454751017373 898075953111545531631515)
                    ·
                      rfl

theorem cell22_2623495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2623495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623495 prefixEnd_2623495 := by exact prefixLift 2623495
  have htrace : WordTrace (prefixWord ++ tailWord_2623495) baseStart_2623495 baseEnd_2623495 := by
    simpa [prefixWord, tailWord_2623495, baseEnd_2623495] using wordTrace_append hprefix tailTrace_2623495
  have hstable : (prefixWord ++ tailWord_2623495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623495).length < 2 ^ (prefixWord ++ tailWord_2623495).sum := by decide
  have hdescent : baseEnd_2623495 < baseStart_2623495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623538 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_2623538 : Nat := 118140960795 + 2623538 * 2 ^ 59
def prefixEnd_2623538 : Nat := 4983230072969 + 3 ^ 40 * 2623538 * 2
def baseEnd_2623538 : Nat := 898090672890307752806383

theorem tailTrace_2623538 : CollatzResearch.WordTrace tailWord_2623538 prefixEnd_2623538 898090672890307752806383 := by
  unfold tailWord_2623538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23922072992344341365815817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63792194646251576975508845 23922072992344341365815817)
  ·
    refine ⟨17941554744258256024361863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23922072992344341365815817 17941554744258256024361863)
    ·
      refine ⟨26912332116387384036542795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17941554744258256024361863 26912332116387384036542795)
      ·
        refine ⟨40368498174581076054814193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26912332116387384036542795 40368498174581076054814193)
        ·
          refine ⟨30276373630935807041110645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40368498174581076054814193 30276373630935807041110645)
          ·
            refine ⟨2838410027900231910104123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30276373630935807041110645 2838410027900231910104123)
            ·
              refine ⟨4257615041850347865156185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838410027900231910104123 4257615041850347865156185)
              ·
                refine ⟨3193211281387760898867139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4257615041850347865156185 3193211281387760898867139)
                ·
                  refine ⟨4789816922081641348300709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193211281387760898867139 4789816922081641348300709)
                  ·
                    refine ⟨898090672890307752806383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4789816922081641348300709 898090672890307752806383)
                    ·
                      rfl

theorem cell22_2623538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_2623538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623538 prefixEnd_2623538 := by exact prefixLift 2623538
  have htrace : WordTrace (prefixWord ++ tailWord_2623538) baseStart_2623538 baseEnd_2623538 := by
    simpa [prefixWord, tailWord_2623538, baseEnd_2623538] using wordTrace_append hprefix tailTrace_2623538
  have hstable : (prefixWord ++ tailWord_2623538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623538).length < 2 ^ (prefixWord ++ tailWord_2623538).sum := by decide
  have hdescent : baseEnd_2623538 < baseStart_2623538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623566 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2623566 : Nat := 118140960795 + 2623566 * 2 ^ 59
def prefixEnd_2623566 : Nat := 4983230072969 + 3 ^ 40 * 2623566 * 2
def baseEnd_2623566 : Nat := 898100257862525013106297

theorem tailTrace_2623566 : CollatzResearch.WordTrace tailWord_2623566 prefixEnd_2623566 898100257862525013106297 := by
  unfold tailWord_2623566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961164151659490780660319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63792875475517284163521701 11961164151659490780660319)
  ·
    refine ⟨17941746227489236170990479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11961164151659490780660319 17941746227489236170990479)
    ·
      refine ⟨26912619341233854256485719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17941746227489236170990479 26912619341233854256485719)
      ·
        refine ⟨40368929011850781384728579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26912619341233854256485719 40368929011850781384728579)
        ·
          refine ⟨60553393517776172077092869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40368929011850781384728579 60553393517776172077092869)
          ·
            refine ⟨11353761284583032264454913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60553393517776172077092869 11353761284583032264454913)
            ·
              refine ⟨8515320963437274198341185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11353761284583032264454913 8515320963437274198341185)
              ·
                refine ⟨6386490722577955648755889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8515320963437274198341185 6386490722577955648755889)
                ·
                  refine ⟨4789868041933466736566917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6386490722577955648755889 4789868041933466736566917)
                  ·
                    refine ⟨898100257862525013106297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4789868041933466736566917 898100257862525013106297)
                    ·
                      rfl

theorem cell22_2623566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2623566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623566 prefixEnd_2623566 := by exact prefixLift 2623566
  have htrace : WordTrace (prefixWord ++ tailWord_2623566) baseStart_2623566 baseEnd_2623566 := by
    simpa [prefixWord, tailWord_2623566, baseEnd_2623566] using wordTrace_append hprefix tailTrace_2623566
  have hstable : (prefixWord ++ tailWord_2623566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623566).length < 2 ^ (prefixWord ++ tailWord_2623566).sum := by decide
  have hdescent : baseEnd_2623566 < baseStart_2623566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623596 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_2623596 : Nat := 118140960795 + 2623596 * 2 ^ 59
def prefixEnd_2623596 : Nat := 4983230072969 + 3 ^ 40 * 2623596 * 2
def baseEnd_2623596 : Nat := 898110527475614934856205

theorem tailTrace_2623596 : CollatzResearch.WordTrace tailWord_2623596 prefixEnd_2623596 898110527475614934856205 := by
  unfold tailWord_2623596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47845203701583620684437321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63793604935444827579249761 47845203701583620684437321)
  ·
    refine ⟨35883902776187715513327991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47845203701583620684437321 35883902776187715513327991)
    ·
      refine ⟨53825854164281573269991987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35883902776187715513327991 53825854164281573269991987)
      ·
        refine ⟨80738781246422359904987981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53825854164281573269991987 80738781246422359904987981)
        ·
          refine ⟨30277042967408384964370493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80738781246422359904987981 30277042967408384964370493)
          ·
            refine ⟨11353891112778144361638935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30277042967408384964370493 11353891112778144361638935)
            ·
              refine ⟨17030836669167216542458403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11353891112778144361638935 17030836669167216542458403)
              ·
                refine ⟨25546255003750824813687605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17030836669167216542458403 25546255003750824813687605)
                ·
                  refine ⟨2394961406601639826283213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25546255003750824813687605 2394961406601639826283213)
                  ·
                    refine ⟨898110527475614934856205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394961406601639826283213 898110527475614934856205)
                    ·
                      rfl

theorem cell22_2623596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_2623596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623596 prefixEnd_2623596 := by exact prefixLift 2623596
  have htrace : WordTrace (prefixWord ++ tailWord_2623596) baseStart_2623596 baseEnd_2623596 := by
    simpa [prefixWord, tailWord_2623596, baseEnd_2623596] using wordTrace_append hprefix tailTrace_2623596
  have hstable : (prefixWord ++ tailWord_2623596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623596).length < 2 ^ (prefixWord ++ tailWord_2623596).sum := by decide
  have hdescent : baseEnd_2623596 < baseStart_2623596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623626 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_2623626 : Nat := 118140960795 + 2623626 * 2 ^ 59
def prefixEnd_2623626 : Nat := 4983230072969 + 3 ^ 40 * 2623626 * 2
def baseEnd_2623626 : Nat := 299373599029568285535371

theorem tailTrace_2623626 : CollatzResearch.WordTrace tailWord_2623626 prefixEnd_2623626 299373599029568285535371 := by
  unfold tailWord_2623626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23922875398264639123116683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63794334395372370994977821 23922875398264639123116683)
  ·
    refine ⟨35884313097396958684675025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23922875398264639123116683 35884313097396958684675025)
    ·
      refine ⟨26913234823047719013506269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35884313097396958684675025 26913234823047719013506269)
      ·
        refine ⟨10092463058642894630064851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26913234823047719013506269 10092463058642894630064851)
        ·
          refine ⟨15138694587964341945097277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10092463058642894630064851 15138694587964341945097277)
          ·
            refine ⟨5677010470486628229411479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15138694587964341945097277 5677010470486628229411479)
            ·
              refine ⟨8515515705729942344117219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677010470486628229411479 8515515705729942344117219)
              ·
                refine ⟨12773273558594913516175829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8515515705729942344117219 12773273558594913516175829)
                ·
                  refine ⟨299373599029568285535371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12773273558594913516175829 299373599029568285535371)
                  ·
                    rfl

theorem cell22_2623626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_2623626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623626 prefixEnd_2623626 := by exact prefixLift 2623626
  have htrace : WordTrace (prefixWord ++ tailWord_2623626) baseStart_2623626 baseEnd_2623626 := by
    simpa [prefixWord, tailWord_2623626, baseEnd_2623626] using wordTrace_append hprefix tailTrace_2623626
  have hstable : (prefixWord ++ tailWord_2623626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623626).length < 2 ^ (prefixWord ++ tailWord_2623626).sum := by decide
  have hdescent : baseEnd_2623626 < baseStart_2623626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623630 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2623630 : Nat := 118140960795 + 2623630 * 2 ^ 59
def prefixEnd_2623630 : Nat := 4983230072969 + 3 ^ 40 * 2623630 * 2
def baseEnd_2623630 : Nat := 898122166370450179506101

theorem tailTrace_2623630 : CollatzResearch.WordTrace tailWord_2623630 prefixEnd_2623630 898122166370450179506101 := by
  unfold tailWord_2623630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961455935630508146951543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63794431656696043450408229 11961455935630508146951543)
  ·
    refine ⟨17942183903445762220427315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11961455935630508146951543 17942183903445762220427315)
    ·
      refine ⟨26913275855168643330640973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17942183903445762220427315 26913275855168643330640973)
      ·
        refine ⟨10092478445688241248990365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26913275855168643330640973 10092478445688241248990365)
        ·
          refine ⟨3784679417133090468371387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10092478445688241248990365 3784679417133090468371387)
          ·
            refine ⟨5677019125699635702557081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784679417133090468371387 5677019125699635702557081)
            ·
              refine ⟨4257764344274726776917811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677019125699635702557081 4257764344274726776917811)
              ·
                refine ⟨6386646516412090165376717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257764344274726776917811 6386646516412090165376717)
                ·
                  refine ⟨2394992443654533812016269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6386646516412090165376717 2394992443654533812016269)
                  ·
                    refine ⟨898122166370450179506101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394992443654533812016269 898122166370450179506101)
                    ·
                      rfl

theorem cell22_2623630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2623630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623630 prefixEnd_2623630 := by exact prefixLift 2623630
  have htrace : WordTrace (prefixWord ++ tailWord_2623630) baseStart_2623630 baseEnd_2623630 := by
    simpa [prefixWord, tailWord_2623630, baseEnd_2623630] using wordTrace_append hprefix tailTrace_2623630
  have hstable : (prefixWord ++ tailWord_2623630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623630).length < 2 ^ (prefixWord ++ tailWord_2623630).sum := by decide
  have hdescent : baseEnd_2623630 < baseStart_2623630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623825 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2623825 : Nat := 118140960795 + 2623825 * 2 ^ 59
def prefixEnd_2623825 : Nat := 4983230072969 + 3 ^ 40 * 2623825 * 2
def baseEnd_2623825 : Nat := 898188918855534670880503

theorem tailTrace_2623825 : CollatzResearch.WordTrace tailWord_2623825 prefixEnd_2623825 898188918855534670880503 := by
  unfold tailWord_2623825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95698759719337613478960929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63799173146225075652640619 95698759719337613478960929)
  ·
    refine ⟨71774069789503210109220697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95698759719337613478960929 71774069789503210109220697)
    ·
      refine ⟨53830552342127407581915523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71774069789503210109220697 53830552342127407581915523)
      ·
        refine ⟨80745828513191111372873285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53830552342127407581915523 80745828513191111372873285)
        ·
          refine ⟨15139842846223333382413741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80745828513191111372873285 15139842846223333382413741)
          ·
            refine ⟨5677441067333750018405153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15139842846223333382413741 5677441067333750018405153)
            ·
              refine ⟨4258080800500312513803865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677441067333750018405153 4258080800500312513803865)
              ·
                refine ⟨3193560600375234385352899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258080800500312513803865 3193560600375234385352899)
                ·
                  refine ⟨4790340900562851578029349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193560600375234385352899 4790340900562851578029349)
                  ·
                    refine ⟨898188918855534670880503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790340900562851578029349 898188918855534670880503)
                    ·
                      rfl

theorem cell22_2623825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2623825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623825 prefixEnd_2623825 := by exact prefixLift 2623825
  have htrace : WordTrace (prefixWord ++ tailWord_2623825) baseStart_2623825 baseEnd_2623825 := by
    simpa [prefixWord, tailWord_2623825, baseEnd_2623825] using wordTrace_append hprefix tailTrace_2623825
  have hstable : (prefixWord ++ tailWord_2623825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623825).length < 2 ^ (prefixWord ++ tailWord_2623825).sum := by decide
  have hdescent : baseEnd_2623825 < baseStart_2623825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623975 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 6]
def baseStart_2623975 : Nat := 118140960795 + 2623975 * 2 ^ 59
def prefixEnd_2623975 : Nat := 4983230072969 + 3 ^ 40 * 2623975 * 2
def baseEnd_2623975 : Nat := 299413422306994759876681

theorem tailTrace_2623975 : CollatzResearch.WordTrace tailWord_2623975 prefixEnd_2623975 299413422306994759876681 := by
  unfold tailWord_2623975
  simp only [CollatzResearch.WordTrace]
  refine ⟨95704230668794189096921379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63802820445862792731280919 95704230668794189096921379)
  ·
    refine ⟨143556346003191283645382069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95704230668794189096921379 143556346003191283645382069)
    ·
      refine ⟨13458407437799182841754569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143556346003191283645382069 13458407437799182841754569)
      ·
        refine ⟨10093805578349387131315927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13458407437799182841754569 10093805578349387131315927)
        ·
          refine ⟨15140708367524080696973891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10093805578349387131315927 15140708367524080696973891)
          ·
            refine ⟨22711062551286121045460837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15140708367524080696973891 22711062551286121045460837)
            ·
              refine ⟨4258324228366147696023907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22711062551286121045460837 4258324228366147696023907)
              ·
                refine ⟨6387486342549221544035861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258324228366147696023907 6387486342549221544035861)
                ·
                  refine ⟨299413422306994759876681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6387486342549221544035861 299413422306994759876681)
                  ·
                    rfl

theorem cell22_2623975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 6].length) (baseStart_2623975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2623975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2623975 prefixEnd_2623975 := by exact prefixLift 2623975
  have htrace : WordTrace (prefixWord ++ tailWord_2623975) baseStart_2623975 baseEnd_2623975 := by
    simpa [prefixWord, tailWord_2623975, baseEnd_2623975] using wordTrace_append hprefix tailTrace_2623975
  have hstable : (prefixWord ++ tailWord_2623975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623975).length < 2 ^ (prefixWord ++ tailWord_2623975).sum := by decide
  have hdescent : baseEnd_2623975 < baseStart_2623975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624003 : List Nat := [1, 1, 1, 3, 2, 1, 5, 8]
def baseStart_2624003 : Nat := 118140960795 + 2624003 * 2 ^ 59
def prefixEnd_2624003 : Nat := 4983230072969 + 3 ^ 40 * 2624003 * 2
def baseEnd_2624003 : Nat := 99805539099244615547773

theorem tailTrace_2624003 : CollatzResearch.WordTrace tailWord_2624003 prefixEnd_2624003 99805539099244615547773 := by
  unfold tailWord_2624003
  simp only [CollatzResearch.WordTrace]
  refine ⟨95705251912692749878940663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63803501275128499919293775 95705251912692749878940663)
  ·
    refine ⟨143557877869039124818410995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95705251912692749878940663 143557877869039124818410995)
    ·
      refine ⟨215336816803558687227616493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143557877869039124818410995 215336816803558687227616493)
      ·
        refine ⟨80751306301334507710356185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215336816803558687227616493 80751306301334507710356185)
        ·
          refine ⟨60563479726000880782767139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80751306301334507710356185 60563479726000880782767139)
          ·
            refine ⟨90845219589001321174150709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60563479726000880782767139 90845219589001321174150709)
            ·
              refine ⟨8516739336468873860076629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90845219589001321174150709 8516739336468873860076629)
              ·
                refine ⟨99805539099244615547773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8516739336468873860076629 99805539099244615547773)
                ·
                  rfl

theorem cell22_2624003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 8].length) (baseStart_2624003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624003 prefixEnd_2624003 := by exact prefixLift 2624003
  have htrace : WordTrace (prefixWord ++ tailWord_2624003) baseStart_2624003 baseEnd_2624003 := by
    simpa [prefixWord, tailWord_2624003, baseEnd_2624003] using wordTrace_append hprefix tailTrace_2624003
  have hstable : (prefixWord ++ tailWord_2624003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624003).length < 2 ^ (prefixWord ++ tailWord_2624003).sum := by decide
  have hdescent : baseEnd_2624003 < baseStart_2624003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624045 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2624045 : Nat := 118140960795 + 2624045 * 2 ^ 59
def prefixEnd_2624045 : Nat := 4983230072969 + 3 ^ 40 * 2624045 * 2
def baseEnd_2624045 : Nat := 898264229351527430379829

theorem tailTrace_2624045 : CollatzResearch.WordTrace tailWord_2624045 prefixEnd_2624045 898264229351527430379829 := by
  unfold tailWord_2624045
  simp only [CollatzResearch.WordTrace]
  refine ⟨95706783778540591051969589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63804522519027060701313059 95706783778540591051969589)
  ·
    refine ⟨8972510979238180411122149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95706783778540591051969589 8972510979238180411122149)
    ·
      refine ⟨1682345808607158827085403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8972510979238180411122149 1682345808607158827085403)
      ·
        refine ⟨2523518712910738240628105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682345808607158827085403 2523518712910738240628105)
        ·
          refine ⟨1892639034683053680471079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523518712910738240628105 1892639034683053680471079)
          ·
            refine ⟨2838958552024580520706619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892639034683053680471079 2838958552024580520706619)
            ·
              refine ⟨4258437828036870781059929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838958552024580520706619 4258437828036870781059929)
              ·
                refine ⟨3193828371027653085794947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258437828036870781059929 3193828371027653085794947)
                ·
                  refine ⟨4790742556541479628692421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193828371027653085794947 4790742556541479628692421)
                  ·
                    refine ⟨898264229351527430379829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4790742556541479628692421 898264229351527430379829)
                    ·
                      rfl

theorem cell22_2624045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2624045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624045 prefixEnd_2624045 := by exact prefixLift 2624045
  have htrace : WordTrace (prefixWord ++ tailWord_2624045) baseStart_2624045 baseEnd_2624045 := by
    simpa [prefixWord, tailWord_2624045, baseEnd_2624045] using wordTrace_append hprefix tailTrace_2624045
  have hstable : (prefixWord ++ tailWord_2624045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624045).length < 2 ^ (prefixWord ++ tailWord_2624045).sum := by decide
  have hdescent : baseEnd_2624045 < baseStart_2624045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624082 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_2624082 : Nat := 118140960795 + 2624082 * 2 ^ 59
def prefixEnd_2624082 : Nat := 4983230072969 + 3 ^ 40 * 2624082 * 2
def baseEnd_2624082 : Nat := 299425631735890555734905

theorem tailTrace_2624082 : CollatzResearch.WordTrace tailWord_2624082 prefixEnd_2624082 299425631735890555734905 := by
  unfold tailWord_2624082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23927033319851636592766625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63805422186271030914044333 23927033319851636592766625)
  ·
    refine ⟨17945274989888727444574969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23927033319851636592766625 17945274989888727444574969)
    ·
      refine ⟨13458956242416545583431227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17945274989888727444574969 13458956242416545583431227)
      ·
        refine ⟨20188434363624818375146841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13458956242416545583431227 20188434363624818375146841)
        ·
          refine ⟨15141325772718613781360131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20188434363624818375146841 15141325772718613781360131)
          ·
            refine ⟨22711988659077920672040197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15141325772718613781360131 22711988659077920672040197)
            ·
              refine ⟨4258497873577110126007537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22711988659077920672040197 4258497873577110126007537)
              ·
                refine ⟨3193873405182832594505653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258497873577110126007537 3193873405182832594505653)
                ·
                  refine ⟨299425631735890555734905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3193873405182832594505653 299425631735890555734905)
                  ·
                    rfl

theorem cell22_2624082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_2624082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624082 prefixEnd_2624082 := by exact prefixLift 2624082
  have htrace : WordTrace (prefixWord ++ tailWord_2624082) baseStart_2624082 baseEnd_2624082 := by
    simpa [prefixWord, tailWord_2624082, baseEnd_2624082] using wordTrace_append hprefix tailTrace_2624082
  have hstable : (prefixWord ++ tailWord_2624082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624082).length < 2 ^ (prefixWord ++ tailWord_2624082).sum := by decide
  have hdescent : baseEnd_2624082 < baseStart_2624082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624174 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2624174 : Nat := 118140960795 + 2624174 * 2 ^ 59
def prefixEnd_2624174 : Nat := 4983230072969 + 3 ^ 40 * 2624174 * 2
def baseEnd_2624174 : Nat := 898308388687814093904433

theorem tailTrace_2624174 : CollatzResearch.WordTrace tailWord_2624174 prefixEnd_2624174 898308388687814093904433 := by
  unfold tailWord_2624174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11963936099384155760426947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63807659196715497388943717 11963936099384155760426947)
  ·
    refine ⟨17945904149076233640640421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11963936099384155760426947 17945904149076233640640421)
    ·
      refine ⟨3364857027951793807620079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17945904149076233640640421 3364857027951793807620079)
      ·
        refine ⟨5047285541927690711430119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364857027951793807620079 5047285541927690711430119)
        ·
          refine ⟨7570928312891536067145179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047285541927690711430119 7570928312891536067145179)
          ·
            refine ⟨11356392469337304100717769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7570928312891536067145179 11356392469337304100717769)
            ·
              refine ⟨8517294352002978075538327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11356392469337304100717769 8517294352002978075538327)
              ·
                refine ⟨12775941528004467113307491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8517294352002978075538327 12775941528004467113307491)
                ·
                  refine ⟨19163912292006700669961237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12775941528004467113307491 19163912292006700669961237)
                  ·
                    refine ⟨898308388687814093904433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19163912292006700669961237 898308388687814093904433)
                    ·
                      rfl

theorem cell22_2624174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2624174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624174 prefixEnd_2624174 := by exact prefixLift 2624174
  have htrace : WordTrace (prefixWord ++ tailWord_2624174) baseStart_2624174 baseEnd_2624174 := by
    simpa [prefixWord, tailWord_2624174, baseEnd_2624174] using wordTrace_append hprefix tailTrace_2624174
  have hstable : (prefixWord ++ tailWord_2624174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624174).length < 2 ^ (prefixWord ++ tailWord_2624174).sum := by decide
  have hdescent : baseEnd_2624174 < baseStart_2624174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624185 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_2624185 : Nat := 118140960795 + 2624185 * 2 ^ 59
def prefixEnd_2624185 : Nat := 4983230072969 + 3 ^ 40 * 2624185 * 2
def baseEnd_2624185 : Nat := 898312154212613731879399

theorem tailTrace_2624185 : CollatzResearch.WordTrace tailWord_2624185 prefixEnd_2624185 898312154212613731879399 := by
  unfold tailWord_2624185
  simp only [CollatzResearch.WordTrace]
  refine ⟨95711889998033394962066009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63807926665355596641377339 95711889998033394962066009)
  ·
    refine ⟨71783917498525046221549507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95711889998033394962066009 71783917498525046221549507)
    ·
      refine ⟨107675876247787569332324261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71783917498525046221549507 107675876247787569332324261)
      ·
        refine ⟨20189226796460169249810799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107675876247787569332324261 20189226796460169249810799)
        ·
          refine ⟨30283840194690253874716199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20189226796460169249810799 30283840194690253874716199)
          ·
            refine ⟨45425760292035380812074299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30283840194690253874716199 45425760292035380812074299)
            ·
              refine ⟨68138640438053071218111449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45425760292035380812074299 68138640438053071218111449)
              ·
                refine ⟨51103980328539803413583587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68138640438053071218111449 51103980328539803413583587)
                ·
                  refine ⟨76655970492809705120375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51103980328539803413583587 76655970492809705120375381)
                  ·
                    refine ⟨898312154212613731879399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76655970492809705120375381 898312154212613731879399)
                    ·
                      rfl

theorem cell22_2624185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_2624185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624185 prefixEnd_2624185 := by exact prefixLift 2624185
  have htrace : WordTrace (prefixWord ++ tailWord_2624185) baseStart_2624185 baseEnd_2624185 := by
    simpa [prefixWord, tailWord_2624185, baseEnd_2624185] using wordTrace_append hprefix tailTrace_2624185
  have hstable : (prefixWord ++ tailWord_2624185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624185).length < 2 ^ (prefixWord ++ tailWord_2624185).sum := by decide
  have hdescent : baseEnd_2624185 < baseStart_2624185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624210 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2624210 : Nat := 118140960795 + 2624210 * 2 ^ 59
def prefixEnd_2624210 : Nat := 4983230072969 + 3 ^ 40 * 2624210 * 2
def baseEnd_2624210 : Nat := 898320712223522000004323

theorem tailTrace_2624210 : CollatzResearch.WordTrace tailWord_2624210 prefixEnd_2624210 898320712223522000004323 := by
  unfold tailWord_2624210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23928200455735706057931521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63808534548628549487817389 23928200455735706057931521)
  ·
    refine ⟨17946150341801779543448641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23928200455735706057931521 17946150341801779543448641)
    ·
      refine ⟨13459612756351334657586481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17946150341801779543448641 13459612756351334657586481)
      ·
        refine ⟨10094709567263500993189861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13459612756351334657586481 10094709567263500993189861)
        ·
          refine ⟨1892758043861906436223099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10094709567263500993189861 1892758043861906436223099)
          ·
            refine ⟨2839137065792859654334649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892758043861906436223099 2839137065792859654334649)
            ·
              refine ⟨2129352799344644740750987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839137065792859654334649 2129352799344644740750987)
              ·
                refine ⟨3194029199016967111126481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129352799344644740750987 3194029199016967111126481)
                ·
                  refine ⟨2395521899262725333344861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194029199016967111126481 2395521899262725333344861)
                  ·
                    refine ⟨898320712223522000004323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2395521899262725333344861 898320712223522000004323)
                    ·
                      rfl

theorem cell22_2624210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2624210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624210 prefixEnd_2624210 := by exact prefixLift 2624210
  have htrace : WordTrace (prefixWord ++ tailWord_2624210) baseStart_2624210 baseEnd_2624210 := by
    simpa [prefixWord, tailWord_2624210, baseEnd_2624210] using wordTrace_append hprefix tailTrace_2624210
  have hstable : (prefixWord ++ tailWord_2624210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624210).length < 2 ^ (prefixWord ++ tailWord_2624210).sum := by decide
  have hdescent : baseEnd_2624210 < baseStart_2624210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624217 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 5]
def baseStart_2624217 : Nat := 118140960795 + 2624217 * 2 ^ 59
def prefixEnd_2624217 : Nat := 4983230072969 + 3 ^ 40 * 2624217 * 2
def baseEnd_2624217 : Nat := 299441036155525438359767

theorem tailTrace_2624217 : CollatzResearch.WordTrace tailWord_2624217 prefixEnd_2624217 299441036155525438359767 := by
  unfold tailWord_2624217
  simp only [CollatzResearch.WordTrace]
  refine ⟨95713057133917464427230905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63808704755944976284820603 95713057133917464427230905)
  ·
    refine ⟨71784792850438098320423179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95713057133917464427230905 71784792850438098320423179)
    ·
      refine ⟨107677189275657147480634769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71784792850438098320423179 107677189275657147480634769)
      ·
        refine ⟨80757891956742860610476077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107677189275657147480634769 80757891956742860610476077)
        ·
          refine ⟨30284209483778572728928529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80757891956742860610476077 30284209483778572728928529)
          ·
            refine ⟨22713157112833929546696397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30284209483778572728928529 22713157112833929546696397)
            ·
              refine ⟨8517433917312723580011149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22713157112833929546696397 8517433917312723580011149)
              ·
                refine ⟨3194037718992271342504181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8517433917312723580011149 3194037718992271342504181)
                ·
                  refine ⟨299441036155525438359767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3194037718992271342504181 299441036155525438359767)
                  ·
                    rfl

theorem cell22_2624217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_2624217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624217 prefixEnd_2624217 := by exact prefixLift 2624217
  have htrace : WordTrace (prefixWord ++ tailWord_2624217) baseStart_2624217 baseEnd_2624217 := by
    simpa [prefixWord, tailWord_2624217, baseEnd_2624217] using wordTrace_append hprefix tailTrace_2624217
  have hstable : (prefixWord ++ tailWord_2624217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624217).length < 2 ^ (prefixWord ++ tailWord_2624217).sum := by decide
  have hdescent : baseEnd_2624217 < baseStart_2624217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624279 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 6]
def baseStart_2624279 : Nat := 118140960795 + 2624279 * 2 ^ 59
def prefixEnd_2624279 : Nat := 4983230072969 + 3 ^ 40 * 2624279 * 2
def baseEnd_2624279 : Nat := 299448110777876273343037

theorem tailTrace_2624279 : CollatzResearch.WordTrace tailWord_2624279 prefixEnd_2624279 299448110777876273343037 := by
  unfold tailWord_2624279
  simp only [CollatzResearch.WordTrace]
  refine ⟨95715318459692849015987891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63810212306461899343991927 95715318459692849015987891)
  ·
    refine ⟨143572977689539273523981837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95715318459692849015987891 143572977689539273523981837)
    ·
      refine ⟨53839866633577227571493189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143572977689539273523981837 53839866633577227571493189)
      ·
        refine ⟨10094974993795730169654973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53839866633577227571493189 10094974993795730169654973)
        ·
          refine ⟨3785615622673398813620615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10094974993795730169654973 3785615622673398813620615)
          ·
            refine ⟨5678423434010098220430923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785615622673398813620615 5678423434010098220430923)
            ·
              refine ⟨8517635151015147330646385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678423434010098220430923 8517635151015147330646385)
              ·
                refine ⟨6388226363261360497984789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8517635151015147330646385 6388226363261360497984789)
                ·
                  refine ⟨299448110777876273343037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6388226363261360497984789 299448110777876273343037)
                  ·
                    rfl

theorem cell22_2624279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 6].length) (baseStart_2624279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624279 prefixEnd_2624279 := by exact prefixLift 2624279
  have htrace : WordTrace (prefixWord ++ tailWord_2624279) baseStart_2624279 baseEnd_2624279 := by
    simpa [prefixWord, tailWord_2624279, baseEnd_2624279] using wordTrace_append hprefix tailTrace_2624279
  have hstable : (prefixWord ++ tailWord_2624279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624279).length < 2 ^ (prefixWord ++ tailWord_2624279).sum := by decide
  have hdescent : baseEnd_2624279 < baseStart_2624279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624296 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_2624296 : Nat := 118140960795 + 2624296 * 2 ^ 59
def prefixEnd_2624296 : Nat := 4983230072969 + 3 ^ 40 * 2624296 * 2
def baseEnd_2624296 : Nat := 299450050593682147451353

theorem tailTrace_2624296 : CollatzResearch.WordTrace tailWord_2624296 prefixEnd_2624296 299450050593682147451353 := by
  unfold tailWord_2624296
  simp only [CollatzResearch.WordTrace]
  refine ⟨47857969250315630459678371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63810625667087507279571161 47857969250315630459678371)
  ·
    refine ⟨71786953875473445689517557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47857969250315630459678371 71786953875473445689517557)
    ·
      refine ⟨6730026925825635533392271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71786953875473445689517557 6730026925825635533392271)
      ·
        refine ⟨10095040388738453300088407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6730026925825635533392271 10095040388738453300088407)
        ·
          refine ⟨15142560583107679950132611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10095040388738453300088407 15142560583107679950132611)
          ·
            refine ⟨22713840874661519925198917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15142560583107679950132611 22713840874661519925198917)
            ·
              refine ⟨4258845163999034985974797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22713840874661519925198917 4258845163999034985974797)
              ·
                refine ⟨1597066936499638119740549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4258845163999034985974797 1597066936499638119740549)
                ·
                  refine ⟨299450050593682147451353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597066936499638119740549 299450050593682147451353)
                  ·
                    rfl

theorem cell22_2624296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_2624296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624296 prefixEnd_2624296 := by exact prefixLift 2624296
  have htrace : WordTrace (prefixWord ++ tailWord_2624296) baseStart_2624296 baseEnd_2624296 := by
    simpa [prefixWord, tailWord_2624296, baseEnd_2624296] using wordTrace_append hprefix tailTrace_2624296
  have hstable : (prefixWord ++ tailWord_2624296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624296).length < 2 ^ (prefixWord ++ tailWord_2624296).sum := by decide
  have hdescent : baseEnd_2624296 < baseStart_2624296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624298 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2624298 : Nat := 118140960795 + 2624298 * 2 ^ 59
def prefixEnd_2624298 : Nat := 4983230072969 + 3 ^ 40 * 2624298 * 2
def baseEnd_2624298 : Nat := 898350836421919103804053

theorem tailTrace_2624298 : CollatzResearch.WordTrace tailWord_2624298 prefixEnd_2624298 898350836421919103804053 := by
  unfold tailWord_2624298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929002861656003815232387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63810674297749343507286365 23929002861656003815232387)
  ·
    refine ⟨35893504292484005722848581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23929002861656003815232387 35893504292484005722848581)
    ·
      refine ⟨6730032054840751073034109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35893504292484005722848581 6730032054840751073034109)
      ·
        refine ⟨2523762020565281652387791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6730032054840751073034109 2523762020565281652387791)
        ·
          refine ⟨3785643030847922478581687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523762020565281652387791 3785643030847922478581687)
          ·
            refine ⟨5678464546271883717872531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785643030847922478581687 5678464546271883717872531)
            ·
              refine ⟨8517696819407825576808797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678464546271883717872531 8517696819407825576808797)
              ·
                refine ⟨3194136307277934591303299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8517696819407825576808797 3194136307277934591303299)
                ·
                  refine ⟨4791204460916901886954949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194136307277934591303299 4791204460916901886954949)
                  ·
                    refine ⟨898350836421919103804053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4791204460916901886954949 898350836421919103804053)
                    ·
                      rfl

theorem cell22_2624298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2624298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624298 prefixEnd_2624298 := by exact prefixLift 2624298
  have htrace : WordTrace (prefixWord ++ tailWord_2624298) baseStart_2624298 baseEnd_2624298 := by
    simpa [prefixWord, tailWord_2624298, baseEnd_2624298] using wordTrace_append hprefix tailTrace_2624298
  have hstable : (prefixWord ++ tailWord_2624298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624298).length < 2 ^ (prefixWord ++ tailWord_2624298).sum := by decide
  have hdescent : baseEnd_2624298 < baseStart_2624298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624307 : List Nat := [1, 1, 1, 2, 6, 2, 9]
def baseStart_2624307 : Nat := 118140960795 + 2624307 * 2 ^ 59
def prefixEnd_2624307 : Nat := 4983230072969 + 3 ^ 40 * 2624307 * 2
def baseEnd_2624307 : Nat := 33272367307623928901075

theorem tailTrace_2624307 : CollatzResearch.WordTrace tailWord_2624307 prefixEnd_2624307 33272367307623928901075 := by
  unfold tailWord_2624307
  simp only [CollatzResearch.WordTrace]
  refine ⟨95716339703591409798007175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63810893135727606532004783 95716339703591409798007175)
  ·
    refine ⟨143574509555387114697010763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95716339703591409798007175 143574509555387114697010763)
    ·
      refine ⟨215361764333080672045516145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143574509555387114697010763 215361764333080672045516145)
      ·
        refine ⟨161521323249810504034137109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215361764333080672045516145 161521323249810504034137109)
        ·
          refine ⟨7571312027334867376600177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161521323249810504034137109 7571312027334867376600177)
          ·
            refine ⟨5678484020501150532450133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7571312027334867376600177 5678484020501150532450133)
            ·
              refine ⟨33272367307623928901075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5678484020501150532450133 33272367307623928901075)
              ·
                rfl

theorem cell22_2624307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 9].length) (baseStart_2624307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624307 prefixEnd_2624307 := by exact prefixLift 2624307
  have htrace : WordTrace (prefixWord ++ tailWord_2624307) baseStart_2624307 baseEnd_2624307 := by
    simpa [prefixWord, tailWord_2624307, baseEnd_2624307] using wordTrace_append hprefix tailTrace_2624307
  have hstable : (prefixWord ++ tailWord_2624307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624307).length < 2 ^ (prefixWord ++ tailWord_2624307).sum := by decide
  have hdescent : baseEnd_2624307 < baseStart_2624307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624352 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_2624352 : Nat := 118140960795 + 2624352 * 2 ^ 59
def prefixEnd_2624352 : Nat := 4983230072969 + 3 ^ 40 * 2624352 * 2
def baseEnd_2624352 : Nat := 299456440575160320984629

theorem tailTrace_2624352 : CollatzResearch.WordTrace tailWord_2624352 prefixEnd_2624352 299456440575160320984629 := by
  unfold tailWord_2624352
  simp only [CollatzResearch.WordTrace]
  refine ⟨47858990494214191241697655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63811987325618921655596873 47858990494214191241697655)
  ·
    refine ⟨71788485741321286862546483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47858990494214191241697655 71788485741321286862546483)
    ·
      refine ⟨107682728611981930293819725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71788485741321286862546483 107682728611981930293819725)
      ·
        refine ⟨40381023229493223860182397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107682728611981930293819725 40381023229493223860182397)
        ·
          refine ⟨15142883711059958947568399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40381023229493223860182397 15142883711059958947568399)
          ·
            refine ⟨22714325566589938421352599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15142883711059958947568399 22714325566589938421352599)
            ·
              refine ⟨34071488349884907632028899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22714325566589938421352599 34071488349884907632028899)
              ·
                refine ⟨51107232524827361448043349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34071488349884907632028899 51107232524827361448043349)
                ·
                  refine ⟨299456440575160320984629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51107232524827361448043349 299456440575160320984629)
                  ·
                    rfl

theorem cell22_2624352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_2624352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624352 prefixEnd_2624352 := by exact prefixLift 2624352
  have htrace : WordTrace (prefixWord ++ tailWord_2624352) baseStart_2624352 baseEnd_2624352 := by
    simpa [prefixWord, tailWord_2624352, baseEnd_2624352] using wordTrace_append hprefix tailTrace_2624352
  have hstable : (prefixWord ++ tailWord_2624352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624352).length < 2 ^ (prefixWord ++ tailWord_2624352).sum := by decide
  have hdescent : baseEnd_2624352 < baseStart_2624352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624367 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_2624367 : Nat := 118140960795 + 2624367 * 2 ^ 59
def prefixEnd_2624367 : Nat := 4983230072969 + 3 ^ 40 * 2624367 * 2
def baseEnd_2624367 : Nat := 898374456532025923828841

theorem tailTrace_2624367 : CollatzResearch.WordTrace tailWord_2624367 prefixEnd_2624367 898374456532025923828841 := by
  unfold tailWord_2624367
  simp only [CollatzResearch.WordTrace]
  refine ⟨95718528083374040045191355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63812352055582693363460903 95718528083374040045191355)
  ·
    refine ⟨143577792125061060067787033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95718528083374040045191355 143577792125061060067787033)
    ·
      refine ⟨107683344093795795050840275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143577792125061060067787033 107683344093795795050840275)
      ·
        refine ⟨161525016140693692576260413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107683344093795795050840275 161525016140693692576260413)
        ·
          refine ⟨60571881052760134716097655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161525016140693692576260413 60571881052760134716097655)
          ·
            refine ⟨90857821579140202074146483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60571881052760134716097655 90857821579140202074146483)
            ·
              refine ⟨136286732368710303111219725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90857821579140202074146483 136286732368710303111219725)
              ·
                refine ⟨51107524638266363666707397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136286732368710303111219725 51107524638266363666707397)
                ·
                  refine ⟨9582660869674943187507637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51107524638266363666707397 9582660869674943187507637)
                  ·
                    refine ⟨898374456532025923828841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9582660869674943187507637 898374456532025923828841)
                    ·
                      rfl

theorem cell22_2624367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_2624367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624367 prefixEnd_2624367 := by exact prefixLift 2624367
  have htrace : WordTrace (prefixWord ++ tailWord_2624367) baseStart_2624367 baseEnd_2624367 := by
    simpa [prefixWord, tailWord_2624367, baseEnd_2624367] using wordTrace_append hprefix tailTrace_2624367
  have hstable : (prefixWord ++ tailWord_2624367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624367).length < 2 ^ (prefixWord ++ tailWord_2624367).sum := by decide
  have hdescent : baseEnd_2624367 < baseStart_2624367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624373 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2624373 : Nat := 118140960795 + 2624373 * 2 ^ 59
def prefixEnd_2624373 : Nat := 4983230072969 + 3 ^ 40 * 2624373 * 2
def baseEnd_2624373 : Nat := 898376510454643908178823

theorem tailTrace_2624373 : CollatzResearch.WordTrace tailWord_2624373 prefixEnd_2624373 898376510454643908178823 := by
  unfold tailWord_2624373
  simp only [CollatzResearch.WordTrace]
  refine ⟨95718746921352303069909773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63812497947568202046606515 95718746921352303069909773)
  ·
    refine ⟨35894530095507113651216165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95718746921352303069909773 35894530095507113651216165)
    ·
      refine ⟨6730224392907583809603031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35894530095507113651216165 6730224392907583809603031)
      ·
        refine ⟨10095336589361375714404547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6730224392907583809603031 10095336589361375714404547)
        ·
          refine ⟨15143004884042063571606821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10095336589361375714404547 15143004884042063571606821)
          ·
            refine ⟨2839313415757886919676279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15143004884042063571606821 2839313415757886919676279)
            ·
              refine ⟨4258970123636830379514419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839313415757886919676279 4258970123636830379514419)
              ·
                refine ⟨6388455185455245569271629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258970123636830379514419 6388455185455245569271629)
                ·
                  refine ⟨2395670694545717088476861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6388455185455245569271629 2395670694545717088476861)
                  ·
                    refine ⟨898376510454643908178823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2395670694545717088476861 898376510454643908178823)
                    ·
                      rfl

theorem cell22_2624373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2624373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624373 prefixEnd_2624373 := by exact prefixLift 2624373
  have htrace : WordTrace (prefixWord ++ tailWord_2624373) baseStart_2624373 baseEnd_2624373 := by
    simpa [prefixWord, tailWord_2624373, baseEnd_2624373] using wordTrace_append hprefix tailTrace_2624373
  have hstable : (prefixWord ++ tailWord_2624373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624373).length < 2 ^ (prefixWord ++ tailWord_2624373).sum := by decide
  have hdescent : baseEnd_2624373 < baseStart_2624373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624446 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2624446 : Nat := 118140960795 + 2624446 * 2 ^ 59
def prefixEnd_2624446 : Nat := 4983230072969 + 3 ^ 40 * 2624446 * 2
def baseEnd_2624446 : Nat := 898401499846496051103599

theorem tailTrace_2624446 : CollatzResearch.WordTrace tailWord_2624446 prefixEnd_2624446 898401499846496051103599 := by
  unfold tailWord_2624446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965176181260979567164649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63814272966725224358211461 11965176181260979567164649)
  ·
    refine ⟨8973882135945734675373487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11965176181260979567164649 8973882135945734675373487)
    ·
      refine ⟨13460823203918602013060231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8973882135945734675373487 13460823203918602013060231)
      ·
        refine ⟨20191234805877903019590347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13460823203918602013060231 20191234805877903019590347)
        ·
          refine ⟨30286852208816854529385521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20191234805877903019590347 30286852208816854529385521)
          ·
            refine ⟨22715139156612640897039141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30286852208816854529385521 22715139156612640897039141)
            ·
              refine ⟨4259088591864870168194839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22715139156612640897039141 4259088591864870168194839)
              ·
                refine ⟨6388632887797305252292259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259088591864870168194839 6388632887797305252292259)
                ·
                  refine ⟨9582949331695957878438389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388632887797305252292259 9582949331695957878438389)
                  ·
                    refine ⟨898401499846496051103599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9582949331695957878438389 898401499846496051103599)
                    ·
                      rfl

theorem cell22_2624446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2624446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624446 prefixEnd_2624446 := by exact prefixLift 2624446
  have htrace : WordTrace (prefixWord ++ tailWord_2624446) baseStart_2624446 baseEnd_2624446 := by
    simpa [prefixWord, tailWord_2624446, baseEnd_2624446] using wordTrace_append hprefix tailTrace_2624446
  have hstable : (prefixWord ++ tailWord_2624446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624446).length < 2 ^ (prefixWord ++ tailWord_2624446).sum := by decide
  have hdescent : baseEnd_2624446 < baseStart_2624446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624510 : List Nat := [4, 2, 2, 2, 2, 2, 2, 6]
def baseStart_2624510 : Nat := 118140960795 + 2624510 * 2 ^ 59
def prefixEnd_2624510 : Nat := 4983230072969 + 3 ^ 40 * 2624510 * 2
def baseEnd_2624510 : Nat := 99824823150491246389267

theorem tailTrace_2624510 : CollatzResearch.WordTrace tailWord_2624510 prefixEnd_2624510 99824823150491246389267 := by
  unfold tailWord_2624510
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965467965231996933455873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63815829147903983645097989 11965467965231996933455873)
  ·
    refine ⟨8974100973923997700091905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11965467965231996933455873 8974100973923997700091905)
    ·
      refine ⟨6730575730442998275068929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8974100973923997700091905 6730575730442998275068929)
      ·
        refine ⟨5047931797832248706301697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6730575730442998275068929 5047931797832248706301697)
        ·
          refine ⟨3785948848374186529726273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5047931797832248706301697 3785948848374186529726273)
          ·
            refine ⟨2839461636280639897294705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3785948848374186529726273 2839461636280639897294705)
            ·
              refine ⟨2129596227210479922971029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839461636280639897294705 2129596227210479922971029)
              ·
                refine ⟨99824823150491246389267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2129596227210479922971029 99824823150491246389267)
                ·
                  rfl

theorem cell22_2624510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_2624510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624510 prefixEnd_2624510 := by exact prefixLift 2624510
  have htrace : WordTrace (prefixWord ++ tailWord_2624510) baseStart_2624510 baseEnd_2624510 := by
    simpa [prefixWord, tailWord_2624510, baseEnd_2624510] using wordTrace_append hprefix tailTrace_2624510
  have hstable : (prefixWord ++ tailWord_2624510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624510).length < 2 ^ (prefixWord ++ tailWord_2624510).sum := by decide
  have hdescent : baseEnd_2624510 < baseStart_2624510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624568 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_2624568 : Nat := 118140960795 + 2624568 * 2 ^ 59
def prefixEnd_2624568 : Nat := 4983230072969 + 3 ^ 40 * 2624568 * 2
def baseEnd_2624568 : Nat := 898443262939728399553225

theorem tailTrace_2624568 : CollatzResearch.WordTrace tailWord_2624568 prefixEnd_2624568 898443262939728399553225 := by
  unfold tailWord_2624568
  simp only [CollatzResearch.WordTrace]
  refine ⟨47862929577822925686629179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63817239437097234248838905 47862929577822925686629179)
  ·
    refine ⟨71794394366734388529943769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47862929577822925686629179 71794394366734388529943769)
    ·
      refine ⟨53845795775050791397457827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71794394366734388529943769 53845795775050791397457827)
      ·
        refine ⟨80768693662576187096186741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53845795775050791397457827 80768693662576187096186741)
        ·
          refine ⟨7572065030866517540267507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80768693662576187096186741 7572065030866517540267507)
          ·
            refine ⟨11358097546299776310401261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7572065030866517540267507 11358097546299776310401261)
            ·
              refine ⟨4259286579862416116400473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11358097546299776310401261 4259286579862416116400473)
              ·
                refine ⟨3194464934896812087300355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259286579862416116400473 3194464934896812087300355)
                ·
                  refine ⟨4791697402345218130950533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194464934896812087300355 4791697402345218130950533)
                  ·
                    refine ⟨898443262939728399553225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4791697402345218130950533 898443262939728399553225)
                    ·
                      rfl

theorem cell22_2624568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_2624568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624568 prefixEnd_2624568 := by exact prefixLift 2624568
  have htrace : WordTrace (prefixWord ++ tailWord_2624568) baseStart_2624568 baseEnd_2624568 := by
    simpa [prefixWord, tailWord_2624568, baseEnd_2624568] using wordTrace_append hprefix tailTrace_2624568
  have hstable : (prefixWord ++ tailWord_2624568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624568).length < 2 ^ (prefixWord ++ tailWord_2624568).sum := by decide
  have hdescent : baseEnd_2624568 < baseStart_2624568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624581 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_2624581 : Nat := 118140960795 + 2624581 * 2 ^ 59
def prefixEnd_2624581 : Nat := 4983230072969 + 3 ^ 40 * 2624581 * 2
def baseEnd_2624581 : Nat := 898447713105400698978185

theorem tailTrace_2624581 : CollatzResearch.WordTrace tailWord_2624581 prefixEnd_2624581 898447713105400698978185 := by
  unfold tailWord_2624581
  simp only [CollatzResearch.WordTrace]
  refine ⟨95726333304598754593481597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63817555536399169728987731 95726333304598754593481597)
  ·
    refine ⟨35897374989224532972555599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95726333304598754593481597 35897374989224532972555599)
    ·
      refine ⟨53846062483836799458833399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35897374989224532972555599 53846062483836799458833399)
      ·
        refine ⟨80769093725755199188250099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53846062483836799458833399 80769093725755199188250099)
        ·
          refine ⟨121153640588632798782375149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80769093725755199188250099 121153640588632798782375149)
          ·
            refine ⟨45432615220737299543390681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121153640588632798782375149 45432615220737299543390681)
            ·
              refine ⟨34074461415552974657543011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45432615220737299543390681 34074461415552974657543011)
              ·
                refine ⟨51111692123329461986314517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34074461415552974657543011 51111692123329461986314517)
                ·
                  refine ⟨2395860568281068530608493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51111692123329461986314517 2395860568281068530608493)
                  ·
                    refine ⟨898447713105400698978185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2395860568281068530608493 898447713105400698978185)
                    ·
                      rfl

theorem cell22_2624581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_2624581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624581 prefixEnd_2624581 := by exact prefixLift 2624581
  have htrace : WordTrace (prefixWord ++ tailWord_2624581) baseStart_2624581 baseEnd_2624581 := by
    simpa [prefixWord, tailWord_2624581, baseEnd_2624581] using wordTrace_append hprefix tailTrace_2624581
  have hstable : (prefixWord ++ tailWord_2624581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624581).length < 2 ^ (prefixWord ++ tailWord_2624581).sum := by decide
  have hdescent : baseEnd_2624581 < baseStart_2624581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624656 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_2624656 : Nat := 118140960795 + 2624656 * 2 ^ 59
def prefixEnd_2624656 : Nat := 4983230072969 + 3 ^ 40 * 2624656 * 2
def baseEnd_2624656 : Nat := 299491129046041834450985

theorem tailTrace_2624656 : CollatzResearch.WordTrace tailWord_2624656 prefixEnd_2624656 299491129046041834450985 := by
  unfold tailWord_2624656
  simp only [CollatzResearch.WordTrace]
  refine ⟨47864534389663521201230911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63819379186218028268307881 47864534389663521201230911)
  ·
    refine ⟨71796801584495281801846367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47864534389663521201230911 71796801584495281801846367)
    ·
      refine ⟨107695202376742922702769551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71796801584495281801846367 107695202376742922702769551)
      ·
        refine ⟨161542803565114384054154327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107695202376742922702769551 161542803565114384054154327)
        ·
          refine ⟨242314205347671576081231491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161542803565114384054154327 242314205347671576081231491)
          ·
            refine ⟨363471308021507364121847237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242314205347671576081231491 363471308021507364121847237)
            ·
              refine ⟨68150870254032630772846357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 363471308021507364121847237 68150870254032630772846357)
              ·
                refine ⟨3194572043157779567477173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68150870254032630772846357 3194572043157779567477173)
                ·
                  refine ⟨299491129046041834450985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3194572043157779567477173 299491129046041834450985)
                  ·
                    rfl

theorem cell22_2624656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_2624656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624656 prefixEnd_2624656 := by exact prefixLift 2624656
  have htrace : WordTrace (prefixWord ++ tailWord_2624656) baseStart_2624656 baseEnd_2624656 := by
    simpa [prefixWord, tailWord_2624656, baseEnd_2624656] using wordTrace_append hprefix tailTrace_2624656
  have hstable : (prefixWord ++ tailWord_2624656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624656).length < 2 ^ (prefixWord ++ tailWord_2624656).sum := by decide
  have hdescent : baseEnd_2624656 < baseStart_2624656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624701 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2624701 : Nat := 118140960795 + 2624701 * 2 ^ 59
def prefixEnd_2624701 : Nat := 4983230072969 + 3 ^ 40 * 2624701 * 2
def baseEnd_2624701 : Nat := 299496263852586795325939

theorem tailTrace_2624701 : CollatzResearch.WordTrace tailWord_2624701 prefixEnd_2624701 299496263852586795325939 := by
  unfold tailWord_2624701
  simp only [CollatzResearch.WordTrace]
  refine ⟨95730710064164015087849957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63820473376109343391899971 95730710064164015087849957)
  ·
    refine ⟨17949508137030752828971867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95730710064164015087849957 17949508137030752828971867)
    ·
      refine ⟨26924262205546129243457801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17949508137030752828971867 26924262205546129243457801)
      ·
        refine ⟨20193196654159596932593351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26924262205546129243457801 20193196654159596932593351)
        ·
          refine ⟨30289794981239395398890027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20193196654159596932593351 30289794981239395398890027)
          ·
            refine ⟨45434692471859093098335041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30289794981239395398890027 45434692471859093098335041)
            ·
              refine ⟨34076019353894319823751281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45434692471859093098335041 34076019353894319823751281)
              ·
                refine ⟨25557014515420739867813461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34076019353894319823751281 25557014515420739867813461)
                ·
                  refine ⟨299496263852586795325939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25557014515420739867813461 299496263852586795325939)
                  ·
                    rfl

theorem cell22_2624701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2624701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624701 prefixEnd_2624701 := by exact prefixLift 2624701
  have htrace : WordTrace (prefixWord ++ tailWord_2624701) baseStart_2624701 baseEnd_2624701 := by
    simpa [prefixWord, tailWord_2624701, baseEnd_2624701] using wordTrace_append hprefix tailTrace_2624701
  have hstable : (prefixWord ++ tailWord_2624701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624701).length < 2 ^ (prefixWord ++ tailWord_2624701).sum := by decide
  have hdescent : baseEnd_2624701 < baseStart_2624701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624703 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 1, 4]
def baseStart_2624703 : Nat := 118140960795 + 2624703 * 2 ^ 59
def prefixEnd_2624703 : Nat := 4983230072969 + 3 ^ 40 * 2624703 * 2
def baseEnd_2624703 : Nat := 898489476198633047427811

theorem tailTrace_2624703 : CollatzResearch.WordTrace tailWord_2624703 prefixEnd_2624703 898489476198633047427811 := by
  unfold tailWord_2624703
  simp only [CollatzResearch.WordTrace]
  refine ⟨95730783010156769429422763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63820522006771179619615175 95730783010156769429422763)
  ·
    refine ⟨143596174515235154144134145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95730783010156769429422763 143596174515235154144134145)
    ·
      refine ⟨107697130886426365608100609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143596174515235154144134145 107697130886426365608100609)
      ·
        refine ⟨80772848164819774206075457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107697130886426365608100609 80772848164819774206075457)
        ·
          refine ⟨60579636123614830654556593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80772848164819774206075457 60579636123614830654556593)
          ·
            refine ⟨45434727092711122990917445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60579636123614830654556593 45434727092711122990917445)
            ·
              refine ⟨8519011329883335560797021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45434727092711122990917445 8519011329883335560797021)
              ·
                refine ⟨3194629248706250835298883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519011329883335560797021 3194629248706250835298883)
                ·
                  refine ⟨4791943873059376252948325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194629248706250835298883 4791943873059376252948325)
                  ·
                    refine ⟨898489476198633047427811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4791943873059376252948325 898489476198633047427811)
                    ·
                      rfl

theorem cell22_2624703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_2624703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624703 prefixEnd_2624703 := by exact prefixLift 2624703
  have htrace : WordTrace (prefixWord ++ tailWord_2624703) baseStart_2624703 baseEnd_2624703 := by
    simpa [prefixWord, tailWord_2624703, baseEnd_2624703] using wordTrace_append hprefix tailTrace_2624703
  have hstable : (prefixWord ++ tailWord_2624703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624703).length < 2 ^ (prefixWord ++ tailWord_2624703).sum := by decide
  have hdescent : baseEnd_2624703 < baseStart_2624703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624724 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2624724 : Nat := 118140960795 + 2624724 * 2 ^ 59
def prefixEnd_2624724 : Nat := 4983230072969 + 3 ^ 40 * 2624724 * 2
def baseEnd_2624724 : Nat := 299498888309265330884249

theorem tailTrace_2624724 : CollatzResearch.WordTrace tailWord_2624724 prefixEnd_2624724 299498888309265330884249 := by
  unfold tailWord_2624724
  simp only [CollatzResearch.WordTrace]
  refine ⟨47865774471540345007968613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63821032628720460010624817 47865774471540345007968613)
  ·
    refine ⟨8974832713413814688994115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47865774471540345007968613 8974832713413814688994115)
    ·
      refine ⟨13462249070120722033491173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8974832713413814688994115 13462249070120722033491173)
      ·
        refine ⟨2524171700647635381279595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13462249070120722033491173 2524171700647635381279595)
        ·
          refine ⟨3786257550971453071919393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524171700647635381279595 3786257550971453071919393)
          ·
            refine ⟨2839693163228589803939545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786257550971453071919393 2839693163228589803939545)
            ·
              refine ⟨2129769872421442352954659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839693163228589803939545 2129769872421442352954659)
              ·
                refine ⟨3194654808632163529431989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129769872421442352954659 3194654808632163529431989)
                ·
                  refine ⟨299498888309265330884249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3194654808632163529431989 299498888309265330884249)
                  ·
                    rfl

theorem cell22_2624724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2624724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624724 prefixEnd_2624724 := by exact prefixLift 2624724
  have htrace : WordTrace (prefixWord ++ tailWord_2624724) baseStart_2624724 baseEnd_2624724 := by
    simpa [prefixWord, tailWord_2624724, baseEnd_2624724] using wordTrace_append hprefix tailTrace_2624724
  have hstable : (prefixWord ++ tailWord_2624724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624724).length < 2 ^ (prefixWord ++ tailWord_2624724).sum := by decide
  have hdescent : baseEnd_2624724 < baseStart_2624724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624748 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_2624748 : Nat := 118140960795 + 2624748 * 2 ^ 59
def prefixEnd_2624748 : Nat := 4983230072969 + 3 ^ 40 * 2624748 * 2
def baseEnd_2624748 : Nat := 898504880618267930052673

theorem tailTrace_2624748 : CollatzResearch.WordTrace tailWord_2624748 prefixEnd_2624748 898504880618267930052673 := by
  unfold tailWord_2624748
  simp only [CollatzResearch.WordTrace]
  refine ⟨47866212147496871057405449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63821616196662494743207265 47866212147496871057405449)
  ·
    refine ⟨35899659110622653293054087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47866212147496871057405449 35899659110622653293054087)
    ·
      refine ⟨53849488665933979939581131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35899659110622653293054087 53849488665933979939581131)
      ·
        refine ⟨80774232998900969909371697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53849488665933979939581131 80774232998900969909371697)
        ·
          refine ⟨60580674749175727432028773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80774232998900969909371697 60580674749175727432028773)
          ·
            refine ⟨11358876515470448893505395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60580674749175727432028773 11358876515470448893505395)
            ·
              refine ⟨17038314773205673340258093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11358876515470448893505395 17038314773205673340258093)
              ·
                refine ⟨6389368039952127502596785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17038314773205673340258093 6389368039952127502596785)
                ·
                  refine ⟨4792026029964095626947589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389368039952127502596785 4792026029964095626947589)
                  ·
                    refine ⟨898504880618267930052673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792026029964095626947589 898504880618267930052673)
                    ·
                      rfl

theorem cell22_2624748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_2624748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624748 prefixEnd_2624748 := by exact prefixLift 2624748
  have htrace : WordTrace (prefixWord ++ tailWord_2624748) baseStart_2624748 baseEnd_2624748 := by
    simpa [prefixWord, tailWord_2624748, baseEnd_2624748] using wordTrace_append hprefix tailTrace_2624748
  have hstable : (prefixWord ++ tailWord_2624748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624748).length < 2 ^ (prefixWord ++ tailWord_2624748).sum := by decide
  have hdescent : baseEnd_2624748 < baseStart_2624748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624825 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 7]
def baseStart_2624825 : Nat := 118140960795 + 2624825 * 2 ^ 59
def prefixEnd_2624825 : Nat := 4983230072969 + 3 ^ 40 * 2624825 * 2
def baseEnd_2624825 : Nat := 299510413097288465292479

theorem tailTrace_2624825 : CollatzResearch.WordTrace tailWord_2624825 prefixEnd_2624825 299510413097288465292479 := by
  unfold tailWord_2624825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95735232715714784265363929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63823488477143189510242619 95735232715714784265363929)
  ·
    refine ⟨71801424536786088199022947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95735232715714784265363929 71801424536786088199022947)
    ·
      refine ⟨107702136805179132298534421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71801424536786088199022947 107702136805179132298534421)
      ·
        refine ⟨5048537662742771826493801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107702136805179132298534421 5048537662742771826493801)
        ·
          refine ⟨3786403247057078869870351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5048537662742771826493801 3786403247057078869870351)
          ·
            refine ⟨5679604870585618304805527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786403247057078869870351 5679604870585618304805527)
            ·
              refine ⟨8519407305878427457208291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679604870585618304805527 8519407305878427457208291)
              ·
                refine ⟨12779110958817641185812437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8519407305878427457208291 12779110958817641185812437)
                ·
                  refine ⟨299510413097288465292479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12779110958817641185812437 299510413097288465292479)
                  ·
                    rfl

theorem cell22_2624825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_2624825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624825 prefixEnd_2624825 := by exact prefixLift 2624825
  have htrace : WordTrace (prefixWord ++ tailWord_2624825) baseStart_2624825 baseEnd_2624825 := by
    simpa [prefixWord, tailWord_2624825, baseEnd_2624825] using wordTrace_append hprefix tailTrace_2624825
  have hstable : (prefixWord ++ tailWord_2624825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624825).length < 2 ^ (prefixWord ++ tailWord_2624825).sum := by decide
  have hdescent : baseEnd_2624825 < baseStart_2624825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624829 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2624829 : Nat := 118140960795 + 2624829 * 2 ^ 59
def prefixEnd_2624829 : Nat := 4983230072969 + 3 ^ 40 * 2624829 * 2
def baseEnd_2624829 : Nat := 898532608573610718777425

theorem tailTrace_2624829 : CollatzResearch.WordTrace tailWord_2624829 prefixEnd_2624829 898532608573610718777425 := by
  unfold tailWord_2624829
  simp only [CollatzResearch.WordTrace]
  refine ⟨95735378607700292948509541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63823585738466861965673027 95735378607700292948509541)
  ·
    refine ⟨17950383488943804927845539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95735378607700292948509541 17950383488943804927845539)
    ·
      refine ⟨26925575233415707391768309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17950383488943804927845539 26925575233415707391768309)
      ·
        refine ⟨2524272678132722567978279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26925575233415707391768309 2524272678132722567978279)
        ·
          refine ⟨3786409017199083851967419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524272678132722567978279 3786409017199083851967419)
          ·
            refine ⟨5679613525798625777951129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786409017199083851967419 5679613525798625777951129)
            ·
              refine ⟨4259710144348969333463347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679613525798625777951129 4259710144348969333463347)
              ·
                refine ⟨6389565216523454000195021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259710144348969333463347 6389565216523454000195021)
                ·
                  refine ⟨2396086956196295250073133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6389565216523454000195021 2396086956196295250073133)
                  ·
                    refine ⟨898532608573610718777425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396086956196295250073133 898532608573610718777425)
                    ·
                      rfl

theorem cell22_2624829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2624829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624829 prefixEnd_2624829 := by exact prefixLift 2624829
  have htrace : WordTrace (prefixWord ++ tailWord_2624829) baseStart_2624829 baseEnd_2624829 := by
    simpa [prefixWord, tailWord_2624829, baseEnd_2624829] using wordTrace_append hprefix tailTrace_2624829
  have hstable : (prefixWord ++ tailWord_2624829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624829).length < 2 ^ (prefixWord ++ tailWord_2624829).sum := by decide
  have hdescent : baseEnd_2624829 < baseStart_2624829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624855 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2624855 : Nat := 118140960795 + 2624855 * 2 ^ 59
def prefixEnd_2624855 : Nat := 4983230072969 + 3 ^ 40 * 2624855 * 2
def baseEnd_2624855 : Nat := 898541508904955317627345

theorem tailTrace_2624855 : CollatzResearch.WordTrace tailWord_2624855 prefixEnd_2624855 898541508904955317627345 := by
  unfold tailWord_2624855
  simp only [CollatzResearch.WordTrace]
  refine ⟨95736326905606099388956019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63824217937070732925970679 95736326905606099388956019)
  ·
    refine ⟨143604490358409149083434029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95736326905606099388956019 143604490358409149083434029)
    ·
      refine ⟨53851683884403430906287761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143604490358409149083434029 53851683884403430906287761)
      ·
        refine ⟨40388762913302573179715821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53851683884403430906287761 40388762913302573179715821)
        ·
          refine ⟨15145786092488464942393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40388762913302573179715821 15145786092488464942393433)
          ·
            refine ⟨11359339569366348706795075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15145786092488464942393433 11359339569366348706795075)
            ·
              refine ⟨17039009354049523060192613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11359339569366348706795075 17039009354049523060192613)
              ·
                refine ⟨3194814253884285573786115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17039009354049523060192613 3194814253884285573786115)
                ·
                  refine ⟨4792221380826428360679173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194814253884285573786115 4792221380826428360679173)
                  ·
                    refine ⟨898541508904955317627345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792221380826428360679173 898541508904955317627345)
                    ·
                      rfl

theorem cell22_2624855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2624855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624855 prefixEnd_2624855 := by exact prefixLift 2624855
  have htrace : WordTrace (prefixWord ++ tailWord_2624855) baseStart_2624855 baseEnd_2624855 := by
    simpa [prefixWord, tailWord_2624855, baseEnd_2624855] using wordTrace_append hprefix tailTrace_2624855
  have hstable : (prefixWord ++ tailWord_2624855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624855).length < 2 ^ (prefixWord ++ tailWord_2624855).sum := by decide
  have hdescent : baseEnd_2624855 < baseStart_2624855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624887 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 4]
def baseStart_2624887 : Nat := 118140960795 + 2624887 * 2 ^ 59
def prefixEnd_2624887 : Nat := 4983230072969 + 3 ^ 40 * 2624887 * 2
def baseEnd_2624887 : Nat := 299517487719639300275749

theorem tailTrace_2624887 : CollatzResearch.WordTrace tailWord_2624887 prefixEnd_2624887 299517487719639300275749 := by
  unfold tailWord_2624887
  simp only [CollatzResearch.WordTrace]
  refine ⟨95737494041490168854120915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63824996027660112569413943 95737494041490168854120915)
  ·
    refine ⟨143606241062235253281181373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95737494041490168854120915 143606241062235253281181373)
    ·
      refine ⟨53852340398338219980443015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143606241062235253281181373 53852340398338219980443015)
      ·
        refine ⟨80778510597507329970664523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53852340398338219980443015 80778510597507329970664523)
        ·
          refine ⟨121167765896260994955996785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80778510597507329970664523 121167765896260994955996785)
          ·
            refine ⟨90875824422195746216997589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121167765896260994955996785 90875824422195746216997589)
            ·
              refine ⟨2129902134895212801960881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90875824422195746216997589 2129902134895212801960881)
              ·
                refine ⟨1597426601171409601470661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129902134895212801960881 1597426601171409601470661)
                ·
                  refine ⟨299517487719639300275749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597426601171409601470661 299517487719639300275749)
                  ·
                    rfl

theorem cell22_2624887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 4].length) (baseStart_2624887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624887 prefixEnd_2624887 := by exact prefixLift 2624887
  have htrace : WordTrace (prefixWord ++ tailWord_2624887) baseStart_2624887 baseEnd_2624887 := by
    simpa [prefixWord, tailWord_2624887, baseEnd_2624887] using wordTrace_append hprefix tailTrace_2624887
  have hstable : (prefixWord ++ tailWord_2624887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624887).length < 2 ^ (prefixWord ++ tailWord_2624887).sum := by decide
  have hdescent : baseEnd_2624887 < baseStart_2624887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624936 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2624936 : Nat := 118140960795 + 2624936 * 2 ^ 59
def prefixEnd_2624936 : Nat := 4983230072969 + 3 ^ 40 * 2624936 * 2
def baseEnd_2624936 : Nat := 898569236860298106352097

theorem tailTrace_2624936 : CollatzResearch.WordTrace tailWord_2624936 prefixEnd_2624936 898569236860298106352097 := by
  unfold tailWord_2624936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47869640609156325111327331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63826187478875100148436441 47869640609156325111327331)
  ·
    refine ⟨71804460913734487666990997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47869640609156325111327331 71804460913734487666990997)
    ·
      refine ⟨3365834105331304109390203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71804460913734487666990997 3365834105331304109390203)
      ·
        refine ⟨5048751157996956164085305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365834105331304109390203 5048751157996956164085305)
        ·
          refine ⟨3786563368497717123063979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5048751157996956164085305 3786563368497717123063979)
          ·
            refine ⟨5679845052746575684595969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786563368497717123063979 5679845052746575684595969)
            ·
              refine ⟨4259883789559931763446977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679845052746575684595969 4259883789559931763446977)
              ·
                refine ⟨3194912842169948822585233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259883789559931763446977 3194912842169948822585233)
                ·
                  refine ⟨2396184631627461616938925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194912842169948822585233 2396184631627461616938925)
                  ·
                    refine ⟨898569236860298106352097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396184631627461616938925 898569236860298106352097)
                    ·
                      rfl

theorem cell22_2624936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2624936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624936 prefixEnd_2624936 := by exact prefixLift 2624936
  have htrace : WordTrace (prefixWord ++ tailWord_2624936) baseStart_2624936 baseEnd_2624936 := by
    simpa [prefixWord, tailWord_2624936, baseEnd_2624936] using wordTrace_append hprefix tailTrace_2624936
  have hstable : (prefixWord ++ tailWord_2624936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624936).length < 2 ^ (prefixWord ++ tailWord_2624936).sum := by decide
  have hdescent : baseEnd_2624936 < baseStart_2624936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624943 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 7]
def baseStart_2624943 : Nat := 118140960795 + 2624943 * 2 ^ 59
def prefixEnd_2624943 : Nat := 4983230072969 + 3 ^ 40 * 2624943 * 2
def baseEnd_2624943 : Nat := 299523877701117473809025

theorem tailTrace_2624943 : CollatzResearch.WordTrace tailWord_2624943 prefixEnd_2624943 299523877701117473809025 := by
  unfold tailWord_2624943
  simp only [CollatzResearch.WordTrace]
  refine ⟨95739536529287290418159483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63826357686191526945439655 95739536529287290418159483)
  ·
    refine ⟨143609304793930935627239225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95739536529287290418159483 143609304793930935627239225)
    ·
      refine ⟨107706978595448201720429419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143609304793930935627239225 107706978595448201720429419)
      ·
        refine ⟨161560467893172302580644129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107706978595448201720429419 161560467893172302580644129)
        ·
          refine ⟨121170350919879226935483097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161560467893172302580644129 121170350919879226935483097)
          ·
            refine ⟨90877763189909420201612323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121170350919879226935483097 90877763189909420201612323)
            ·
              refine ⟨136316644784864130302418485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90877763189909420201612323 136316644784864130302418485)
              ·
                refine ⟨12779685448581012215851733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136316644784864130302418485 12779685448581012215851733)
                ·
                  refine ⟨299523877701117473809025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12779685448581012215851733 299523877701117473809025)
                  ·
                    rfl

theorem cell22_2624943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_2624943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624943 prefixEnd_2624943 := by exact prefixLift 2624943
  have htrace : WordTrace (prefixWord ++ tailWord_2624943) baseStart_2624943 baseEnd_2624943 := by
    simpa [prefixWord, tailWord_2624943, baseEnd_2624943] using wordTrace_append hprefix tailTrace_2624943
  have hstable : (prefixWord ++ tailWord_2624943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624943).length < 2 ^ (prefixWord ++ tailWord_2624943).sum := by decide
  have hdescent : baseEnd_2624943 < baseStart_2624943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624960 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_2624960 : Nat := 118140960795 + 2624960 * 2 ^ 59
def prefixEnd_2624960 : Nat := 4983230072969 + 3 ^ 40 * 2624960 * 2
def baseEnd_2624960 : Nat := 299525817516923347917341

theorem tailTrace_2624960 : CollatzResearch.WordTrace tailWord_2624960 prefixEnd_2624960 299525817516923347917341 := by
  unfold tailWord_2624960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47870078285112851160764167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63826771046817134881018889 47870078285112851160764167)
  ·
    refine ⟨71805117427669276741146251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47870078285112851160764167 71805117427669276741146251)
    ·
      refine ⟨107707676141503915111719377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71805117427669276741146251 107707676141503915111719377)
      ·
        refine ⟨80780757106127936333789533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107707676141503915111719377 80780757106127936333789533)
        ·
          refine ⟨30292783914797976125171075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80780757106127936333789533 30292783914797976125171075)
          ·
            refine ⟨45439175872196964187756613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30292783914797976125171075 45439175872196964187756613)
            ·
              refine ⟨8519845476036930785204365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45439175872196964187756613 8519845476036930785204365)
              ·
                refine ⟨3194942053513849044451637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519845476036930785204365 3194942053513849044451637)
                ·
                  refine ⟨299525817516923347917341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3194942053513849044451637 299525817516923347917341)
                  ·
                    rfl

theorem cell22_2624960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_2624960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624960 prefixEnd_2624960 := by exact prefixLift 2624960
  have htrace : WordTrace (prefixWord ++ tailWord_2624960) baseStart_2624960 baseEnd_2624960 := by
    simpa [prefixWord, tailWord_2624960, baseEnd_2624960] using wordTrace_append hprefix tailTrace_2624960
  have hstable : (prefixWord ++ tailWord_2624960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624960).length < 2 ^ (prefixWord ++ tailWord_2624960).sum := by decide
  have hdescent : baseEnd_2624960 < baseStart_2624960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624964 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2624964 : Nat := 118140960795 + 2624964 * 2 ^ 59
def prefixEnd_2624964 : Nat := 4983230072969 + 3 ^ 40 * 2624964 * 2
def baseEnd_2624964 : Nat := 898578821832515366652011

theorem tailTrace_2624964 : CollatzResearch.WordTrace tailWord_2624964 prefixEnd_2624964 898578821832515366652011 := by
  unfold tailWord_2624964
  simp only [CollatzResearch.WordTrace]
  refine ⟨47870151231105605502336973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63826868308140807336449297 47870151231105605502336973)
  ·
    refine ⟨17951306711664602063376365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47870151231105605502336973 17951306711664602063376365)
    ·
      refine ⟨6731740016874225773766137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17951306711664602063376365 6731740016874225773766137)
      ·
        refine ⟨5048805012655669330324603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6731740016874225773766137 5048805012655669330324603)
        ·
          refine ⟨7573207518983503995486905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048805012655669330324603 7573207518983503995486905)
          ·
            refine ⟨5679905639237627996615179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7573207518983503995486905 5679905639237627996615179)
            ·
              refine ⟨8519858458856441994922769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679905639237627996615179 8519858458856441994922769)
              ·
                refine ⟨6389893844142331496192077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8519858458856441994922769 6389893844142331496192077)
                ·
                  refine ⟨2396210191553374311072029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6389893844142331496192077 2396210191553374311072029)
                  ·
                    refine ⟨898578821832515366652011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396210191553374311072029 898578821832515366652011)
                    ·
                      rfl

theorem cell22_2624964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2624964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2624964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2624964 prefixEnd_2624964 := by exact prefixLift 2624964
  have htrace : WordTrace (prefixWord ++ tailWord_2624964) baseStart_2624964 baseEnd_2624964 := by
    simpa [prefixWord, tailWord_2624964, baseEnd_2624964] using wordTrace_append hprefix tailTrace_2624964
  have hstable : (prefixWord ++ tailWord_2624964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624964).length < 2 ^ (prefixWord ++ tailWord_2624964).sum := by decide
  have hdescent : baseEnd_2624964 < baseStart_2624964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625052 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2625052 : Nat := 118140960795 + 2625052 * 2 ^ 59
def prefixEnd_2625052 : Nat := 4983230072969 + 3 ^ 40 * 2625052 * 2
def baseEnd_2625052 : Nat := 898608946030912470451741

theorem tailTrace_2625052 : CollatzResearch.WordTrace tailWord_2625052 prefixEnd_2625052 898608946030912470451741 := by
  unfold tailWord_2625052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47871756042946201016938705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63829008057261601355918273 47871756042946201016938705)
  ·
    refine ⟨35903817032209650762704029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47871756042946201016938705 35903817032209650762704029)
    ·
      refine ⟨13463931387078619036014011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35903817032209650762704029 13463931387078619036014011)
      ·
        refine ⟨20195897080617928554021017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13463931387078619036014011 20195897080617928554021017)
        ·
          refine ⟨15146922810463446415515763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20195897080617928554021017 15146922810463446415515763)
          ·
            refine ⟨22720384215695169623273645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15146922810463446415515763 22720384215695169623273645)
            ·
              refine ⟨8520144080885688608727617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22720384215695169623273645 8520144080885688608727617)
              ·
                refine ⟨6390108060664266456545713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8520144080885688608727617 6390108060664266456545713)
                ·
                  refine ⟨4792581045498199842409285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390108060664266456545713 4792581045498199842409285)
                  ·
                    refine ⟨898608946030912470451741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792581045498199842409285 898608946030912470451741)
                    ·
                      rfl

theorem cell22_2625052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2625052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625052 prefixEnd_2625052 := by exact prefixLift 2625052
  have htrace : WordTrace (prefixWord ++ tailWord_2625052) baseStart_2625052 baseEnd_2625052 := by
    simpa [prefixWord, tailWord_2625052, baseEnd_2625052] using wordTrace_append hprefix tailTrace_2625052
  have hstable : (prefixWord ++ tailWord_2625052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625052).length < 2 ^ (prefixWord ++ tailWord_2625052).sum := by decide
  have hdescent : baseEnd_2625052 < baseStart_2625052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625056 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_2625056 : Nat := 118140960795 + 2625056 * 2 ^ 59
def prefixEnd_2625056 : Nat := 4983230072969 + 3 ^ 40 * 2625056 * 2
def baseEnd_2625056 : Nat := 299536771770885931117243

theorem tailTrace_2625056 : CollatzResearch.WordTrace tailWord_2625056 prefixEnd_2625056 299536771770885931117243 := by
  unfold tailWord_2625056
  simp only [CollatzResearch.WordTrace]
  refine ⟨47871828988938955358511511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63829105318585273811348681 47871828988938955358511511)
  ·
    refine ⟨71807743483408433037767267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47871828988938955358511511 71807743483408433037767267)
    ·
      refine ⟨107711615225112649556650901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71807743483408433037767267 107711615225112649556650901)
      ·
        refine ⟨5048981963677155447968011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107711615225112649556650901 5048981963677155447968011)
        ·
          refine ⟨7573472945515733171952017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048981963677155447968011 7573472945515733171952017)
          ·
            refine ⟨5680104709136799878964013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7573472945515733171952017 5680104709136799878964013)
            ·
              refine ⟨2130039265926299954611505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5680104709136799878964013 2130039265926299954611505)
              ·
                refine ⟨1597529449444724965958629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130039265926299954611505 1597529449444724965958629)
                ·
                  refine ⟨299536771770885931117243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597529449444724965958629 299536771770885931117243)
                  ·
                    rfl

theorem cell22_2625056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_2625056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625056 prefixEnd_2625056 := by exact prefixLift 2625056
  have htrace : WordTrace (prefixWord ++ tailWord_2625056) baseStart_2625056 baseEnd_2625056 := by
    simpa [prefixWord, tailWord_2625056, baseEnd_2625056] using wordTrace_append hprefix tailTrace_2625056
  have hstable : (prefixWord ++ tailWord_2625056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625056).length < 2 ^ (prefixWord ++ tailWord_2625056).sum := by decide
  have hdescent : baseEnd_2625056 < baseStart_2625056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625082 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_2625082 : Nat := 118140960795 + 2625082 * 2 ^ 59
def prefixEnd_2625082 : Nat := 4983230072969 + 3 ^ 40 * 2625082 * 2
def baseEnd_2625082 : Nat := 898619215644002392201649

theorem tailTrace_2625082 : CollatzResearch.WordTrace tailWord_2625082 prefixEnd_2625082 898619215644002392201649 := by
  unfold tailWord_2625082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23936151568945929289367375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63829737517189144771646333 23936151568945929289367375)
  ·
    refine ⟨35904227353418893934051063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23936151568945929289367375 35904227353418893934051063)
    ·
      refine ⟨53856341030128340901076595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35904227353418893934051063 53856341030128340901076595)
      ·
        refine ⟨80784511545192511351614893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53856341030128340901076595 80784511545192511351614893)
        ·
          refine ⟨30294191829447191756855585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80784511545192511351614893 30294191829447191756855585)
          ·
            refine ⟨22720643872085393817641689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30294191829447191756855585 22720643872085393817641689)
            ·
              refine ⟨17040482904064045363231267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22720643872085393817641689 17040482904064045363231267)
              ·
                refine ⟨25560724356096068044846901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17040482904064045363231267 25560724356096068044846901)
                ·
                  refine ⟨2396317908384006379204397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25560724356096068044846901 2396317908384006379204397)
                  ·
                    refine ⟨898619215644002392201649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396317908384006379204397 898619215644002392201649)
                    ·
                      rfl

theorem cell22_2625082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_2625082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625082 prefixEnd_2625082 := by exact prefixLift 2625082
  have htrace : WordTrace (prefixWord ++ tailWord_2625082) baseStart_2625082 baseEnd_2625082 := by
    simpa [prefixWord, tailWord_2625082, baseEnd_2625082] using wordTrace_append hprefix tailTrace_2625082
  have hstable : (prefixWord ++ tailWord_2625082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625082).length < 2 ^ (prefixWord ++ tailWord_2625082).sum := by decide
  have hdescent : baseEnd_2625082 < baseStart_2625082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625099 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 1, 3]
def baseStart_2625099 : Nat := 118140960795 + 2625099 * 2 ^ 59
def prefixEnd_2625099 : Nat := 4983230072969 + 3 ^ 40 * 2625099 * 2
def baseEnd_2625099 : Nat := 898625035091420014526597

theorem tailTrace_2625099 : CollatzResearch.WordTrace tailWord_2625099 prefixEnd_2625099 898625035091420014526597 := by
  unfold tailWord_2625099
  simp only [CollatzResearch.WordTrace]
  refine ⟨95745226316722129060838351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63830150877814752707225567 95745226316722129060838351)
  ·
    refine ⟨143617839475083193591257527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95745226316722129060838351 143617839475083193591257527)
    ·
      refine ⟨215426759212624790386886291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143617839475083193591257527 215426759212624790386886291)
      ·
        refine ⟨323140138818937185580329437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215426759212624790386886291 323140138818937185580329437)
        ·
          refine ⟨121177552057101444592623539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323140138818937185580329437 121177552057101444592623539)
          ·
            refine ⟨181766328085652166888935309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121177552057101444592623539 181766328085652166888935309)
            ·
              refine ⟨68162373032119562583350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181766328085652166888935309 68162373032119562583350741)
              ·
                refine ⟨1597555617940302248047283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68162373032119562583350741 1597555617940302248047283)
                ·
                  refine ⟨2396333426910453372070925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597555617940302248047283 2396333426910453372070925)
                  ·
                    refine ⟨898625035091420014526597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396333426910453372070925 898625035091420014526597)
                    ·
                      rfl

theorem cell22_2625099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 3].length) (baseStart_2625099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625099 prefixEnd_2625099 := by exact prefixLift 2625099
  have htrace : WordTrace (prefixWord ++ tailWord_2625099) baseStart_2625099 baseEnd_2625099 := by
    simpa [prefixWord, tailWord_2625099, baseEnd_2625099] using wordTrace_append hprefix tailTrace_2625099
  have hstable : (prefixWord ++ tailWord_2625099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625099).length < 2 ^ (prefixWord ++ tailWord_2625099).sum := by decide
  have hdescent : baseEnd_2625099 < baseStart_2625099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625159 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2625159 : Nat := 118140960795 + 2625159 * 2 ^ 59
def prefixEnd_2625159 : Nat := 4983230072969 + 3 ^ 40 * 2625159 * 2
def baseEnd_2625159 : Nat := 898645574317599858026413

theorem tailTrace_2625159 : CollatzResearch.WordTrace tailWord_2625159 prefixEnd_2625159 898645574317599858026413 := by
  unfold tailWord_2625159
  simp only [CollatzResearch.WordTrace]
  refine ⟨95747414696504759308022531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63831609797669839538681687 95747414696504759308022531)
  ·
    refine ⟨143621122044757138962033797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95747414696504759308022531 143621122044757138962033797)
    ·
      refine ⟨26928960383391963555381337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143621122044757138962033797 26928960383391963555381337)
      ·
        refine ⟨20196720287543972666536003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26928960383391963555381337 20196720287543972666536003)
        ·
          refine ⟨30295080431315958999804005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20196720287543972666536003 30295080431315958999804005)
          ·
            refine ⟨5680327580871742312463251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30295080431315958999804005 5680327580871742312463251)
            ·
              refine ⟨8520491371307613468694877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680327580871742312463251 8520491371307613468694877)
              ·
                refine ⟨3195184264240355050760579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8520491371307613468694877 3195184264240355050760579)
                ·
                  refine ⟨4792776396360532576140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195184264240355050760579 4792776396360532576140869)
                  ·
                    refine ⟨898645574317599858026413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4792776396360532576140869 898645574317599858026413)
                    ·
                      rfl

theorem cell22_2625159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2625159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625159 prefixEnd_2625159 := by exact prefixLift 2625159
  have htrace : WordTrace (prefixWord ++ tailWord_2625159) baseStart_2625159 baseEnd_2625159 := by
    simpa [prefixWord, tailWord_2625159, baseEnd_2625159] using wordTrace_append hprefix tailTrace_2625159
  have hstable : (prefixWord ++ tailWord_2625159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625159).length < 2 ^ (prefixWord ++ tailWord_2625159).sum := by decide
  have hdescent : baseEnd_2625159 < baseStart_2625159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625189 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_2625189 : Nat := 118140960795 + 2625189 * 2 ^ 59
def prefixEnd_2625189 : Nat := 4983230072969 + 3 ^ 40 * 2625189 * 2
def baseEnd_2625189 : Nat := 898655843930689779776321

theorem tailTrace_2625189 : CollatzResearch.WordTrace tailWord_2625189 prefixEnd_2625189 898655843930689779776321 := by
  unfold tailWord_2625189
  simp only [CollatzResearch.WordTrace]
  refine ⟨95748508886396074431614621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63832339257597382954409747 95748508886396074431614621)
  ·
    refine ⟨35905690832398527911855483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95748508886396074431614621 35905690832398527911855483)
    ·
      refine ⟨53858536248597791867783225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35905690832398527911855483 53858536248597791867783225)
      ·
        refine ⟨40393902186448343900837419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53858536248597791867783225 40393902186448343900837419)
        ·
          refine ⟨60590853279672515851256129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40393902186448343900837419 60590853279672515851256129)
          ·
            refine ⟨45443139959754386888442097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60590853279672515851256129 45443139959754386888442097)
            ·
              refine ⟨34082354969815790166331573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45443139959754386888442097 34082354969815790166331573)
              ·
                refine ⟨3195220778420230328093585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34082354969815790166331573 3195220778420230328093585)
                ·
                  refine ⟨2396415583815172746070189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195220778420230328093585 2396415583815172746070189)
                  ·
                    refine ⟨898655843930689779776321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396415583815172746070189 898655843930689779776321)
                    ·
                      rfl

theorem cell22_2625189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_2625189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625189 prefixEnd_2625189 := by exact prefixLift 2625189
  have htrace : WordTrace (prefixWord ++ tailWord_2625189) baseStart_2625189 baseEnd_2625189 := by
    simpa [prefixWord, tailWord_2625189, baseEnd_2625189] using wordTrace_append hprefix tailTrace_2625189
  have hstable : (prefixWord ++ tailWord_2625189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625189).length < 2 ^ (prefixWord ++ tailWord_2625189).sum := by decide
  have hdescent : baseEnd_2625189 < baseStart_2625189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625294 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2625294 : Nat := 118140960795 + 2625294 * 2 ^ 59
def prefixEnd_2625294 : Nat := 4983230072969 + 3 ^ 40 * 2625294 * 2
def baseEnd_2625294 : Nat := 898691787576504505900999

theorem tailTrace_2625294 : CollatzResearch.WordTrace tailWord_2625294 prefixEnd_2625294 898691787576504505900999 := by
  unfold tailWord_2625294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969042318876959670523367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63834892367343784909457957 11969042318876959670523367)
  ·
    refine ⟨17953563478315439505785051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11969042318876959670523367 17953563478315439505785051)
    ·
      refine ⟨26930345217473159258677577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17953563478315439505785051 26930345217473159258677577)
      ·
        refine ⟨20197758913104869444008183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26930345217473159258677577 20197758913104869444008183)
        ·
          refine ⟨30296638369657304166012275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20197758913104869444008183 30296638369657304166012275)
          ·
            refine ⟨45444957554485956249018413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30296638369657304166012275 45444957554485956249018413)
            ·
              refine ⟨17041859082932233593381905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45444957554485956249018413 17041859082932233593381905)
              ·
                refine ⟨12781394312199175195036429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17041859082932233593381905 12781394312199175195036429)
                ·
                  refine ⟨4793022867074690698138661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12781394312199175195036429 4793022867074690698138661)
                  ·
                    refine ⟨898691787576504505900999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793022867074690698138661 898691787576504505900999)
                    ·
                      rfl

theorem cell22_2625294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2625294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625294 prefixEnd_2625294 := by exact prefixLift 2625294
  have htrace : WordTrace (prefixWord ++ tailWord_2625294) baseStart_2625294 baseEnd_2625294 := by
    simpa [prefixWord, tailWord_2625294, baseEnd_2625294] using wordTrace_append hprefix tailTrace_2625294
  have hstable : (prefixWord ++ tailWord_2625294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625294).length < 2 ^ (prefixWord ++ tailWord_2625294).sum := by decide
  have hdescent : baseEnd_2625294 < baseStart_2625294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625307 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_2625307 : Nat := 118140960795 + 2625307 * 2 ^ 59
def prefixEnd_2625307 : Nat := 4983230072969 + 3 ^ 40 * 2625307 * 2
def baseEnd_2625307 : Nat := 898696237742176805325959

theorem tailTrace_2625307 : CollatzResearch.WordTrace tailWord_2625307 prefixEnd_2625307 898696237742176805325959 := by
  unfold tailWord_2625307
  simp only [CollatzResearch.WordTrace]
  refine ⟨95752812699968580584410175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63835208466645720389606783 95752812699968580584410175)
  ·
    refine ⟨143629219049952870876615263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95752812699968580584410175 143629219049952870876615263)
    ·
      refine ⟨215443828574929306314922895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143629219049952870876615263 215443828574929306314922895)
      ·
        refine ⟨323165742862393959472384343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215443828574929306314922895 323165742862393959472384343)
        ·
          refine ⟨484748614293590939208576515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323165742862393959472384343 484748614293590939208576515)
          ·
            refine ⟨727122921440386408812864773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484748614293590939208576515 727122921440386408812864773)
            ·
              refine ⟨136335547770072451652412145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 727122921440386408812864773 136335547770072451652412145)
              ·
                refine ⟨102251660827554338739309109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136335547770072451652412145 102251660827554338739309109)
                ·
                  refine ⟨9586093202583219256810229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102251660827554338739309109 9586093202583219256810229)
                  ·
                    refine ⟨898696237742176805325959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586093202583219256810229 898696237742176805325959)
                    ·
                      rfl

theorem cell22_2625307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_2625307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625307 prefixEnd_2625307 := by exact prefixLift 2625307
  have htrace : WordTrace (prefixWord ++ tailWord_2625307) baseStart_2625307 baseEnd_2625307 := by
    simpa [prefixWord, tailWord_2625307, baseEnd_2625307] using wordTrace_append hprefix tailTrace_2625307
  have hstable : (prefixWord ++ tailWord_2625307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625307).length < 2 ^ (prefixWord ++ tailWord_2625307).sum := by decide
  have hdescent : baseEnd_2625307 < baseStart_2625307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625324 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_2625324 : Nat := 118140960795 + 2625324 * 2 ^ 59
def prefixEnd_2625324 : Nat := 4983230072969 + 3 ^ 40 * 2625324 * 2
def baseEnd_2625324 : Nat := 898702057189594427650907

theorem tailTrace_2625324 : CollatzResearch.WordTrace tailWord_2625324 prefixEnd_2625324 898702057189594427650907 := by
  unfold tailWord_2625324
  simp only [CollatzResearch.WordTrace]
  refine ⟨47876716370453496243889513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63835621827271328325186017 47876716370453496243889513)
  ·
    refine ⟨35907537277840122182917135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47876716370453496243889513 35907537277840122182917135)
    ·
      refine ⟨53861305916760183274375703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35907537277840122182917135 53861305916760183274375703)
      ·
        refine ⟨80791958875140274911563555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53861305916760183274375703 80791958875140274911563555)
        ·
          refine ⟨121187938312710412367345333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80791958875140274911563555 121187938312710412367345333)
          ·
            refine ⟨11361369216816601159438625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121187938312710412367345333 11361369216816601159438625)
            ·
              refine ⟨8521026912612450869578969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11361369216816601159438625 8521026912612450869578969)
              ·
                refine ⟨6390770184459338152184227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521026912612450869578969 6390770184459338152184227)
                ·
                  refine ⟨9586155276689007228276341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6390770184459338152184227 9586155276689007228276341)
                  ·
                    refine ⟨898702057189594427650907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586155276689007228276341 898702057189594427650907)
                    ·
                      rfl

theorem cell22_2625324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_2625324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625324 prefixEnd_2625324 := by exact prefixLift 2625324
  have htrace : WordTrace (prefixWord ++ tailWord_2625324) baseStart_2625324 baseEnd_2625324 := by
    simpa [prefixWord, tailWord_2625324, baseEnd_2625324] using wordTrace_append hprefix tailTrace_2625324
  have hstable : (prefixWord ++ tailWord_2625324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625324).length < 2 ^ (prefixWord ++ tailWord_2625324).sum := by decide
  have hdescent : baseEnd_2625324 < baseStart_2625324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625409 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2625409 : Nat := 118140960795 + 2625409 * 2 ^ 59
def prefixEnd_2625409 : Nat := 4983230072969 + 3 ^ 40 * 2625409 * 2
def baseEnd_2625409 : Nat := 898731154426682539275647

theorem tailTrace_2625409 : CollatzResearch.WordTrace tailWord_2625409 prefixEnd_2625409 898731154426682539275647 := by
  unfold tailWord_2625409
  simp only [CollatzResearch.WordTrace]
  refine ⟨95756532945599052004623281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63837688630399368003082187 95756532945599052004623281)
  ·
    refine ⟨71817399709199289003467461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95756532945599052004623281 71817399709199289003467461)
    ·
      refine ⟨13465762445474866688150149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71817399709199289003467461 13465762445474866688150149)
      ·
        refine ⟨2524830458526537504028153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13465762445474866688150149 2524830458526537504028153)
        ·
          refine ⟨1893622843894903128021115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524830458526537504028153 1893622843894903128021115)
          ·
            refine ⟨2840434265842354692031673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893622843894903128021115 2840434265842354692031673)
            ·
              refine ⟨2130325699381766019023755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840434265842354692031673 2130325699381766019023755)
              ·
                refine ⟨3195488549072649028535633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130325699381766019023755 3195488549072649028535633)
                ·
                  refine ⟨2396616411804486771401725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195488549072649028535633 2396616411804486771401725)
                  ·
                    refine ⟨898731154426682539275647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396616411804486771401725 898731154426682539275647)
                    ·
                      rfl

theorem cell22_2625409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2625409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625409 prefixEnd_2625409 := by exact prefixLift 2625409
  have htrace : WordTrace (prefixWord ++ tailWord_2625409) baseStart_2625409 baseEnd_2625409 := by
    simpa [prefixWord, tailWord_2625409, baseEnd_2625409] using wordTrace_append hprefix tailTrace_2625409
  have hstable : (prefixWord ++ tailWord_2625409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625409).length < 2 ^ (prefixWord ++ tailWord_2625409).sum := by decide
  have hdescent : baseEnd_2625409 < baseStart_2625409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625459 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_2625459 : Nat := 118140960795 + 2625459 * 2 ^ 59
def prefixEnd_2625459 : Nat := 4983230072969 + 3 ^ 40 * 2625459 * 2
def baseEnd_2625459 : Nat := 898748270448499075525493

theorem tailTrace_2625459 : CollatzResearch.WordTrace tailWord_2625459 prefixEnd_2625459 898748270448499075525493 := by
  unfold tailWord_2625459
  simp only [CollatzResearch.WordTrace]
  refine ⟨95758356595417910543943431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63838904396945273695962287 95758356595417910543943431)
  ·
    refine ⟨143637534893126865815915147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95758356595417910543943431 143637534893126865815915147)
    ·
      refine ⟨215456302339690298723872721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143637534893126865815915147 215456302339690298723872721)
      ·
        refine ⟨161592226754767724042904541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215456302339690298723872721 161592226754767724042904541)
        ·
          refine ⟨60597085033037896516089203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161592226754767724042904541 60597085033037896516089203)
          ·
            refine ⟨90895627549556844774133805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60597085033037896516089203 90895627549556844774133805)
            ·
              refine ⟨34085860331083816790300177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90895627549556844774133805 34085860331083816790300177)
              ·
                refine ⟨25564395248312862592725133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34085860331083816790300177 25564395248312862592725133)
                ·
                  refine ⟨9586648218117323472271925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25564395248312862592725133 9586648218117323472271925)
                  ·
                    refine ⟨898748270448499075525493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9586648218117323472271925 898748270448499075525493)
                    ·
                      rfl

theorem cell22_2625459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_2625459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625459 prefixEnd_2625459 := by exact prefixLift 2625459
  have htrace : WordTrace (prefixWord ++ tailWord_2625459) baseStart_2625459 baseEnd_2625459 := by
    simpa [prefixWord, tailWord_2625459, baseEnd_2625459] using wordTrace_append hprefix tailTrace_2625459
  have hstable : (prefixWord ++ tailWord_2625459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625459).length < 2 ^ (prefixWord ++ tailWord_2625459).sum := by decide
  have hdescent : baseEnd_2625459 < baseStart_2625459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625497 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_2625497 : Nat := 118140960795 + 2625497 * 2 ^ 59
def prefixEnd_2625497 : Nat := 4983230072969 + 3 ^ 40 * 2625497 * 2
def baseEnd_2625497 : Nat := 898761278625079643075377

theorem tailTrace_2625497 : CollatzResearch.WordTrace tailWord_2625497 prefixEnd_2625497 898761278625079643075377 := by
  unfold tailWord_2625497
  simp only [CollatzResearch.WordTrace]
  refine ⟨95759742569280243033826745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63839828379520162022551163 95759742569280243033826745)
  ·
    refine ⟨71819806926960182275370059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95759742569280243033826745 71819806926960182275370059)
    ·
      refine ⟨107729710390440273413055089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71819806926960182275370059 107729710390440273413055089)
      ·
        refine ⟨80797282792830205059791317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107729710390440273413055089 80797282792830205059791317)
        ·
          refine ⟨1893686315456957931088859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80797282792830205059791317 1893686315456957931088859)
          ·
            refine ⟨2840529473185436896633289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893686315456957931088859 2840529473185436896633289)
            ·
              refine ⟨2130397104889077672474967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840529473185436896633289 2130397104889077672474967)
              ·
                refine ⟨3195595657333616508712451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130397104889077672474967 3195595657333616508712451)
                ·
                  refine ⟨4793393486000424763068677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195595657333616508712451 4793393486000424763068677)
                  ·
                    refine ⟨898761278625079643075377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793393486000424763068677 898761278625079643075377)
                    ·
                      rfl

theorem cell22_2625497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_2625497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625497 prefixEnd_2625497 := by exact prefixLift 2625497
  have htrace : WordTrace (prefixWord ++ tailWord_2625497) baseStart_2625497 baseEnd_2625497 := by
    simpa [prefixWord, tailWord_2625497, baseEnd_2625497] using wordTrace_append hprefix tailTrace_2625497
  have hstable : (prefixWord ++ tailWord_2625497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625497).length < 2 ^ (prefixWord ++ tailWord_2625497).sum := by decide
  have hdescent : baseEnd_2625497 < baseStart_2625497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625504 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_2625504 : Nat := 118140960795 + 2625504 * 2 ^ 59
def prefixEnd_2625504 : Nat := 4983230072969 + 3 ^ 40 * 2625504 * 2
def baseEnd_2625504 : Nat := 898763674868133958150355

theorem tailTrace_2625504 : CollatzResearch.WordTrace tailWord_2625504 prefixEnd_2625504 898763674868133958150355 := by
  unfold tailWord_2625504
  simp only [CollatzResearch.WordTrace]
  refine ⟨47879998940127441614665783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63839998586836588819554377 47879998940127441614665783)
  ·
    refine ⟨71819998410191162421998675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47879998940127441614665783 71819998410191162421998675)
    ·
      refine ⟨107729997615286743632998013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71819998410191162421998675 107729997615286743632998013)
      ·
        refine ⟨40398749105732528862374255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107729997615286743632998013 40398749105732528862374255)
        ·
          refine ⟨60598123658598793293561383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40398749105732528862374255 60598123658598793293561383)
          ·
            refine ⟨90897185487898189940342075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60598123658598793293561383 90897185487898189940342075)
            ·
              refine ⟨136345778231847284910513113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90897185487898189940342075 136345778231847284910513113)
              ·
                refine ⟨102259333673885463682884835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136345778231847284910513113 102259333673885463682884835)
                ·
                  refine ⟨153389000510828195524327253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102259333673885463682884835 153389000510828195524327253)
                  ·
                    refine ⟨898763674868133958150355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 153389000510828195524327253 898763674868133958150355)
                    ·
                      rfl

theorem cell22_2625504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_2625504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625504 prefixEnd_2625504 := by exact prefixLift 2625504
  have htrace : WordTrace (prefixWord ++ tailWord_2625504) baseStart_2625504 baseEnd_2625504 := by
    simpa [prefixWord, tailWord_2625504, baseEnd_2625504] using wordTrace_append hprefix tailTrace_2625504
  have hstable : (prefixWord ++ tailWord_2625504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625504).length < 2 ^ (prefixWord ++ tailWord_2625504).sum := by decide
  have hdescent : baseEnd_2625504 < baseStart_2625504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625555 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 1, 3]
def baseStart_2625555 : Nat := 118140960795 + 2625555 * 2 ^ 59
def prefixEnd_2625555 : Nat := 4983230072969 + 3 ^ 40 * 2625555 * 2
def baseEnd_2625555 : Nat := 898781133210386825125199

theorem tailTrace_2625555 : CollatzResearch.WordTrace tailWord_2625555 prefixEnd_2625555 898781133210386825125199 := by
  unfold tailWord_2625555
  simp only [CollatzResearch.WordTrace]
  refine ⟨95761858003070118939438119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63841238668713412626292079 95761858003070118939438119)
  ·
    refine ⟨143642787004605178409157179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95761858003070118939438119 143642787004605178409157179)
    ·
      refine ⟨215464180506907767613735769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143642787004605178409157179 215464180506907767613735769)
      ·
        refine ⟨161598135380180825710301827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215464180506907767613735769 161598135380180825710301827)
        ·
          refine ⟨242397203070271238565452741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161598135380180825710301827 242397203070271238565452741)
          ·
            refine ⟨45449475575675857231022389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242397203070271238565452741 45449475575675857231022389)
            ·
              refine ⟨4260888335219611615408349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45449475575675857231022389 4260888335219611615408349)
              ·
                refine ⟨1597833125707354355778131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4260888335219611615408349 1597833125707354355778131)
                ·
                  refine ⟨2396749688561031533667197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597833125707354355778131 2396749688561031533667197)
                  ·
                    refine ⟨898781133210386825125199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396749688561031533667197 898781133210386825125199)
                    ·
                      rfl

theorem cell22_2625555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 3].length) (baseStart_2625555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625555 prefixEnd_2625555 := by exact prefixLift 2625555
  have htrace : WordTrace (prefixWord ++ tailWord_2625555) baseStart_2625555 baseEnd_2625555 := by
    simpa [prefixWord, tailWord_2625555, baseEnd_2625555] using wordTrace_append hprefix tailTrace_2625555
  have hstable : (prefixWord ++ tailWord_2625555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625555).length < 2 ^ (prefixWord ++ tailWord_2625555).sum := by decide
  have hdescent : baseEnd_2625555 < baseStart_2625555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625572 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_2625572 : Nat := 118140960795 + 2625572 * 2 ^ 59
def prefixEnd_2625572 : Nat := 4983230072969 + 3 ^ 40 * 2625572 * 2
def baseEnd_2625572 : Nat := 898786952657804447450147

theorem tailTrace_2625572 : CollatzResearch.WordTrace tailWord_2625572 prefixEnd_2625572 898786952657804447450147 := by
  unfold tailWord_2625572
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881239022004265421403485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63841652029339020561871313 47881239022004265421403485)
  ·
    refine ⟨17955464633251599533026307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47881239022004265421403485 17955464633251599533026307)
    ·
      refine ⟨26933196949877399299539461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17955464633251599533026307 26933196949877399299539461)
      ·
        refine ⟨5049974428102012368663649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26933196949877399299539461 5049974428102012368663649)
        ·
          refine ⟨3787480821076509276497737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5049974428102012368663649 3787480821076509276497737)
          ·
            refine ⟨2840610615807381957373303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3787480821076509276497737 2840610615807381957373303)
            ·
              refine ⟨4260915923711072936059955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840610615807381957373303 4260915923711072936059955)
              ·
                refine ⟨6391373885566609404089933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260915923711072936059955 6391373885566609404089933)
                ·
                  refine ⟨2396765207087478526533725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6391373885566609404089933 2396765207087478526533725)
                  ·
                    refine ⟨898786952657804447450147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396765207087478526533725 898786952657804447450147)
                    ·
                      rfl

theorem cell22_2625572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_2625572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625572 prefixEnd_2625572 := by exact prefixLift 2625572
  have htrace : WordTrace (prefixWord ++ tailWord_2625572) baseStart_2625572 baseEnd_2625572 := by
    simpa [prefixWord, tailWord_2625572, baseEnd_2625572] using wordTrace_append hprefix tailTrace_2625572
  have hstable : (prefixWord ++ tailWord_2625572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625572).length < 2 ^ (prefixWord ++ tailWord_2625572).sum := by decide
  have hdescent : baseEnd_2625572 < baseStart_2625572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625585 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 5]
def baseStart_2625585 : Nat := 118140960795 + 2625585 * 2 ^ 59
def prefixEnd_2625585 : Nat := 4983230072969 + 3 ^ 40 * 2625585 * 2
def baseEnd_2625585 : Nat := 299597134274492248958369

theorem tailTrace_2625585 : CollatzResearch.WordTrace tailWord_2625585 prefixEnd_2625585 299597134274492248958369 := by
  unfold tailWord_2625585
  simp only [CollatzResearch.WordTrace]
  refine ⟨95762952192961434063030209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63841968128640956042020139 95762952192961434063030209)
  ·
    refine ⟨71822214144721075547272657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95762952192961434063030209 71822214144721075547272657)
    ·
      refine ⟨53866660608540806660454493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71822214144721075547272657 53866660608540806660454493)
      ·
        refine ⟨20199997728202802497670435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53866660608540806660454493 20199997728202802497670435)
        ·
          refine ⟨30299996592304203746505653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20199997728202802497670435 30299996592304203746505653)
          ·
            refine ⟨2840624680528519101234905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30299996592304203746505653 2840624680528519101234905)
            ·
              refine ⟨2130468510396389325926179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840624680528519101234905 2130468510396389325926179)
              ·
                refine ⟨3195702765594583988889269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130468510396389325926179 3195702765594583988889269)
                ·
                  refine ⟨299597134274492248958369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3195702765594583988889269 299597134274492248958369)
                  ·
                    rfl

theorem cell22_2625585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_2625585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625585 prefixEnd_2625585 := by exact prefixLift 2625585
  have htrace : WordTrace (prefixWord ++ tailWord_2625585) baseStart_2625585 baseEnd_2625585 := by
    simpa [prefixWord, tailWord_2625585, baseEnd_2625585] using wordTrace_append hprefix tailTrace_2625585
  have hstable : (prefixWord ++ tailWord_2625585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625585).length < 2 ^ (prefixWord ++ tailWord_2625585).sum := by decide
  have hdescent : baseEnd_2625585 < baseStart_2625585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625596 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_2625596 : Nat := 118140960795 + 2625596 * 2 ^ 59
def prefixEnd_2625596 : Nat := 4983230072969 + 3 ^ 40 * 2625596 * 2
def baseEnd_2625596 : Nat := 299598389449425461616691

theorem tailTrace_2625596 : CollatzResearch.WordTrace tailWord_2625596 prefixEnd_2625596 299598389449425461616691 := by
  unfold tailWord_2625596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881676697960791470840321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63842235597281055294453761 47881676697960791470840321)
  ·
    refine ⟨35911257523470593603130241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47881676697960791470840321 35911257523470593603130241)
    ·
      refine ⟨26933443142602945202347681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35911257523470593603130241 26933443142602945202347681)
      ·
        refine ⟨20200082356952208901760761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26933443142602945202347681 20200082356952208901760761)
        ·
          refine ⟨15150061767714156676320571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20200082356952208901760761 15150061767714156676320571)
          ·
            refine ⟨22725092651571235014480857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15150061767714156676320571 22725092651571235014480857)
            ·
              refine ⟨17043819488678426260860643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22725092651571235014480857 17043819488678426260860643)
              ·
                refine ⟨25565729233017639391290965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17043819488678426260860643 25565729233017639391290965)
                ·
                  refine ⟨299598389449425461616691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25565729233017639391290965 299598389449425461616691)
                  ·
                    rfl

theorem cell22_2625596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_2625596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625596 prefixEnd_2625596 := by exact prefixLift 2625596
  have htrace : WordTrace (prefixWord ++ tailWord_2625596) baseStart_2625596 baseEnd_2625596 := by
    simpa [prefixWord, tailWord_2625596, baseEnd_2625596] using wordTrace_append hprefix tailTrace_2625596
  have hstable : (prefixWord ++ tailWord_2625596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625596).length < 2 ^ (prefixWord ++ tailWord_2625596).sum := by decide
  have hdescent : baseEnd_2625596 < baseStart_2625596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625611 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_2625611 : Nat := 118140960795 + 2625611 * 2 ^ 59
def prefixEnd_2625611 : Nat := 4983230072969 + 3 ^ 40 * 2625611 * 2
def baseEnd_2625611 : Nat := 898800303154821345725027

theorem tailTrace_2625611 : CollatzResearch.WordTrace tailWord_2625611 prefixEnd_2625611 898800303154821345725027 := by
  unfold tailWord_2625611
  simp only [CollatzResearch.WordTrace]
  refine ⟨95763900490867240503476687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63842600327244827002317791 95763900490867240503476687)
  ·
    refine ⟨143645850736300860755215031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95763900490867240503476687 143645850736300860755215031)
    ·
      refine ⟨215468776104451291132822547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143645850736300860755215031 215468776104451291132822547)
      ·
        refine ⟨323203164156676936699233821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215468776104451291132822547 323203164156676936699233821)
        ·
          refine ⟨121201186558753851262212683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323203164156676936699233821 121201186558753851262212683)
          ·
            refine ⟨181801779838130776893319025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121201186558753851262212683 181801779838130776893319025)
            ·
              refine ⟨136351334878598082669989269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181801779838130776893319025 136351334878598082669989269)
              ·
                refine ⟨6391468822434285125155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136351334878598082669989269 6391468822434285125155747)
                ·
                  refine ⟨9587203233651427687733621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391468822434285125155747 9587203233651427687733621)
                  ·
                    refine ⟨898800303154821345725027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9587203233651427687733621 898800303154821345725027)
                    ·
                      rfl

theorem cell22_2625611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_2625611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625611 prefixEnd_2625611 := by exact prefixLift 2625611
  have htrace : WordTrace (prefixWord ++ tailWord_2625611) baseStart_2625611 baseEnd_2625611 := by
    simpa [prefixWord, tailWord_2625611, baseEnd_2625611] using wordTrace_append hprefix tailTrace_2625611
  have hstable : (prefixWord ++ tailWord_2625611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625611).length < 2 ^ (prefixWord ++ tailWord_2625611).sum := by decide
  have hdescent : baseEnd_2625611 < baseStart_2625611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625645 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_2625645 : Nat := 118140960795 + 2625645 * 2 ^ 59
def prefixEnd_2625645 : Nat := 4983230072969 + 3 ^ 40 * 2625645 * 2
def baseEnd_2625645 : Nat := 898811942049656590374923

theorem tailTrace_2625645 : CollatzResearch.WordTrace tailWord_2625645 prefixEnd_2625645 898811942049656590374923 := by
  unfold tailWord_2625645
  simp only [CollatzResearch.WordTrace]
  refine ⟨95765140572744064310214389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63843427048496042873476259 95765140572744064310214389)
  ·
    refine ⟨8977981928694756029082599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95765140572744064310214389 8977981928694756029082599)
    ·
      refine ⟨13466972893042134043623899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8977981928694756029082599 13466972893042134043623899)
      ·
        refine ⟨20200459339563201065435849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13466972893042134043623899 20200459339563201065435849)
        ·
          refine ⟨15150344504672400799076887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20200459339563201065435849 15150344504672400799076887)
          ·
            refine ⟨22725516757008601198615331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15150344504672400799076887 22725516757008601198615331)
            ·
              refine ⟨34088275135512901797922997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22725516757008601198615331 34088275135512901797922997)
              ·
                refine ⟨3195775793954334543555281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34088275135512901797922997 3195775793954334543555281)
                ·
                  refine ⟨2396831845465750907666461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195775793954334543555281 2396831845465750907666461)
                  ·
                    refine ⟨898811942049656590374923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396831845465750907666461 898811942049656590374923)
                    ·
                      rfl

theorem cell22_2625645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_2625645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625645 prefixEnd_2625645 := by exact prefixLift 2625645
  have htrace : WordTrace (prefixWord ++ tailWord_2625645) baseStart_2625645 baseEnd_2625645 := by
    simpa [prefixWord, tailWord_2625645, baseEnd_2625645] using wordTrace_append hprefix tailTrace_2625645
  have hstable : (prefixWord ++ tailWord_2625645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625645).length < 2 ^ (prefixWord ++ tailWord_2625645).sum := by decide
  have hdescent : baseEnd_2625645 < baseStart_2625645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625660 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_2625660 : Nat := 118140960795 + 2625660 * 2 ^ 59
def prefixEnd_2625660 : Nat := 4983230072969 + 3 ^ 40 * 2625660 * 2
def baseEnd_2625660 : Nat := 898817076856201551249877

theorem tailTrace_2625660 : CollatzResearch.WordTrace tailWord_2625660 prefixEnd_2625660 898817076856201551249877 := by
  unfold tailWord_2625660
  simp only [CollatzResearch.WordTrace]
  refine ⟨47882843833844860936005217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63843791778459814581340289 47882843833844860936005217)
  ·
    refine ⟨35912132875383645702003913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47882843833844860936005217 35912132875383645702003913)
    ·
      refine ⟨26934099656537734276502935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35912132875383645702003913 26934099656537734276502935)
      ·
        refine ⟨40401149484806601414754403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26934099656537734276502935 40401149484806601414754403)
        ·
          refine ⟨60601724227209902122131605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40401149484806601414754403 60601724227209902122131605)
          ·
            refine ⟨2840705823150464161974919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60601724227209902122131605 2840705823150464161974919)
            ·
              refine ⟨4261058734725696242962379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840705823150464161974919 4261058734725696242962379)
              ·
                refine ⟨6391588102088544364443569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261058734725696242962379 6391588102088544364443569)
                ·
                  refine ⟨4793691076566408273332677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391588102088544364443569 4793691076566408273332677)
                  ·
                    refine ⟨898817076856201551249877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793691076566408273332677 898817076856201551249877)
                    ·
                      rfl

theorem cell22_2625660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_2625660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625660 prefixEnd_2625660 := by exact prefixLift 2625660
  have htrace : WordTrace (prefixWord ++ tailWord_2625660) baseStart_2625660 baseEnd_2625660 := by
    simpa [prefixWord, tailWord_2625660, baseEnd_2625660] using wordTrace_append hprefix tailTrace_2625660
  have hstable : (prefixWord ++ tailWord_2625660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625660).length < 2 ^ (prefixWord ++ tailWord_2625660).sum := by decide
  have hdescent : baseEnd_2625660 < baseStart_2625660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625673 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_2625673 : Nat := 118140960795 + 2625673 * 2 ^ 59
def prefixEnd_2625673 : Nat := 4983230072969 + 3 ^ 40 * 2625673 * 2
def baseEnd_2625673 : Nat := 898821527021873850674837

theorem tailTrace_2625673 : CollatzResearch.WordTrace tailWord_2625673 prefixEnd_2625673 898821527021873850674837 := by
  unfold tailWord_2625673
  simp only [CollatzResearch.WordTrace]
  refine ⟨95766161816642625092233673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63844107877761750061489115 95766161816642625092233673)
  ·
    refine ⟨71824621362481968819175255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95766161816642625092233673 71824621362481968819175255)
    ·
      refine ⟨107736932043722953228762883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71824621362481968819175255 107736932043722953228762883)
      ·
        refine ⟨161605398065584429843144325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107736932043722953228762883 161605398065584429843144325)
        ·
          refine ⟨30301012137297080595589561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161605398065584429843144325 30301012137297080595589561)
          ·
            refine ⟨22725759102972810446692171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30301012137297080595589561 22725759102972810446692171)
            ·
              refine ⟨34088638654459215670038257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22725759102972810446692171 34088638654459215670038257)
              ·
                refine ⟨25566478990844411752528693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34088638654459215670038257 25566478990844411752528693)
                ·
                  refine ⟨2396857405391663601799565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25566478990844411752528693 2396857405391663601799565)
                  ·
                    refine ⟨898821527021873850674837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396857405391663601799565 898821527021873850674837)
                    ·
                      rfl

theorem cell22_2625673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_2625673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625673 prefixEnd_2625673 := by exact prefixLift 2625673
  have htrace : WordTrace (prefixWord ++ tailWord_2625673) baseStart_2625673 baseEnd_2625673 := by
    simpa [prefixWord, tailWord_2625673, baseEnd_2625673] using wordTrace_append hprefix tailTrace_2625673
  have hstable : (prefixWord ++ tailWord_2625673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625673).length < 2 ^ (prefixWord ++ tailWord_2625673).sum := by decide
  have hdescent : baseEnd_2625673 < baseStart_2625673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625767 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2625767 : Nat := 118140960795 + 2625767 * 2 ^ 59
def prefixEnd_2625767 : Nat := 4983230072969 + 3 ^ 40 * 2625767 * 2
def baseEnd_2625767 : Nat := 898853705142888938824549

theorem tailTrace_2625767 : CollatzResearch.WordTrace tailWord_2625767 prefixEnd_2625767 898853705142888938824549 := by
  unfold tailWord_2625767
  simp only [CollatzResearch.WordTrace]
  refine ⟨95769590278302079146155555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63846393518868052764103703 95769590278302079146155555)
  ·
    refine ⟨143654385417453118719233333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95769590278302079146155555 143654385417453118719233333)
    ·
      refine ⟨13467598632886229879928125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143654385417453118719233333 13467598632886229879928125)
      ·
        refine ⟨5050349487332336204973047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13467598632886229879928125 5050349487332336204973047)
        ·
          refine ⟨7575524230998504307459571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050349487332336204973047 7575524230998504307459571)
          ·
            refine ⟨11363286346497756461189357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7575524230998504307459571 11363286346497756461189357)
            ·
              refine ⟨4261232379936658672946009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11363286346497756461189357 4261232379936658672946009)
              ·
                refine ⟨3195924284952494004709507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261232379936658672946009 3195924284952494004709507)
                ·
                  refine ⟨4793886427428741007064261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195924284952494004709507 4793886427428741007064261)
                  ·
                    refine ⟨898853705142888938824549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793886427428741007064261 898853705142888938824549)
                    ·
                      rfl

theorem cell22_2625767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2625767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625767 prefixEnd_2625767 := by exact prefixLift 2625767
  have htrace : WordTrace (prefixWord ++ tailWord_2625767) baseStart_2625767 baseEnd_2625767 := by
    simpa [prefixWord, tailWord_2625767, baseEnd_2625767] using wordTrace_append hprefix tailTrace_2625767
  have hstable : (prefixWord ++ tailWord_2625767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625767).length < 2 ^ (prefixWord ++ tailWord_2625767).sum := by decide
  have hdescent : baseEnd_2625767 < baseStart_2625767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625799 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 4]
def baseStart_2625799 : Nat := 118140960795 + 2625799 * 2 ^ 59
def prefixEnd_2625799 : Nat := 4983230072969 + 3 ^ 40 * 2625799 * 2
def baseEnd_2625799 : Nat := 299621553132283840674817

theorem tailTrace_2625799 : CollatzResearch.WordTrace tailWord_2625799 prefixEnd_2625799 299621553132283840674817 := by
  unfold tailWord_2625799
  simp only [CollatzResearch.WordTrace]
  refine ⟨95770757414186148611320451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63847171609457432407546967 95770757414186148611320451)
  ·
    refine ⟨143656136121279222916980677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95770757414186148611320451 143656136121279222916980677)
    ·
      refine ⟨26935525522739854296933877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143656136121279222916980677 26935525522739854296933877)
      ·
        refine ⟨2525205517756861340337551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26935525522739854296933877 2525205517756861340337551)
        ·
          refine ⟨3787808276635292010506327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525205517756861340337551 3787808276635292010506327)
          ·
            refine ⟨5681712414952938015759491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787808276635292010506327 5681712414952938015759491)
            ·
              refine ⟨8522568622429407023639237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681712414952938015759491 8522568622429407023639237)
              ·
                refine ⟨1597981616705513816932357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8522568622429407023639237 1597981616705513816932357)
                ·
                  refine ⟨299621553132283840674817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597981616705513816932357 299621553132283840674817)
                  ·
                    rfl

theorem cell22_2625799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 4].length) (baseStart_2625799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625799 prefixEnd_2625799 := by exact prefixLift 2625799
  have htrace : WordTrace (prefixWord ++ tailWord_2625799) baseStart_2625799 baseEnd_2625799 := by
    simpa [prefixWord, tailWord_2625799, baseEnd_2625799] using wordTrace_append hprefix tailTrace_2625799
  have hstable : (prefixWord ++ tailWord_2625799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625799).length < 2 ^ (prefixWord ++ tailWord_2625799).sum := by decide
  have hdescent : baseEnd_2625799 < baseStart_2625799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625825 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2625825 : Nat := 118140960795 + 2625825 * 2 ^ 59
def prefixEnd_2625825 : Nat := 4983230072969 + 3 ^ 40 * 2625825 * 2
def baseEnd_2625825 : Nat := 898873559728196120874371

theorem tailTrace_2625825 : CollatzResearch.WordTrace tailWord_2625825 prefixEnd_2625825 898873559728196120874371 := by
  unfold tailWord_2625825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95771705712091955051766929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63847803808061303367844619 95771705712091955051766929)
  ·
    refine ⟨71828779284068966288825197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95771705712091955051766929 71828779284068966288825197)
    ·
      refine ⟨26935792231525862358309449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71828779284068966288825197 26935792231525862358309449)
      ·
        refine ⟨20201844173644396768732087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26935792231525862358309449 20201844173644396768732087)
        ·
          refine ⟨30302766260466595153098131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20201844173644396768732087 30302766260466595153098131)
          ·
            refine ⟨45454149390699892729647197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30302766260466595153098131 45454149390699892729647197)
            ·
              refine ⟨17045306021512459773617699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45454149390699892729647197 17045306021512459773617699)
              ·
                refine ⟨25567959032268689660426549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17045306021512459773617699 25567959032268689660426549)
                ·
                  refine ⟨2396996159275189655664989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25567959032268689660426549 2396996159275189655664989)
                  ·
                    refine ⟨898873559728196120874371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2396996159275189655664989 898873559728196120874371)
                    ·
                      rfl

theorem cell22_2625825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2625825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625825 prefixEnd_2625825 := by exact prefixLift 2625825
  have htrace : WordTrace (prefixWord ++ tailWord_2625825) baseStart_2625825 baseEnd_2625825 := by
    simpa [prefixWord, tailWord_2625825, baseEnd_2625825] using wordTrace_append hprefix tailTrace_2625825
  have hstable : (prefixWord ++ tailWord_2625825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625825).length < 2 ^ (prefixWord ++ tailWord_2625825).sum := by decide
  have hdescent : baseEnd_2625825 < baseStart_2625825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625829 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_2625829 : Nat := 118140960795 + 2625829 * 2 ^ 59
def prefixEnd_2625829 : Nat := 4983230072969 + 3 ^ 40 * 2625829 * 2
def baseEnd_2625829 : Nat := 898874929009941443774359

theorem tailTrace_2625829 : CollatzResearch.WordTrace tailWord_2625829 prefixEnd_2625829 898874929009941443774359 := by
  unfold tailWord_2625829
  simp only [CollatzResearch.WordTrace]
  refine ⟨95771851604077463734912541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63847901069384975823275027 95771851604077463734912541)
  ·
    refine ⟨35914444351529048900592203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95771851604077463734912541 35914444351529048900592203)
    ·
      refine ⟨53871666527293573350888305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35914444351529048900592203 53871666527293573350888305)
      ·
        refine ⟨40403749895470180013166229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53871666527293573350888305 40403749895470180013166229)
        ·
          refine ⟨1893925776350164688117167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40403749895470180013166229 1893925776350164688117167)
          ·
            refine ⟨2840888664525247032175751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893925776350164688117167 2840888664525247032175751)
            ·
              refine ⟨4261332996787870548263627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840888664525247032175751 4261332996787870548263627)
              ·
                refine ⟨6391999495181805822395441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261332996787870548263627 6391999495181805822395441)
                ·
                  refine ⟨4793999621386354366796581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391999495181805822395441 4793999621386354366796581)
                  ·
                    refine ⟨898874929009941443774359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4793999621386354366796581 898874929009941443774359)
                    ·
                      rfl

theorem cell22_2625829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_2625829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625829 prefixEnd_2625829 := by exact prefixLift 2625829
  have htrace : WordTrace (prefixWord ++ tailWord_2625829) baseStart_2625829 baseEnd_2625829 := by
    simpa [prefixWord, tailWord_2625829, baseEnd_2625829] using wordTrace_append hprefix tailTrace_2625829
  have hstable : (prefixWord ++ tailWord_2625829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625829).length < 2 ^ (prefixWord ++ tailWord_2625829).sum := by decide
  have hdescent : baseEnd_2625829 < baseStart_2625829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625872 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_2625872 : Nat := 118140960795 + 2625872 * 2 ^ 59
def prefixEnd_2625872 : Nat := 4983230072969 + 3 ^ 40 * 2625872 * 2
def baseEnd_2625872 : Nat := 299629882929567888316409

theorem tailTrace_2625872 : CollatzResearch.WordTrace tailWord_2625872 prefixEnd_2625872 299629882929567888316409 := by
  unfold tailWord_2625872
  simp only [CollatzResearch.WordTrace]
  refine ⟨47886709971460841039363935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63848946628614454719151913 47886709971460841039363935)
  ·
    refine ⟨71830064957191261559045903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47886709971460841039363935 71830064957191261559045903)
    ·
      refine ⟨107745097435786892338568855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71830064957191261559045903 107745097435786892338568855)
      ·
        refine ⟨161617646153680338507853283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107745097435786892338568855 161617646153680338507853283)
        ·
          refine ⟨242426469230520507761779925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161617646153680338507853283 242426469230520507761779925)
          ·
            refine ⟨5681870372590324400666717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 242426469230520507761779925 5681870372590324400666717)
            ·
              refine ⟨2130701389721371650250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5681870372590324400666717 2130701389721371650250019)
              ·
                refine ⟨3196052084582057475375029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130701389721371650250019 3196052084582057475375029)
                ·
                  refine ⟨299629882929567888316409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196052084582057475375029 299629882929567888316409)
                  ·
                    rfl

theorem cell22_2625872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_2625872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625872 prefixEnd_2625872 := by exact prefixLift 2625872
  have htrace : WordTrace (prefixWord ++ tailWord_2625872) baseStart_2625872 baseEnd_2625872 := by
    simpa [prefixWord, tailWord_2625872, baseEnd_2625872] using wordTrace_append hprefix tailTrace_2625872
  have hstable : (prefixWord ++ tailWord_2625872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625872).length < 2 ^ (prefixWord ++ tailWord_2625872).sum := by decide
  have hdescent : baseEnd_2625872 < baseStart_2625872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625910 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_2625910 : Nat := 118140960795 + 2625910 * 2 ^ 59
def prefixEnd_2625910 : Nat := 4983230072969 + 3 ^ 40 * 2625910 * 2
def baseEnd_2625910 : Nat := 898902656965284232499111

theorem tailTrace_2625910 : CollatzResearch.WordTrace tailWord_2625910 prefixEnd_2625910 898902656965284232499111 := by
  unfold tailWord_2625910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985925369799000910538199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63849870611189343045740789 5985925369799000910538199)
  ·
    refine ⟨8978888054698501365807299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5985925369799000910538199 8978888054698501365807299)
    ·
      refine ⟨13468332082047752048710949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8978888054698501365807299 13468332082047752048710949)
      ·
        refine ⟨2525312265383953509133303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13468332082047752048710949 2525312265383953509133303)
        ·
          refine ⟨3787968398075930263699955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525312265383953509133303 3787968398075930263699955)
          ·
            refine ⟨5681952597113895395549933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787968398075930263699955 5681952597113895395549933)
            ·
              refine ⟨2130732223917710773331225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5681952597113895395549933 2130732223917710773331225)
              ·
                refine ⟨1598049167938283079998419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130732223917710773331225 1598049167938283079998419)
                ·
                  refine ⟨2397073751907424619997629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598049167938283079998419 2397073751907424619997629)
                  ·
                    refine ⟨898902656965284232499111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397073751907424619997629 898902656965284232499111)
                    ·
                      rfl

theorem cell22_2625910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_2625910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625910 prefixEnd_2625910 := by exact prefixLift 2625910
  have htrace : WordTrace (prefixWord ++ tailWord_2625910) baseStart_2625910 baseEnd_2625910 := by
    simpa [prefixWord, tailWord_2625910, baseEnd_2625910] using wordTrace_append hprefix tailTrace_2625910
  have hstable : (prefixWord ++ tailWord_2625910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625910).length < 2 ^ (prefixWord ++ tailWord_2625910).sum := by decide
  have hdescent : baseEnd_2625910 < baseStart_2625910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625917 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 6]
def baseStart_2625917 : Nat := 118140960795 + 2625917 * 2 ^ 59
def prefixEnd_2625917 : Nat := 4983230072969 + 3 ^ 40 * 2625917 * 2
def baseEnd_2625917 : Nat := 299635017736112849191363

theorem tailTrace_2625917 : CollatzResearch.WordTrace tailWord_2625917 prefixEnd_2625917 299635017736112849191363 := by
  unfold tailWord_2625917
  simp only [CollatzResearch.WordTrace]
  refine ⟨95775061227758654764116005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63850040818505769842744003 95775061227758654764116005)
  ·
    refine ⟨17957823980204747768271751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95775061227758654764116005 17957823980204747768271751)
    ·
      refine ⟨26936735970307121652407627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17957823980204747768271751 26936735970307121652407627)
      ·
        refine ⟨40405103955460682478611441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26936735970307121652407627 40405103955460682478611441)
        ·
          refine ⟨30303827966595511858958581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40405103955460682478611441 30303827966595511858958581)
          ·
            refine ⟨2840983871868329236777367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30303827966595511858958581 2840983871868329236777367)
            ·
              refine ⟨4261475807802493855166051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840983871868329236777367 4261475807802493855166051)
              ·
                refine ⟨6392213711703740782749077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261475807802493855166051 6392213711703740782749077)
                ·
                  refine ⟨299635017736112849191363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6392213711703740782749077 299635017736112849191363)
                  ·
                    rfl

theorem cell22_2625917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_2625917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625917 prefixEnd_2625917 := by exact prefixLift 2625917
  have htrace : WordTrace (prefixWord ++ tailWord_2625917) baseStart_2625917 baseEnd_2625917 := by
    simpa [prefixWord, tailWord_2625917, baseEnd_2625917] using wordTrace_append hprefix tailTrace_2625917
  have hstable : (prefixWord ++ tailWord_2625917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625917).length < 2 ^ (prefixWord ++ tailWord_2625917).sum := by decide
  have hdescent : baseEnd_2625917 < baseStart_2625917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625975 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2625975 : Nat := 118140960795 + 2625975 * 2 ^ 59
def prefixEnd_2625975 : Nat := 4983230072969 + 3 ^ 40 * 2625975 * 2
def baseEnd_2625975 : Nat := 898924907793645729623911

theorem tailTrace_2625975 : CollatzResearch.WordTrace tailWord_2625975 prefixEnd_2625975 898924907793645729623911 := by
  unfold tailWord_2625975
  simp only [CollatzResearch.WordTrace]
  refine ⟨95777176661548530669727379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63851451107699020446484919 95777176661548530669727379)
  ·
    refine ⟨143665764992322796004591069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95777176661548530669727379 143665764992322796004591069)
    ·
      refine ⟨53874661872121048501721651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143665764992322796004591069 53874661872121048501721651)
      ·
        refine ⟨80811992808181572752582477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53874661872121048501721651 80811992808181572752582477)
        ·
          refine ⟨30304497303068089782218429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80811992808181572752582477 30304497303068089782218429)
          ·
            refine ⟨11364186488650533668331911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30304497303068089782218429 11364186488650533668331911)
            ·
              refine ⟨17046279732975800502497867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11364186488650533668331911 17046279732975800502497867)
              ·
                refine ⟨25569419599463700753746801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17046279732975800502497867 25569419599463700753746801)
                ·
                  refine ⟨19177064699597775565310101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25569419599463700753746801 19177064699597775565310101)
                  ·
                    refine ⟨898924907793645729623911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19177064699597775565310101 898924907793645729623911)
                    ·
                      rfl

theorem cell22_2625975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2625975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2625975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2625975 prefixEnd_2625975 := by exact prefixLift 2625975
  have htrace : WordTrace (prefixWord ++ tailWord_2625975) baseStart_2625975 baseEnd_2625975 := by
    simpa [prefixWord, tailWord_2625975, baseEnd_2625975] using wordTrace_append hprefix tailTrace_2625975
  have hstable : (prefixWord ++ tailWord_2625975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625975).length < 2 ^ (prefixWord ++ tailWord_2625975).sum := by decide
  have hdescent : baseEnd_2625975 < baseStart_2625975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626024 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_2626024 : Nat := 118140960795 + 2626024 * 2 ^ 59
def prefixEnd_2626024 : Nat := 4983230072969 + 3 ^ 40 * 2626024 * 2
def baseEnd_2626024 : Nat := 299647227165008645049587

theorem tailTrace_2626024 : CollatzResearch.WordTrace tailWord_2626024 prefixEnd_2626024 299647227165008645049587 := by
  unfold tailWord_2626024
  simp only [CollatzResearch.WordTrace]
  refine ⟨47889481919185506019130563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63852642558914008025507417 47889481919185506019130563)
  ·
    refine ⟨71834222878778259028695845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47889481919185506019130563 71834222878778259028695845)
    ·
      refine ⟨13468916789770923567880471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71834222878778259028695845 13468916789770923567880471)
      ·
        refine ⟨20203375184656385351820707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13468916789770923567880471 20203375184656385351820707)
        ·
          refine ⟨30305062776984578027731061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20203375184656385351820707 30305062776984578027731061)
          ·
            refine ⟨2841099635342304190099787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30305062776984578027731061 2841099635342304190099787)
            ·
              refine ⟨4261649453013456285149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841099635342304190099787 4261649453013456285149681)
              ·
                refine ⟨3196237089760092213862261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261649453013456285149681 3196237089760092213862261)
                ·
                  refine ⟨299647227165008645049587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196237089760092213862261 299647227165008645049587)
                  ·
                    rfl

theorem cell22_2626024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_2626024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626024 prefixEnd_2626024 := by exact prefixLift 2626024
  have htrace : WordTrace (prefixWord ++ tailWord_2626024) baseStart_2626024 baseEnd_2626024 := by
    simpa [prefixWord, tailWord_2626024, baseEnd_2626024] using wordTrace_append hprefix tailTrace_2626024
  have hstable : (prefixWord ++ tailWord_2626024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626024).length < 2 ^ (prefixWord ++ tailWord_2626024).sum := by decide
  have hdescent : baseEnd_2626024 < baseStart_2626024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626067 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 6, 3]
def baseStart_2626067 : Nat := 118140960795 + 2626067 * 2 ^ 59
def prefixEnd_2626067 : Nat := 4983230072969 + 3 ^ 40 * 2626067 * 2
def baseEnd_2626067 : Nat := 898956401273788156323629

theorem tailTrace_2626067 : CollatzResearch.WordTrace tailWord_2626067 prefixEnd_2626067 898956401273788156323629 := by
  unfold tailWord_2626067
  simp only [CollatzResearch.WordTrace]
  refine ⟨95780532177215230382076455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63853688118143486921384303 95780532177215230382076455)
  ·
    refine ⟨143670798265822845573114683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95780532177215230382076455 143670798265822845573114683)
    ·
      refine ⟨215506197398734268359672025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143670798265822845573114683 215506197398734268359672025)
      ·
        refine ⟨161629648049050701269754019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215506197398734268359672025 161629648049050701269754019)
        ·
          refine ⟨242444472073576051904631029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161629648049050701269754019 242444472073576051904631029)
          ·
            refine ⟨22729169256897754866059159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242444472073576051904631029 22729169256897754866059159)
            ·
              refine ⟨34093753885346632299088739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22729169256897754866059159 34093753885346632299088739)
              ·
                refine ⟨51140630828019948448633109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34093753885346632299088739 51140630828019948448633109)
                ·
                  refine ⟨2397217070063435083529677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51140630828019948448633109 2397217070063435083529677)
                  ·
                    refine ⟨898956401273788156323629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397217070063435083529677 898956401273788156323629)
                    ·
                      rfl

theorem cell22_2626067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3].length) (baseStart_2626067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626067 prefixEnd_2626067 := by exact prefixLift 2626067
  have htrace : WordTrace (prefixWord ++ tailWord_2626067) baseStart_2626067 baseEnd_2626067 := by
    simpa [prefixWord, tailWord_2626067, baseEnd_2626067] using wordTrace_append hprefix tailTrace_2626067
  have hstable : (prefixWord ++ tailWord_2626067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626067).length < 2 ^ (prefixWord ++ tailWord_2626067).sum := by decide
  have hdescent : baseEnd_2626067 < baseStart_2626067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626204 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_2626204 : Nat := 118140960795 + 2626204 * 2 ^ 59
def prefixEnd_2626204 : Nat := 4983230072969 + 3 ^ 40 * 2626204 * 2
def baseEnd_2626204 : Nat := 299667766391188488549403

theorem tailTrace_2626204 : CollatzResearch.WordTrace tailWord_2626204 prefixEnd_2626204 299667766391188488549403 := by
  unfold tailWord_2626204
  simp only [CollatzResearch.WordTrace]
  refine ⟨47892764488859451389906833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63857019318479268519875777 47892764488859451389906833)
  ·
    refine ⟨35919573366644588542430125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47892764488859451389906833 35919573366644588542430125)
    ·
      refine ⟨13469840012491720703411297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35919573366644588542430125 13469840012491720703411297)
      ·
        refine ⟨10102380009368790527558473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13469840012491720703411297 10102380009368790527558473)
        ·
          refine ⟨7576785007026592895668855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10102380009368790527558473 7576785007026592895668855)
          ·
            refine ⟨11365177510539889343503283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576785007026592895668855 11365177510539889343503283)
            ·
              refine ⟨17047766265809834015254925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11365177510539889343503283 17047766265809834015254925)
              ·
                refine ⟨6392912349678687755720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17047766265809834015254925 6392912349678687755720597)
                ·
                  refine ⟨299667766391188488549403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6392912349678687755720597 299667766391188488549403)
                  ·
                    rfl

theorem cell22_2626204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_2626204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626204 prefixEnd_2626204 := by exact prefixLift 2626204
  have htrace : WordTrace (prefixWord ++ tailWord_2626204) baseStart_2626204 baseEnd_2626204 := by
    simpa [prefixWord, tailWord_2626204, baseEnd_2626204] using wordTrace_append hprefix tailTrace_2626204
  have hstable : (prefixWord ++ tailWord_2626204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626204).length < 2 ^ (prefixWord ++ tailWord_2626204).sum := by decide
  have hdescent : baseEnd_2626204 < baseStart_2626204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626217 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_2626217 : Nat := 118140960795 + 2626217 * 2 ^ 59
def prefixEnd_2626217 : Nat := 4983230072969 + 3 ^ 40 * 2626217 * 2
def baseEnd_2626217 : Nat := 899007749339237765073169

theorem tailTrace_2626217 : CollatzResearch.WordTrace tailWord_2626217 prefixEnd_2626217 899007749339237765073169 := by
  unfold tailWord_2626217
  simp only [CollatzResearch.WordTrace]
  refine ⟨95786003126671806000036905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63857335417781204000024603 95786003126671806000036905)
  ·
    refine ⟨71839502345003854500027679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95786003126671806000036905 71839502345003854500027679)
    ·
      refine ⟨107759253517505781750041519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71839502345003854500027679 107759253517505781750041519)
      ·
        refine ⟨161638880276258672625062279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107759253517505781750041519 161638880276258672625062279)
        ·
          refine ⟨242458320414388008937593419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161638880276258672625062279 242458320414388008937593419)
          ·
            refine ⟨363687480621582013406390129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242458320414388008937593419 363687480621582013406390129)
            ·
              refine ⟨272765610466186510054792597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363687480621582013406390129 272765610466186510054792597)
              ·
                refine ⟨12785887990602492658818403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272765610466186510054792597 12785887990602492658818403)
                ·
                  refine ⟨19178831985903738988227605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12785887990602492658818403 19178831985903738988227605)
                  ·
                    refine ⟨899007749339237765073169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19178831985903738988227605 899007749339237765073169)
                    ·
                      rfl

theorem cell22_2626217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_2626217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626217 prefixEnd_2626217 := by exact prefixLift 2626217
  have htrace : WordTrace (prefixWord ++ tailWord_2626217) baseStart_2626217 baseEnd_2626217 := by
    simpa [prefixWord, tailWord_2626217, baseEnd_2626217] using wordTrace_append hprefix tailTrace_2626217
  have hstable : (prefixWord ++ tailWord_2626217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626217).length < 2 ^ (prefixWord ++ tailWord_2626217).sum := by decide
  have hdescent : baseEnd_2626217 < baseStart_2626217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626234 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_2626234 : Nat := 118140960795 + 2626234 * 2 ^ 59
def prefixEnd_2626234 : Nat := 4983230072969 + 3 ^ 40 * 2626234 * 2
def baseEnd_2626234 : Nat := 899013568786655387398117

theorem tailTrace_2626234 : CollatzResearch.WordTrace tailWord_2626234 prefixEnd_2626234 899013568786655387398117 := by
  unfold tailWord_2626234
  simp only [CollatzResearch.WordTrace]
  refine ⟨23946655791902554475851439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63857748778406811935603837 23946655791902554475851439)
  ·
    refine ⟨35919983687853831713777159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23946655791902554475851439 35919983687853831713777159)
    ·
      refine ⟨53879975531780747570665739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35919983687853831713777159 53879975531780747570665739)
      ·
        refine ⟨80819963297671121355998609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53879975531780747570665739 80819963297671121355998609)
        ·
          refine ⟨60614972473253341016998957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80819963297671121355998609 60614972473253341016998957)
          ·
            refine ⟨22730614677470002881374609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60614972473253341016998957 22730614677470002881374609)
            ·
              refine ⟨17047961008102502161030957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22730614677470002881374609 17047961008102502161030957)
              ·
                refine ⟨6392985378038438310386609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17047961008102502161030957 6392985378038438310386609)
                ·
                  refine ⟨4794739033528828732789957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6392985378038438310386609 4794739033528828732789957)
                  ·
                    refine ⟨899013568786655387398117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4794739033528828732789957 899013568786655387398117)
                    ·
                      rfl

theorem cell22_2626234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_2626234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626234 prefixEnd_2626234 := by exact prefixLift 2626234
  have htrace : WordTrace (prefixWord ++ tailWord_2626234) baseStart_2626234 baseEnd_2626234 := by
    simpa [prefixWord, tailWord_2626234, baseEnd_2626234] using wordTrace_append hprefix tailTrace_2626234
  have hstable : (prefixWord ++ tailWord_2626234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626234).length < 2 ^ (prefixWord ++ tailWord_2626234).sum := by decide
  have hdescent : baseEnd_2626234 < baseStart_2626234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626311 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 5]
def baseStart_2626311 : Nat := 118140960795 + 2626311 * 2 ^ 59
def prefixEnd_2626311 : Nat := 4983230072969 + 3 ^ 40 * 2626311 * 2
def baseEnd_2626311 : Nat := 299679975820084284407627

theorem tailTrace_2626311 : CollatzResearch.WordTrace tailWord_2626311 prefixEnd_2626311 299679975820084284407627 := by
  unfold tailWord_2626311
  simp only [CollatzResearch.WordTrace]
  refine ⟨95789431588331260053958787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63859621058887506702639191 95789431588331260053958787)
  ·
    refine ⟨143684147382496890080938181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95789431588331260053958787 143684147382496890080938181)
    ·
      refine ⟨26940777634218166890175909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143684147382496890080938181 26940777634218166890175909)
      ·
        refine ⟨5051395806415906291907983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26940777634218166890175909 5051395806415906291907983)
        ·
          refine ⟨7577093709623859437861975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051395806415906291907983 7577093709623859437861975)
          ·
            refine ⟨11365640564435789156792963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577093709623859437861975 11365640564435789156792963)
            ·
              refine ⟨17048460846653683735189445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11365640564435789156792963 17048460846653683735189445)
              ·
                refine ⟨3196586408747565700348021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17048460846653683735189445 3196586408747565700348021)
                ·
                  refine ⟨299679975820084284407627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196586408747565700348021 299679975820084284407627)
                  ·
                    rfl

theorem cell22_2626311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 5].length) (baseStart_2626311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626311 prefixEnd_2626311 := by exact prefixLift 2626311
  have htrace : WordTrace (prefixWord ++ tailWord_2626311) baseStart_2626311 baseEnd_2626311 := by
    simpa [prefixWord, tailWord_2626311, baseEnd_2626311] using wordTrace_append hprefix tailTrace_2626311
  have hstable : (prefixWord ++ tailWord_2626311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626311).length < 2 ^ (prefixWord ++ tailWord_2626311).sum := by decide
  have hdescent : baseEnd_2626311 < baseStart_2626311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626341 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_2626341 : Nat := 118140960795 + 2626341 * 2 ^ 59
def prefixEnd_2626341 : Nat := 4983230072969 + 3 ^ 40 * 2626341 * 2
def baseEnd_2626341 : Nat := 899050197073342774972789

theorem tailTrace_2626341 : CollatzResearch.WordTrace tailWord_2626341 prefixEnd_2626341 899050197073342774972789 := by
  unfold tailWord_2626341
  simp only [CollatzResearch.WordTrace]
  refine ⟨95790525778222575177550877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63860350518815050118367251 95790525778222575177550877)
  ·
    refine ⟨35921447166833465691581579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95790525778222575177550877 35921447166833465691581579)
    ·
      refine ⟨53882170750250198537372369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35921447166833465691581579 53882170750250198537372369)
      ·
        refine ⟨40411628062687648903029277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53882170750250198537372369 40411628062687648903029277)
        ·
          refine ⟨15154360523507868338635979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40411628062687648903029277 15154360523507868338635979)
          ·
            refine ⟨22731540785261802507953969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15154360523507868338635979 22731540785261802507953969)
            ·
              refine ⟨17048655588946351880965477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22731540785261802507953969 17048655588946351880965477)
              ·
                refine ⟨3196622922927440977681027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17048655588946351880965477 3196622922927440977681027)
                ·
                  refine ⟨4794934384391161466521541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196622922927440977681027 4794934384391161466521541)
                  ·
                    refine ⟨899050197073342774972789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4794934384391161466521541 899050197073342774972789)
                    ·
                      rfl

theorem cell22_2626341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_2626341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626341 prefixEnd_2626341 := by exact prefixLift 2626341
  have htrace : WordTrace (prefixWord ++ tailWord_2626341) baseStart_2626341 baseEnd_2626341 := by
    simpa [prefixWord, tailWord_2626341, baseEnd_2626341] using wordTrace_append hprefix tailTrace_2626341
  have hstable : (prefixWord ++ tailWord_2626341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626341).length < 2 ^ (prefixWord ++ tailWord_2626341).sum := by decide
  have hdescent : baseEnd_2626341 < baseStart_2626341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626349 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2626349 : Nat := 118140960795 + 2626349 * 2 ^ 59
def prefixEnd_2626349 : Nat := 4983230072969 + 3 ^ 40 * 2626349 * 2
def baseEnd_2626349 : Nat := 899052935636833420772765

theorem tailTrace_2626349 : CollatzResearch.WordTrace tailWord_2626349 prefixEnd_2626349 899052935636833420772765 := by
  unfold tailWord_2626349
  simp only [CollatzResearch.WordTrace]
  refine ⟨95790817562193592543842101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63860545041462395029228067 95790817562193592543842101)
  ·
    refine ⟨8980389146455649300985197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95790817562193592543842101 8980389146455649300985197)
    ·
      refine ⟨3367645929920868487869449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8980389146455649300985197 3367645929920868487869449)
      ·
        refine ⟨2525734447440651365902087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3367645929920868487869449 2525734447440651365902087)
        ·
          refine ⟨3788601671160977048853131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525734447440651365902087 3788601671160977048853131)
          ·
            refine ⟨5682902506741465573279697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788601671160977048853131 5682902506741465573279697)
            ·
              refine ⟨4262176880056099179959773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682902506741465573279697 4262176880056099179959773)
              ·
                refine ⟨1598316330021037192484915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4262176880056099179959773 1598316330021037192484915)
                ·
                  refine ⟨2397474495031555788727373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598316330021037192484915 2397474495031555788727373)
                  ·
                    refine ⟨899052935636833420772765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397474495031555788727373 899052935636833420772765)
                    ·
                      rfl

theorem cell22_2626349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2626349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626349 prefixEnd_2626349 := by exact prefixLift 2626349
  have htrace : WordTrace (prefixWord ++ tailWord_2626349) baseStart_2626349 baseEnd_2626349 := by
    simpa [prefixWord, tailWord_2626349, baseEnd_2626349] using wordTrace_append hprefix tailTrace_2626349
  have hstable : (prefixWord ++ tailWord_2626349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626349).length < 2 ^ (prefixWord ++ tailWord_2626349).sum := by decide
  have hdescent : baseEnd_2626349 < baseStart_2626349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626371 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 4, 3]
def baseStart_2626371 : Nat := 118140960795 + 2626371 * 2 ^ 59
def prefixEnd_2626371 : Nat := 4983230072969 + 3 ^ 40 * 2626371 * 2
def baseEnd_2626371 : Nat := 899060466686432696722697

theorem tailTrace_2626371 : CollatzResearch.WordTrace tailWord_2626371 prefixEnd_2626371 899060466686432696722697 := by
  unfold tailWord_2626371
  simp only [CollatzResearch.WordTrace]
  refine ⟨95791619968113890301142967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63861079978742593534095311 95791619968113890301142967)
  ·
    refine ⟨143687429952170835451714451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95791619968113890301142967 143687429952170835451714451)
    ·
      refine ⟨215531144928256253177571677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143687429952170835451714451 215531144928256253177571677)
      ·
        refine ⟨80824179348096094941589379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215531144928256253177571677 80824179348096094941589379)
        ·
          refine ⟨121236269022144142412384069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80824179348096094941589379 121236269022144142412384069)
          ·
            refine ⟨22731800441652026702322013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121236269022144142412384069 22731800441652026702322013)
            ·
              refine ⟨8524425165619510013370755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22731800441652026702322013 8524425165619510013370755)
              ·
                refine ⟨12786637748429265020056133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8524425165619510013370755 12786637748429265020056133)
                ·
                  refine ⟨2397494577830487191260525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12786637748429265020056133 2397494577830487191260525)
                  ·
                    refine ⟨899060466686432696722697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397494577830487191260525 899060466686432696722697)
                    ·
                      rfl

theorem cell22_2626371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3].length) (baseStart_2626371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626371 prefixEnd_2626371 := by exact prefixLift 2626371
  have htrace : WordTrace (prefixWord ++ tailWord_2626371) baseStart_2626371 baseEnd_2626371 := by
    simpa [prefixWord, tailWord_2626371, baseEnd_2626371] using wordTrace_append hprefix tailTrace_2626371
  have hstable : (prefixWord ++ tailWord_2626371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626371).length < 2 ^ (prefixWord ++ tailWord_2626371).sum := by decide
  have hdescent : baseEnd_2626371 < baseStart_2626371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626399 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_2626399 : Nat := 118140960795 + 2626399 * 2 ^ 59
def prefixEnd_2626399 : Nat := 4983230072969 + 3 ^ 40 * 2626399 * 2
def baseEnd_2626399 : Nat := 899070051658649957022611

theorem tailTrace_2626399 : CollatzResearch.WordTrace tailWord_2626399 prefixEnd_2626399 899070051658649957022611 := by
  unfold tailWord_2626399
  simp only [CollatzResearch.WordTrace]
  refine ⟨95792641212012451083162251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63861760808008300722108167 95792641212012451083162251)
  ·
    refine ⟨143688961818018676624743377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95792641212012451083162251 143688961818018676624743377)
    ·
      refine ⟨107766721363514007468557533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143688961818018676624743377 107766721363514007468557533)
      ·
        refine ⟨40412520511317752800709075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107766721363514007468557533 40412520511317752800709075)
        ·
          refine ⟨60618780766976629201063613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40412520511317752800709075 60618780766976629201063613)
          ·
            refine ⟨22732042787616235950398855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60618780766976629201063613 22732042787616235950398855)
            ·
              refine ⟨34098064181424353925598283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22732042787616235950398855 34098064181424353925598283)
              ·
                refine ⟨51147096272136530888397425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34098064181424353925598283 51147096272136530888397425)
                ·
                  refine ⟨38360322204102398166298069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51147096272136530888397425 38360322204102398166298069)
                  ·
                    refine ⟨899070051658649957022611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38360322204102398166298069 899070051658649957022611)
                    ·
                      rfl

theorem cell22_2626399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_2626399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626399 prefixEnd_2626399 := by exact prefixLift 2626399
  have htrace : WordTrace (prefixWord ++ tailWord_2626399) baseStart_2626399 baseEnd_2626399 := by
    simpa [prefixWord, tailWord_2626399, baseEnd_2626399] using wordTrace_append hprefix tailTrace_2626399
  have hstable : (prefixWord ++ tailWord_2626399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626399).length < 2 ^ (prefixWord ++ tailWord_2626399).sum := by decide
  have hdescent : baseEnd_2626399 < baseStart_2626399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626416 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_2626416 : Nat := 118140960795 + 2626416 * 2 ^ 59
def prefixEnd_2626416 : Nat := 4983230072969 + 3 ^ 40 * 2626416 * 2
def baseEnd_2626416 : Nat := 899075871106067579347559

theorem tailTrace_2626416 : CollatzResearch.WordTrace tailWord_2626416 prefixEnd_2626416 899075871106067579347559 := by
  unfold tailWord_2626416
  simp only [CollatzResearch.WordTrace]
  refine ⟨47896630626475431493265551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63862174168633908657687401 47896630626475431493265551)
  ·
    refine ⟨71844945939713147239898327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47896630626475431493265551 71844945939713147239898327)
    ·
      refine ⟨107767418909569720859847491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71844945939713147239898327 107767418909569720859847491)
      ·
        refine ⟨161651128364354581289771237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107767418909569720859847491 161651128364354581289771237)
        ·
          refine ⟨30309586568316483991832107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161651128364354581289771237 30309586568316483991832107)
          ·
            refine ⟨45464379852474725987748161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30309586568316483991832107 45464379852474725987748161)
            ·
              refine ⟨34098284889356044490811121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45464379852474725987748161 34098284889356044490811121)
              ·
                refine ⟨25573713667017033368108341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34098284889356044490811121 25573713667017033368108341)
                ·
                  refine ⟨2397535656282846878260157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25573713667017033368108341 2397535656282846878260157)
                  ·
                    refine ⟨899075871106067579347559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397535656282846878260157 899075871106067579347559)
                    ·
                      rfl

theorem cell22_2626416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_2626416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626416 prefixEnd_2626416 := by exact prefixLift 2626416
  have htrace : WordTrace (prefixWord ++ tailWord_2626416) baseStart_2626416 baseEnd_2626416 := by
    simpa [prefixWord, tailWord_2626416, baseEnd_2626416] using wordTrace_append hprefix tailTrace_2626416
  have hstable : (prefixWord ++ tailWord_2626416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626416).length < 2 ^ (prefixWord ++ tailWord_2626416).sum := by decide
  have hdescent : baseEnd_2626416 < baseStart_2626416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626484 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2626484 : Nat := 118140960795 + 2626484 * 2 ^ 59
def prefixEnd_2626484 : Nat := 4983230072969 + 3 ^ 40 * 2626484 * 2
def baseEnd_2626484 : Nat := 899099148895738068647351

theorem tailTrace_2626484 : CollatzResearch.WordTrace tailWord_2626484 prefixEnd_2626484 899099148895738068647351 := by
  unfold tailWord_2626484
  simp only [CollatzResearch.WordTrace]
  refine ⟨47897870708352255300003253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63863827611136340400004337 47897870708352255300003253)
  ·
    refine ⟨4490425378908023934375305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47897870708352255300003253 4490425378908023934375305)
    ·
      refine ⟨3367819034181017950781479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4490425378908023934375305 3367819034181017950781479)
      ·
        refine ⟨5051728551271526926172219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367819034181017950781479 5051728551271526926172219)
        ·
          refine ⟨7577592826907290389258329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051728551271526926172219 7577592826907290389258329)
          ·
            refine ⟨5683194620180467791943747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7577592826907290389258329 5683194620180467791943747)
            ·
              refine ⟨8524791930270701687915621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683194620180467791943747 8524791930270701687915621)
              ·
                refine ⟨1598398486925756566484179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8524791930270701687915621 1598398486925756566484179)
                ·
                  refine ⟨2397597730388634849726269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598398486925756566484179 2397597730388634849726269)
                  ·
                    refine ⟨899099148895738068647351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397597730388634849726269 899099148895738068647351)
                    ·
                      rfl

theorem cell22_2626484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2626484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626484 prefixEnd_2626484 := by exact prefixLift 2626484
  have htrace : WordTrace (prefixWord ++ tailWord_2626484) baseStart_2626484 baseEnd_2626484 := by
    simpa [prefixWord, tailWord_2626484, baseEnd_2626484] using wordTrace_append hprefix tailTrace_2626484
  have hstable : (prefixWord ++ tailWord_2626484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626484).length < 2 ^ (prefixWord ++ tailWord_2626484).sum := by decide
  have hdescent : baseEnd_2626484 < baseStart_2626484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626525 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 4]
def baseStart_2626525 : Nat := 118140960795 + 2626525 * 2 ^ 59
def prefixEnd_2626525 : Nat := 4983230072969 + 3 ^ 40 * 2626525 * 2
def baseEnd_2626525 : Nat := 299704394677875876124075

theorem tailTrace_2626525 : CollatzResearch.WordTrace tailWord_2626525 prefixEnd_2626525 299704394677875876124075 := by
  unfold tailWord_2626525
  simp only [CollatzResearch.WordTrace]
  refine ⟨95797236809555974602249029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63864824539703983068166019 95797236809555974602249029)
  ·
    refine ⟨17961981901791745237921693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95797236809555974602249029 17961981901791745237921693)
    ·
      refine ⟨6735743213171904464220635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17961981901791745237921693 6735743213171904464220635)
      ·
        refine ⟨10103614819757856696330953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6735743213171904464220635 10103614819757856696330953)
        ·
          refine ⟨7577711114818392522248215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10103614819757856696330953 7577711114818392522248215)
          ·
            refine ⟨11366566672227588783372323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577711114818392522248215 11366566672227588783372323)
            ·
              refine ⟨17049850008341383175058485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11366566672227588783372323 17049850008341383175058485)
              ·
                refine ⟨1598423438282004672661733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17049850008341383175058485 1598423438282004672661733)
                ·
                  refine ⟨299704394677875876124075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598423438282004672661733 299704394677875876124075)
                  ·
                    rfl

theorem cell22_2626525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_2626525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626525 prefixEnd_2626525 := by exact prefixLift 2626525
  have htrace : WordTrace (prefixWord ++ tailWord_2626525) baseStart_2626525 baseEnd_2626525 := by
    simpa [prefixWord, tailWord_2626525, baseEnd_2626525] using wordTrace_append hprefix tailTrace_2626525
  have hstable : (prefixWord ++ tailWord_2626525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626525).length < 2 ^ (prefixWord ++ tailWord_2626525).sum := by decide
  have hdescent : baseEnd_2626525 < baseStart_2626525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626527 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 1, 4]
def baseStart_2626527 : Nat := 118140960795 + 2626527 * 2 ^ 59
def prefixEnd_2626527 : Nat := 4983230072969 + 3 ^ 40 * 2626527 * 2
def baseEnd_2626527 : Nat := 899113868674500289822219

theorem tailTrace_2626527 : CollatzResearch.WordTrace tailWord_2626527 prefixEnd_2626527 899113868674500289822219 := by
  unfold tailWord_2626527
  simp only [CollatzResearch.WordTrace]
  refine ⟨95797309755548728943821835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63864873170365819295881223 95797309755548728943821835)
  ·
    refine ⟨143695964633323093415732753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95797309755548728943821835 143695964633323093415732753)
    ·
      refine ⟨107771973474992320061799565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143695964633323093415732753 107771973474992320061799565)
      ·
        refine ⟨40414490053122120023174837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107771973474992320061799565 40414490053122120023174837)
        ·
          refine ⟨3788858442480198752172641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40414490053122120023174837 3788858442480198752172641)
          ·
            refine ⟨2841643831860149064129481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788858442480198752172641 2841643831860149064129481)
            ·
              refine ⟨2131232873895111798097111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841643831860149064129481 2131232873895111798097111)
              ·
                refine ⟨3196849310842667697145667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131232873895111798097111 3196849310842667697145667)
                ·
                  refine ⟨4795273966264001545718501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196849310842667697145667 4795273966264001545718501)
                  ·
                    refine ⟨899113868674500289822219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795273966264001545718501 899113868674500289822219)
                    ·
                      rfl

theorem cell22_2626527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_2626527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626527 prefixEnd_2626527 := by exact prefixLift 2626527
  have htrace : WordTrace (prefixWord ++ tailWord_2626527) baseStart_2626527 baseEnd_2626527 := by
    simpa [prefixWord, tailWord_2626527, baseEnd_2626527] using wordTrace_append hprefix tailTrace_2626527
  have hstable : (prefixWord ++ tailWord_2626527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626527).length < 2 ^ (prefixWord ++ tailWord_2626527).sum := by decide
  have hdescent : baseEnd_2626527 < baseStart_2626527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626570 : List Nat := [3, 1, 2, 2, 3, 3, 2, 6]
def baseStart_2626570 : Nat := 118140960795 + 2626570 * 2 ^ 59
def prefixEnd_2626570 : Nat := 4983230072969 + 3 ^ 40 * 2626570 * 2
def baseEnd_2626570 : Nat := 99903176494806945666343

theorem tailTrace_2626570 : CollatzResearch.WordTrace tailWord_2626570 prefixEnd_2626570 99903176494806945666343 := by
  unfold tailWord_2626570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23949719523598236821909291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63865918729595298191758109 23949719523598236821909291)
  ·
    refine ⟨35924579285397355232863937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23949719523598236821909291 35924579285397355232863937)
    ·
      refine ⟨26943434464048016424647953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35924579285397355232863937 26943434464048016424647953)
      ·
        refine ⟨20207575848036012318485965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26943434464048016424647953 20207575848036012318485965)
        ·
          refine ⟨7577840943013504619432237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20207575848036012318485965 7577840943013504619432237)
          ·
            refine ⟨2841690353630064232287089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7577840943013504619432237 2841690353630064232287089)
            ·
              refine ⟨2131267765222548174215317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841690353630064232287089 2131267765222548174215317)
              ·
                refine ⟨99903176494806945666343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2131267765222548174215317 99903176494806945666343)
                ·
                  rfl

theorem cell22_2626570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_2626570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626570 prefixEnd_2626570 := by exact prefixLift 2626570
  have htrace : WordTrace (prefixWord ++ tailWord_2626570) baseStart_2626570 baseEnd_2626570 := by
    simpa [prefixWord, tailWord_2626570, baseEnd_2626570] using wordTrace_append hprefix tailTrace_2626570
  have hstable : (prefixWord ++ tailWord_2626570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626570).length < 2 ^ (prefixWord ++ tailWord_2626570).sum := by decide
  have hdescent : baseEnd_2626570 < baseStart_2626570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626611 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_2626611 : Nat := 118140960795 + 2626611 * 2 ^ 59
def prefixEnd_2626611 : Nat := 4983230072969 + 3 ^ 40 * 2626611 * 2
def baseEnd_2626611 : Nat := 899142623591152070721961

theorem tailTrace_2626611 : CollatzResearch.WordTrace tailWord_2626611 prefixEnd_2626611 899142623591152070721961 := by
  unfold tailWord_2626611
  simp only [CollatzResearch.WordTrace]
  refine ⟨95800373487244411289879687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63866915658162940859919791 95800373487244411289879687)
  ·
    refine ⟨143700560230866616934819531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95800373487244411289879687 143700560230866616934819531)
    ·
      refine ⟨215550840346299925402229297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143700560230866616934819531 215550840346299925402229297)
      ·
        refine ⟨161663130259724944051671973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215550840346299925402229297 161663130259724944051671973)
        ·
          refine ⟨30311836923698427009688495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161663130259724944051671973 30311836923698427009688495)
          ·
            refine ⟨45467755385547640514532743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30311836923698427009688495 45467755385547640514532743)
            ·
              refine ⟨68201633078321460771799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45467755385547640514532743 68201633078321460771799115)
              ·
                refine ⟨102302449617482191157698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68201633078321460771799115 102302449617482191157698673)
                ·
                  refine ⟨76726837213111643368274005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102302449617482191157698673 76726837213111643368274005)
                  ·
                    refine ⟨899142623591152070721961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76726837213111643368274005 899142623591152070721961)
                    ·
                      rfl

theorem cell22_2626611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_2626611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626611 prefixEnd_2626611 := by exact prefixLift 2626611
  have htrace : WordTrace (prefixWord ++ tailWord_2626611) baseStart_2626611 baseEnd_2626611 := by
    simpa [prefixWord, tailWord_2626611, baseEnd_2626611] using wordTrace_append hprefix tailTrace_2626611
  have hstable : (prefixWord ++ tailWord_2626611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626611).length < 2 ^ (prefixWord ++ tailWord_2626611).sum := by decide
  have hdescent : baseEnd_2626611 < baseStart_2626611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626653 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2626653 : Nat := 118140960795 + 2626653 * 2 ^ 59
def prefixEnd_2626653 : Nat := 4983230072969 + 3 ^ 40 * 2626653 * 2
def baseEnd_2626653 : Nat := 899157001049477961171833

theorem tailTrace_2626653 : CollatzResearch.WordTrace tailWord_2626653 prefixEnd_2626653 899157001049477961171833 := by
  unfold tailWord_2626653
  simp only [CollatzResearch.WordTrace]
  refine ⟨95801905353092252462908613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63867936902061501641939075 95801905353092252462908613)
  ·
    refine ⟨17962857253704797336795365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95801905353092252462908613 17962857253704797336795365)
    ·
      refine ⟨3368035735069649500649131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17962857253704797336795365 3368035735069649500649131)
      ·
        refine ⟨5052053602604474250973697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368035735069649500649131 5052053602604474250973697)
        ·
          refine ⟨3789040201953355688230273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5052053602604474250973697 3789040201953355688230273)
          ·
            refine ⟨2841780151465016766172705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789040201953355688230273 2841780151465016766172705)
            ·
              refine ⟨2131335113598762574629529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841780151465016766172705 2131335113598762574629529)
              ·
                refine ⟨1598501335199071930972147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131335113598762574629529 1598501335199071930972147)
                ·
                  refine ⟨2397752002798607896458221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598501335199071930972147 2397752002798607896458221)
                  ·
                    refine ⟨899157001049477961171833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397752002798607896458221 899157001049477961171833)
                    ·
                      rfl

theorem cell22_2626653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2626653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626653 prefixEnd_2626653 := by exact prefixLift 2626653
  have htrace : WordTrace (prefixWord ++ tailWord_2626653) baseStart_2626653 baseEnd_2626653 := by
    simpa [prefixWord, tailWord_2626653, baseEnd_2626653] using wordTrace_append hprefix tailTrace_2626653
  have hstable : (prefixWord ++ tailWord_2626653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626653).length < 2 ^ (prefixWord ++ tailWord_2626653).sum := by decide
  have hdescent : baseEnd_2626653 < baseStart_2626653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626677 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 6]
def baseStart_2626677 : Nat := 118140960795 + 2626677 * 2 ^ 59
def prefixEnd_2626677 : Nat := 4983230072969 + 3 ^ 40 * 2626677 * 2
def baseEnd_2626677 : Nat := 299721738913316632857253

theorem tailTrace_2626677 : CollatzResearch.WordTrace tailWord_2626677 prefixEnd_2626677 299721738913316632857253 := by
  unfold tailWord_2626677
  simp only [CollatzResearch.WordTrace]
  refine ⟨95802780705005304561782285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63868520470003536374521523 95802780705005304561782285)
  ·
    refine ⟨35926042764376989210668357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95802780705005304561782285 35926042764376989210668357)
    ·
      refine ⟨6736133018320685477000317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35926042764376989210668357 6736133018320685477000317)
      ·
        refine ⟨2526049881870257053875119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6736133018320685477000317 2526049881870257053875119)
        ·
          refine ⟨3789074822805385580812679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526049881870257053875119 3789074822805385580812679)
          ·
            refine ⟨5683612234208078371219019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789074822805385580812679 5683612234208078371219019)
            ·
              refine ⟨8525418351312117556828529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683612234208078371219019 8525418351312117556828529)
              ·
                refine ⟨6394063763484088167621397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8525418351312117556828529 6394063763484088167621397)
                ·
                  refine ⟨299721738913316632857253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6394063763484088167621397 299721738913316632857253)
                  ·
                    rfl

theorem cell22_2626677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_2626677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626677 prefixEnd_2626677 := by exact prefixLift 2626677
  have htrace : WordTrace (prefixWord ++ tailWord_2626677) baseStart_2626677 baseEnd_2626677 := by
    simpa [prefixWord, tailWord_2626677, baseEnd_2626677] using wordTrace_append hprefix tailTrace_2626677
  have hstable : (prefixWord ++ tailWord_2626677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626677).length < 2 ^ (prefixWord ++ tailWord_2626677).sum := by decide
  have hdescent : baseEnd_2626677 < baseStart_2626677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626696 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_2626696 : Nat := 118140960795 + 2626696 * 2 ^ 59
def prefixEnd_2626696 : Nat := 4983230072969 + 3 ^ 40 * 2626696 * 2
def baseEnd_2626696 : Nat := 899171720828240182346701

theorem tailTrace_2626696 : CollatzResearch.WordTrace tailWord_2626696 prefixEnd_2626696 899171720828240182346701 := by
  unfold tailWord_2626696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47901736845968235403361971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63868982461290980537815961 47901736845968235403361971)
  ·
    refine ⟨71852605268952353105042957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47901736845968235403361971 71852605268952353105042957)
    ·
      refine ⟨26944726975857132414391109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71852605268952353105042957 26944726975857132414391109)
      ·
        refine ⟨5052136307973212327698333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26944726975857132414391109 5052136307973212327698333)
        ·
          refine ⟨1894551115489954622886875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5052136307973212327698333 1894551115489954622886875)
          ·
            refine ⟨2841826673234931934330313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894551115489954622886875 2841826673234931934330313)
            ·
              refine ⟨2131370004926198950747735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841826673234931934330313 2131370004926198950747735)
              ·
                refine ⟨3197055007389298426121603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131370004926198950747735 3197055007389298426121603)
                ·
                  refine ⟨4795582511083947639182405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197055007389298426121603 4795582511083947639182405)
                  ·
                    refine ⟨899171720828240182346701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795582511083947639182405 899171720828240182346701)
                    ·
                      rfl

theorem cell22_2626696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_2626696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626696 prefixEnd_2626696 := by exact prefixLift 2626696
  have htrace : WordTrace (prefixWord ++ tailWord_2626696) baseStart_2626696 baseEnd_2626696 := by
    simpa [prefixWord, tailWord_2626696, baseEnd_2626696] using wordTrace_append hprefix tailTrace_2626696
  have hstable : (prefixWord ++ tailWord_2626696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626696).length < 2 ^ (prefixWord ++ tailWord_2626696).sum := by decide
  have hdescent : baseEnd_2626696 < baseStart_2626696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626737 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_2626737 : Nat := 118140960795 + 2626737 * 2 ^ 59
def prefixEnd_2626737 : Nat := 4983230072969 + 3 ^ 40 * 2626737 * 2
def baseEnd_2626737 : Nat := 899185755966129742071575

theorem tailTrace_2626737 : CollatzResearch.WordTrace tailWord_2626737 prefixEnd_2626737 899185755966129742071575 := by
  unfold tailWord_2626737
  simp only [CollatzResearch.WordTrace]
  refine ⟨95804969084787934808966465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63869979389858623205977643 95804969084787934808966465)
  ·
    refine ⟨71853726813590951106724849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95804969084787934808966465 71853726813590951106724849)
    ·
      refine ⟨53890295110193213330043637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71853726813590951106724849 53890295110193213330043637)
      ·
        refine ⟨5052215166580613749691591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53890295110193213330043637 5052215166580613749691591)
        ·
          refine ⟨7578322749870920624537387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052215166580613749691591 7578322749870920624537387)
          ·
            refine ⟨11367484124806380936806081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578322749870920624537387 11367484124806380936806081)
            ·
              refine ⟨8525613093604785702604561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11367484124806380936806081 8525613093604785702604561)
              ·
                refine ⟨6394209820203589276953421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8525613093604785702604561 6394209820203589276953421)
                ·
                  refine ⟨2397828682576345978857533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6394209820203589276953421 2397828682576345978857533)
                  ·
                    refine ⟨899185755966129742071575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397828682576345978857533 899185755966129742071575)
                    ·
                      rfl

theorem cell22_2626737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_2626737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626737 prefixEnd_2626737 := by exact prefixLift 2626737
  have htrace : WordTrace (prefixWord ++ tailWord_2626737) baseStart_2626737 baseEnd_2626737 := by
    simpa [prefixWord, tailWord_2626737, baseEnd_2626737] using wordTrace_append hprefix tailTrace_2626737
  have hstable : (prefixWord ++ tailWord_2626737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626737).length < 2 ^ (prefixWord ++ tailWord_2626737).sum := by decide
  have hdescent : baseEnd_2626737 < baseStart_2626737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626750 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2626750 : Nat := 118140960795 + 2626750 * 2 ^ 59
def prefixEnd_2626750 : Nat := 4983230072969 + 3 ^ 40 * 2626750 * 2
def baseEnd_2626750 : Nat := 299730068710600680498845

theorem tailTrace_2626750 : CollatzResearch.WordTrace tailWord_2626750 prefixEnd_2626750 299730068710600680498845 := by
  unfold tailWord_2626750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11975680404217604753648713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63870295489160558686126469 11975680404217604753648713)
  ·
    refine ⟨8981760303163203565236535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11975680404217604753648713 8981760303163203565236535)
    ·
      refine ⟨13472640454744805347854803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981760303163203565236535 13472640454744805347854803)
      ·
        refine ⟨20208960682117208021782205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13472640454744805347854803 20208960682117208021782205)
        ·
          refine ⟨7578360255793953008168327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20208960682117208021782205 7578360255793953008168327)
          ·
            refine ⟨11367540383690929512252491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578360255793953008168327 11367540383690929512252491)
            ·
              refine ⟨17051310575536394268378737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367540383690929512252491 17051310575536394268378737)
              ·
                refine ⟨12788482931652295701284053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17051310575536394268378737 12788482931652295701284053)
                ·
                  refine ⟨299730068710600680498845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12788482931652295701284053 299730068710600680498845)
                  ·
                    rfl

theorem cell22_2626750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2626750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626750 prefixEnd_2626750 := by exact prefixLift 2626750
  have htrace : WordTrace (prefixWord ++ tailWord_2626750) baseStart_2626750 baseEnd_2626750 := by
    simpa [prefixWord, tailWord_2626750, baseEnd_2626750] using wordTrace_append hprefix tailTrace_2626750
  have hstable : (prefixWord ++ tailWord_2626750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626750).length < 2 ^ (prefixWord ++ tailWord_2626750).sum := by decide
  have hdescent : baseEnd_2626750 < baseStart_2626750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626797 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2626797 : Nat := 118140960795 + 2626797 * 2 ^ 59
def prefixEnd_2626797 : Nat := 4983230072969 + 3 ^ 40 * 2626797 * 2
def baseEnd_2626797 : Nat := 899206295192309585571391

theorem tailTrace_2626797 : CollatzResearch.WordTrace tailWord_2626797 prefixEnd_2626797 899206295192309585571391 := by
  unfold tailWord_2626797
  simp only [CollatzResearch.WordTrace]
  refine ⟨95807157464570565056150645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63871438309713710037433763 95807157464570565056150645)
  ·
    refine ⟨8981921012303490474014123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95807157464570565056150645 8981921012303490474014123)
    ·
      refine ⟨13472881518455235711021185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981921012303490474014123 13472881518455235711021185)
      ·
        refine ⟨10104661138841426783265889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13472881518455235711021185 10104661138841426783265889)
        ·
          refine ⟨7578495854131070087449417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10104661138841426783265889 7578495854131070087449417)
          ·
            refine ⟨5683871890598302565587063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7578495854131070087449417 5683871890598302565587063)
            ·
              refine ⟨8525807835897453848380595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683871890598302565587063 8525807835897453848380595)
              ·
                refine ⟨12788711753846180772570893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525807835897453848380595 12788711753846180772570893)
                ·
                  refine ⟨4795766907692317789714085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12788711753846180772570893 4795766907692317789714085)
                  ·
                    refine ⟨899206295192309585571391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795766907692317789714085 899206295192309585571391)
                    ·
                      rfl

theorem cell22_2626797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2626797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626797 prefixEnd_2626797 := by exact prefixLift 2626797
  have htrace : WordTrace (prefixWord ++ tailWord_2626797) baseStart_2626797 baseEnd_2626797 := by
    simpa [prefixWord, tailWord_2626797, baseEnd_2626797] using wordTrace_append hprefix tailTrace_2626797
  have hstable : (prefixWord ++ tailWord_2626797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626797).length < 2 ^ (prefixWord ++ tailWord_2626797).sum := by decide
  have hdescent : baseEnd_2626797 < baseStart_2626797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626810 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_2626810 : Nat := 118140960795 + 2626810 * 2 ^ 59
def prefixEnd_2626810 : Nat := 4983230072969 + 3 ^ 40 * 2626810 * 2
def baseEnd_2626810 : Nat := 899210745357981884996351

theorem tailTrace_2626810 : CollatzResearch.WordTrace tailWord_2626810 prefixEnd_2626810 899210745357981884996351 := by
  unfold tailWord_2626810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951907903380867069093471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63871754409015645517582589 23951907903380867069093471)
  ·
    refine ⟨35927861855071300603640207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23951907903380867069093471 35927861855071300603640207)
    ·
      refine ⟨53891792782606950905460311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35927861855071300603640207 53891792782606950905460311)
      ·
        refine ⟨80837689173910426358190467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53891792782606950905460311 80837689173910426358190467)
        ·
          refine ⟨121256533760865639537285701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80837689173910426358190467 121256533760865639537285701)
          ·
            refine ⟨22735600080162307413241069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121256533760865639537285701 22735600080162307413241069)
            ·
              refine ⟨8525850030060865279965401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22735600080162307413241069 8525850030060865279965401)
              ·
                refine ⟨6394387522545648959974051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8525850030060865279965401 6394387522545648959974051)
                ·
                  refine ⟨9591581283818473439961077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6394387522545648959974051 9591581283818473439961077)
                  ·
                    refine ⟨899210745357981884996351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9591581283818473439961077 899210745357981884996351)
                    ·
                      rfl

theorem cell22_2626810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_2626810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626810 prefixEnd_2626810 := by exact prefixLift 2626810
  have htrace : WordTrace (prefixWord ++ tailWord_2626810) baseStart_2626810 baseEnd_2626810 := by
    simpa [prefixWord, tailWord_2626810, baseEnd_2626810] using wordTrace_append hprefix tailTrace_2626810
  have hstable : (prefixWord ++ tailWord_2626810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626810).length < 2 ^ (prefixWord ++ tailWord_2626810).sum := by decide
  have hdescent : baseEnd_2626810 < baseStart_2626810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626823 : List Nat := [1, 1, 4, 16]
def baseStart_2626823 : Nat := 118140960795 + 2626823 * 2 ^ 59
def prefixEnd_2626823 : Nat := 4983230072969 + 3 ^ 40 * 2626823 * 2
def baseEnd_2626823 : Nat := 1233491351884299292759

theorem tailTrace_2626823 : CollatzResearch.WordTrace tailWord_2626823 prefixEnd_2626823 1233491351884299292759 := by
  unfold tailWord_2626823
  simp only [CollatzResearch.WordTrace]
  refine ⟨95808105762476371496597123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63872070508317580997731415 95808105762476371496597123)
  ·
    refine ⟨143712158643714557244895685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95808105762476371496597123 143712158643714557244895685)
    ·
      refine ⟨26946029745696479483417941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143712158643714557244895685 26946029745696479483417941)
      ·
        refine ⟨1233491351884299292759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 26946029745696479483417941 1233491351884299292759)
        ·
          rfl

theorem cell22_2626823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 16].length) (baseStart_2626823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626823 prefixEnd_2626823 := by exact prefixLift 2626823
  have htrace : WordTrace (prefixWord ++ tailWord_2626823) baseStart_2626823 baseEnd_2626823 := by
    simpa [prefixWord, tailWord_2626823, baseEnd_2626823] using wordTrace_append hprefix tailTrace_2626823
  have hstable : (prefixWord ++ tailWord_2626823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626823).length < 2 ^ (prefixWord ++ tailWord_2626823).sum := by decide
  have hdescent : baseEnd_2626823 < baseStart_2626823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626825 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_2626825 : Nat := 118140960795 + 2626825 * 2 ^ 59
def prefixEnd_2626825 : Nat := 4983230072969 + 3 ^ 40 * 2626825 * 2
def baseEnd_2626825 : Nat := 899215880164526845871305

theorem tailTrace_2626825 : CollatzResearch.WordTrace tailWord_2626825 prefixEnd_2626825 899215880164526845871305 := by
  unfold tailWord_2626825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95808178708469125838169929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63872119138979417225446619 95808178708469125838169929)
  ·
    refine ⟨71856134031351844378627447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95808178708469125838169929 71856134031351844378627447)
    ·
      refine ⟨107784201047027766567941171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71856134031351844378627447 107784201047027766567941171)
      ·
        refine ⟨161676301570541649851911757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107784201047027766567941171 161676301570541649851911757)
        ·
          refine ⟨60628613088953118694466909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161676301570541649851911757 60628613088953118694466909)
          ·
            refine ⟨22735729908357419510425091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60628613088953118694466909 22735729908357419510425091)
            ·
              refine ⟨34103594862536129265637637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22735729908357419510425091 34103594862536129265637637)
              ·
                refine ⟨6394424036725524237307057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34103594862536129265637637 6394424036725524237307057)
                ·
                  refine ⟨4795818027544143177980293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394424036725524237307057 4795818027544143177980293)
                  ·
                    refine ⟨899215880164526845871305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795818027544143177980293 899215880164526845871305)
                    ·
                      rfl

theorem cell22_2626825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_2626825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626825 prefixEnd_2626825 := by exact prefixLift 2626825
  have htrace : WordTrace (prefixWord ++ tailWord_2626825) baseStart_2626825 baseEnd_2626825 := by
    simpa [prefixWord, tailWord_2626825, baseEnd_2626825] using wordTrace_append hprefix tailTrace_2626825
  have hstable : (prefixWord ++ tailWord_2626825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626825).length < 2 ^ (prefixWord ++ tailWord_2626825).sum := by decide
  have hdescent : baseEnd_2626825 < baseStart_2626825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626827 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 2, 3]
def baseStart_2626827 : Nat := 118140960795 + 2626827 * 2 ^ 59
def prefixEnd_2626827 : Nat := 4983230072969 + 3 ^ 40 * 2626827 * 2
def baseEnd_2626827 : Nat := 899216564805399507321299

theorem tailTrace_2626827 : CollatzResearch.WordTrace tailWord_2626827 prefixEnd_2626827 899216564805399507321299 := by
  unfold tailWord_2626827
  simp only [CollatzResearch.WordTrace]
  refine ⟨95808251654461880179742735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63872167769641253453161823 95808251654461880179742735)
  ·
    refine ⟨143712377481692820269614103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95808251654461880179742735 143712377481692820269614103)
    ·
      refine ⟨215568566222539230404421155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143712377481692820269614103 215568566222539230404421155)
      ·
        refine ⟨323352849333808845606631733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215568566222539230404421155 323352849333808845606631733)
        ·
          refine ⟨30314329625044579275621725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323352849333808845606631733 30314329625044579275621725)
          ·
            refine ⟨11367873609391717228358147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30314329625044579275621725 11367873609391717228358147)
            ·
              refine ⟨17051810414087575842537221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367873609391717228358147 17051810414087575842537221)
              ·
                refine ⟨3197214452641420470475729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17051810414087575842537221 3197214452641420470475729)
                ·
                  refine ⟨2397910839481065352856797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197214452641420470475729 2397910839481065352856797)
                  ·
                    refine ⟨899216564805399507321299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397910839481065352856797 899216564805399507321299)
                    ·
                      rfl

theorem cell22_2626827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3].length) (baseStart_2626827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626827 prefixEnd_2626827 := by exact prefixLift 2626827
  have htrace : WordTrace (prefixWord ++ tailWord_2626827) baseStart_2626827 baseEnd_2626827 := by
    simpa [prefixWord, tailWord_2626827, baseEnd_2626827] using wordTrace_append hprefix tailTrace_2626827
  have hstable : (prefixWord ++ tailWord_2626827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626827).length < 2 ^ (prefixWord ++ tailWord_2626827).sum := by decide
  have hdescent : baseEnd_2626827 < baseStart_2626827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626840 : List Nat := [2, 1, 2, 3, 1, 3, 3, 7]
def baseStart_2626840 : Nat := 118140960795 + 2626840 * 2 ^ 59
def prefixEnd_2626840 : Nat := 4983230072969 + 3 ^ 40 * 2626840 * 2
def baseEnd_2626840 : Nat := 99913446107896867416251

theorem tailTrace_2626840 : CollatzResearch.WordTrace tailWord_2626840 prefixEnd_2626840 99913446107896867416251 := by
  unfold tailWord_2626840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47904362901707391699982987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63872483868943188933310649 47904362901707391699982987)
  ·
    refine ⟨71856544352561087549974481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47904362901707391699982987 71856544352561087549974481)
    ·
      refine ⟨53892408264420815662480861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71856544352561087549974481 53892408264420815662480861)
      ·
        refine ⟨20209653099157805873430323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53892408264420815662480861 20209653099157805873430323)
        ·
          refine ⟨30314479648736708810145485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209653099157805873430323 30314479648736708810145485)
          ·
            refine ⟨11367929868276265803804557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30314479648736708810145485 11367929868276265803804557)
            ·
              refine ⟨4262973700603599676426709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11367929868276265803804557 4262973700603599676426709)
              ·
                refine ⟨99913446107896867416251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4262973700603599676426709 99913446107896867416251)
                ·
                  rfl

theorem cell22_2626840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_2626840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626840 prefixEnd_2626840 := by exact prefixLift 2626840
  have htrace : WordTrace (prefixWord ++ tailWord_2626840) baseStart_2626840 baseEnd_2626840 := by
    simpa [prefixWord, tailWord_2626840, baseEnd_2626840] using wordTrace_append hprefix tailTrace_2626840
  have hstable : (prefixWord ++ tailWord_2626840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626840).length < 2 ^ (prefixWord ++ tailWord_2626840).sum := by decide
  have hdescent : baseEnd_2626840 < baseStart_2626840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626889 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 1, 3]
def baseStart_2626889 : Nat := 118140960795 + 2626889 * 2 ^ 59
def prefixEnd_2626889 : Nat := 4983230072969 + 3 ^ 40 * 2626889 * 2
def baseEnd_2626889 : Nat := 899237788672452012271109

theorem tailTrace_2626889 : CollatzResearch.WordTrace tailWord_2626889 prefixEnd_2626889 899237788672452012271109 := by
  unfold tailWord_2626889
  simp only [CollatzResearch.WordTrace]
  refine ⟨95810512980237264768499721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63873675320158176512333147 95810512980237264768499721)
  ·
    refine ⟨71857884735177948576374791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95810512980237264768499721 71857884735177948576374791)
    ·
      refine ⟨107786827102766922864562187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71857884735177948576374791 107786827102766922864562187)
      ·
        refine ⟨161680240654150384296843281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107786827102766922864562187 161680240654150384296843281)
        ·
          refine ⟨121260180490612788222632461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161680240654150384296843281 121260180490612788222632461)
          ·
            refine ⟨45472567683979795583487173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121260180490612788222632461 45472567683979795583487173)
            ·
              refine ⟨8526106440746211671903845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45472567683979795583487173 8526106440746211671903845)
              ·
                refine ⟨1598644957639914688481971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8526106440746211671903845 1598644957639914688481971)
                ·
                  refine ⟨2397967436459872032722957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598644957639914688481971 2397967436459872032722957)
                  ·
                    refine ⟨899237788672452012271109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397967436459872032722957 899237788672452012271109)
                    ·
                      rfl

theorem cell22_2626889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_2626889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626889 prefixEnd_2626889 := by exact prefixLift 2626889
  have htrace : WordTrace (prefixWord ++ tailWord_2626889) baseStart_2626889 baseEnd_2626889 := by
    simpa [prefixWord, tailWord_2626889, baseEnd_2626889] using wordTrace_append hprefix tailTrace_2626889
  have hstable : (prefixWord ++ tailWord_2626889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626889).length < 2 ^ (prefixWord ++ tailWord_2626889).sum := by decide
  have hdescent : baseEnd_2626889 < baseStart_2626889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626947 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 6]
def baseStart_2626947 : Nat := 118140960795 + 2626947 * 2 ^ 59
def prefixEnd_2626947 : Nat := 4983230072969 + 3 ^ 40 * 2626947 * 2
def baseEnd_2626947 : Nat := 299752547752586398106977

theorem tailTrace_2626947 : CollatzResearch.WordTrace tailWord_2626947 prefixEnd_2626947 299752547752586398106977 := by
  unfold tailWord_2626947
  simp only [CollatzResearch.WordTrace]
  refine ⟨95812628414027140674111095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63875085609351427116074063 95812628414027140674111095)
  ·
    refine ⟨143718942621040711011166643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95812628414027140674111095 143718942621040711011166643)
    ·
      refine ⟨215578413931561066516749965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143718942621040711011166643 215578413931561066516749965)
      ·
        refine ⟨80841905224335399943781237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215578413931561066516749965 80841905224335399943781237)
        ·
          refine ⟨7578928614781443744729491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80841905224335399943781237 7578928614781443744729491)
          ·
            refine ⟨11368392922172165617094237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578928614781443744729491 11368392922172165617094237)
            ·
              refine ⟨4263147345814562106410339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11368392922172165617094237 4263147345814562106410339)
              ·
                refine ⟨6394721018721843159615509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263147345814562106410339 6394721018721843159615509)
                ·
                  refine ⟨299752547752586398106977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6394721018721843159615509 299752547752586398106977)
                  ·
                    rfl

theorem cell22_2626947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 6].length) (baseStart_2626947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2626947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2626947 prefixEnd_2626947 := by exact prefixLift 2626947
  have htrace : WordTrace (prefixWord ++ tailWord_2626947) baseStart_2626947 baseEnd_2626947 := by
    simpa [prefixWord, tailWord_2626947, baseEnd_2626947] using wordTrace_append hprefix tailTrace_2626947
  have hstable : (prefixWord ++ tailWord_2626947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626947).length < 2 ^ (prefixWord ++ tailWord_2626947).sum := by decide
  have hdescent : baseEnd_2626947 < baseStart_2626947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627007 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 7, 3]
def baseStart_2627007 : Nat := 118140960795 + 2627007 * 2 ^ 59
def prefixEnd_2627007 : Nat := 4983230072969 + 3 ^ 40 * 2627007 * 2
def baseEnd_2627007 : Nat := 899278182483939037820747

theorem tailTrace_2627007 : CollatzResearch.WordTrace tailWord_2627007 prefixEnd_2627007 899278182483939037820747 := by
  unfold tailWord_2627007
  simp only [CollatzResearch.WordTrace]
  refine ⟨95814816793809770921295275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63876544529206513947530183 95814816793809770921295275)
  ·
    refine ⟨143722225190714656381942913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95814816793809770921295275 143722225190714656381942913)
    ·
      refine ⟨107791668893035992286457185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143722225190714656381942913 107791668893035992286457185)
      ·
        refine ⟨80843751669776994214842889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107791668893035992286457185 80843751669776994214842889)
        ·
          refine ⟨60632813752332745661132167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80843751669776994214842889 60632813752332745661132167)
          ·
            refine ⟨90949220628499118491698251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60632813752332745661132167 90949220628499118491698251)
            ·
              refine ⟨136423830942748677737547377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90949220628499118491698251 136423830942748677737547377)
              ·
                refine ⟨102317873207061508303160533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136423830942748677737547377 102317873207061508303160533)
                ·
                  refine ⟨2398075153290504100855325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102317873207061508303160533 2398075153290504100855325)
                  ·
                    refine ⟨899278182483939037820747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398075153290504100855325 899278182483939037820747)
                    ·
                      rfl

theorem cell22_2627007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_2627007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627007 prefixEnd_2627007 := by exact prefixLift 2627007
  have htrace : WordTrace (prefixWord ++ tailWord_2627007) baseStart_2627007 baseEnd_2627007 := by
    simpa [prefixWord, tailWord_2627007, baseEnd_2627007] using wordTrace_append hprefix tailTrace_2627007
  have hstable : (prefixWord ++ tailWord_2627007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627007).length < 2 ^ (prefixWord ++ tailWord_2627007).sum := by decide
  have hdescent : baseEnd_2627007 < baseStart_2627007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627028 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2627028 : Nat := 118140960795 + 2627028 * 2 ^ 59
def prefixEnd_2627028 : Nat := 4983230072969 + 3 ^ 40 * 2627028 * 2
def baseEnd_2627028 : Nat := 899285371213101983045683

theorem tailTrace_2627028 : CollatzResearch.WordTrace tailWord_2627028 prefixEnd_2627028 899285371213101983045683 := by
  unfold tailWord_2627028
  simp only [CollatzResearch.WordTrace]
  refine ⟨47907791363366845753904869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63877055151155794338539825 47907791363366845753904869)
  ·
    refine ⟨8982710880631283578857163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47907791363366845753904869 8982710880631283578857163)
    ·
      refine ⟨13474066320946925368285745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8982710880631283578857163 13474066320946925368285745)
      ·
        refine ⟨10105549740710194026214309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13474066320946925368285745 10105549740710194026214309)
        ·
          refine ⟨1894790576383161379915183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10105549740710194026214309 1894790576383161379915183)
          ·
            refine ⟨2842185864574742069872775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894790576383161379915183 2842185864574742069872775)
            ·
              refine ⟨4263278796862113104809163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842185864574742069872775 4263278796862113104809163)
              ·
                refine ⟨6394918195293169657213745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263278796862113104809163 6394918195293169657213745)
                ·
                  refine ⟨4796188646469877242910309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6394918195293169657213745 4796188646469877242910309)
                  ·
                    refine ⟨899285371213101983045683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796188646469877242910309 899285371213101983045683)
                    ·
                      rfl

theorem cell22_2627028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2627028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627028 prefixEnd_2627028 := by exact prefixLift 2627028
  have htrace : WordTrace (prefixWord ++ tailWord_2627028) baseStart_2627028 baseEnd_2627028 := by
    simpa [prefixWord, tailWord_2627028, baseEnd_2627028] using wordTrace_append hprefix tailTrace_2627028
  have hstable : (prefixWord ++ tailWord_2627028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627028).length < 2 ^ (prefixWord ++ tailWord_2627028).sum := by decide
  have hdescent : baseEnd_2627028 < baseStart_2627028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627041 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 1, 3]
def baseStart_2627041 : Nat := 118140960795 + 2627041 * 2 ^ 59
def prefixEnd_2627041 : Nat := 4983230072969 + 3 ^ 40 * 2627041 * 2
def baseEnd_2627041 : Nat := 899289821378774282470643

theorem tailTrace_2627041 : CollatzResearch.WordTrace tailWord_2627041 prefixEnd_2627041 899289821378774282470643 := by
  unfold tailWord_2627041
  simp only [CollatzResearch.WordTrace]
  refine ⟨95816056875686594728032977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63877371250457729818688651 95816056875686594728032977)
  ·
    refine ⟨71862042656764946046024733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95816056875686594728032977 71862042656764946046024733)
    ·
      refine ⟨26948265996286854767259275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71862042656764946046024733 26948265996286854767259275)
      ·
        refine ⟨40422398994430282150888913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26948265996286854767259275 40422398994430282150888913)
        ·
          refine ⟨30316799245822711613166685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40422398994430282150888913 30316799245822711613166685)
          ·
            refine ⟨11368799717183516854937507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30316799245822711613166685 11368799717183516854937507)
            ·
              refine ⟨17053199575775275282406261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11368799717183516854937507 17053199575775275282406261)
              ·
                refine ⟨1598737460228932057725587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17053199575775275282406261 1598737460228932057725587)
                ·
                  refine ⟨2398106190343398086588381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598737460228932057725587 2398106190343398086588381)
                  ·
                    refine ⟨899289821378774282470643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398106190343398086588381 899289821378774282470643)
                    ·
                      rfl

theorem cell22_2627041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_2627041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627041 prefixEnd_2627041 := by exact prefixLift 2627041
  have htrace : WordTrace (prefixWord ++ tailWord_2627041) baseStart_2627041 baseEnd_2627041 := by
    simpa [prefixWord, tailWord_2627041, baseEnd_2627041] using wordTrace_append hprefix tailTrace_2627041
  have hstable : (prefixWord ++ tailWord_2627041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627041).length < 2 ^ (prefixWord ++ tailWord_2627041).sum := by decide
  have hdescent : baseEnd_2627041 < baseStart_2627041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627058 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_2627058 : Nat := 118140960795 + 2627058 * 2 ^ 59
def prefixEnd_2627058 : Nat := 4983230072969 + 3 ^ 40 * 2627058 * 2
def baseEnd_2627058 : Nat := 899295640826191904795591

theorem tailTrace_2627058 : CollatzResearch.WordTrace tailWord_2627058 prefixEnd_2627058 899295640826191904795591 := by
  unfold tailWord_2627058
  simp only [CollatzResearch.WordTrace]
  refine ⟨23954169229156251657850457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63877784611083337754267885 23954169229156251657850457)
  ·
    refine ⟨17965626921867188743387843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23954169229156251657850457 17965626921867188743387843)
    ·
      refine ⟨26948440382800783115081765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17965626921867188743387843 26948440382800783115081765)
      ·
        refine ⟨5052832571775146834077831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26948440382800783115081765 5052832571775146834077831)
        ·
          refine ⟨7579248857662720251116747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052832571775146834077831 7579248857662720251116747)
          ·
            refine ⟨11368873286494080376675121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7579248857662720251116747 11368873286494080376675121)
            ·
              refine ⟨8526654964870560282506341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11368873286494080376675121 8526654964870560282506341)
              ·
                refine ⟨1598747805913230052969939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8526654964870560282506341 1598747805913230052969939)
                ·
                  refine ⟨2398121708869845079454909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598747805913230052969939 2398121708869845079454909)
                  ·
                    refine ⟨899295640826191904795591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398121708869845079454909 899295640826191904795591)
                    ·
                      rfl

theorem cell22_2627058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_2627058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627058 prefixEnd_2627058 := by exact prefixLift 2627058
  have htrace : WordTrace (prefixWord ++ tailWord_2627058) baseStart_2627058 baseEnd_2627058 := by
    simpa [prefixWord, tailWord_2627058, baseEnd_2627058] using wordTrace_append hprefix tailTrace_2627058
  have hstable : (prefixWord ++ tailWord_2627058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627058).length < 2 ^ (prefixWord ++ tailWord_2627058).sum := by decide
  have hdescent : baseEnd_2627058 < baseStart_2627058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627092 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2627092 : Nat := 118140960795 + 2627092 * 2 ^ 59
def prefixEnd_2627092 : Nat := 4983230072969 + 3 ^ 40 * 2627092 * 2
def baseEnd_2627092 : Nat := 899307279721027149445487

theorem tailTrace_2627092 : CollatzResearch.WordTrace tailWord_2627092 prefixEnd_2627092 899307279721027149445487 := by
  unfold tailWord_2627092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47908958499250915219069765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63878611332334553625426353 47908958499250915219069765)
  ·
    refine ⟨8982929718609546603575581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47908958499250915219069765 8982929718609546603575581)
    ·
      refine ⟨3368598644478579976340843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8982929718609546603575581 3368598644478579976340843)
      ·
        refine ⟨5052897966717869964511265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368598644478579976340843 5052897966717869964511265)
        ·
          refine ⟨3789673475038402473383449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5052897966717869964511265 3789673475038402473383449)
          ·
            refine ⟨2842255106278801855037587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789673475038402473383449 2842255106278801855037587)
            ·
              refine ⟨4263382659418202782556381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842255106278801855037587 4263382659418202782556381)
              ·
                refine ⟨1598768497281826043458643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4263382659418202782556381 1598768497281826043458643)
                ·
                  refine ⟨2398152745922739065187965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598768497281826043458643 2398152745922739065187965)
                  ·
                    refine ⟨899307279721027149445487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398152745922739065187965 899307279721027149445487)
                    ·
                      rfl

theorem cell22_2627092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2627092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627092 prefixEnd_2627092 := by exact prefixLift 2627092
  have htrace : WordTrace (prefixWord ++ tailWord_2627092) baseStart_2627092 baseEnd_2627092 := by
    simpa [prefixWord, tailWord_2627092, baseEnd_2627092] using wordTrace_append hprefix tailTrace_2627092
  have hstable : (prefixWord ++ tailWord_2627092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627092).length < 2 ^ (prefixWord ++ tailWord_2627092).sum := by decide
  have hdescent : baseEnd_2627092 < baseStart_2627092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627127 : List Nat := [1, 1, 3, 1, 2, 4, 1, 9]
def baseStart_2627127 : Nat := 118140960795 + 2627127 * 2 ^ 59
def prefixEnd_2627127 : Nat := 4983230072969 + 3 ^ 40 * 2627127 * 2
def baseEnd_2627127 : Nat := 99924362326255413868931

theorem tailTrace_2627127 : CollatzResearch.WordTrace tailWord_2627127 prefixEnd_2627127 99924362326255413868931 := by
  unfold tailWord_2627127
  simp only [CollatzResearch.WordTrace]
  refine ⟨95819193553375031415663635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63879462368916687610442423 95819193553375031415663635)
  ·
    refine ⟨143728790330062547123495453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95819193553375031415663635 143728790330062547123495453)
    ·
      refine ⟨53898296373773455171310795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143728790330062547123495453 53898296373773455171310795)
      ·
        refine ⟨80847444560660182756966193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53898296373773455171310795 80847444560660182756966193)
        ·
          refine ⟨60635583420495137067724645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80847444560660182756966193 60635583420495137067724645)
          ·
            refine ⟨11369171891342838200198371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60635583420495137067724645 11369171891342838200198371)
            ·
              refine ⟨17053757837014257300297557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369171891342838200198371 17053757837014257300297557)
              ·
                refine ⟨99924362326255413868931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17053757837014257300297557 99924362326255413868931)
                ·
                  rfl

theorem cell22_2627127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 9].length) (baseStart_2627127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627127 prefixEnd_2627127 := by exact prefixLift 2627127
  have htrace : WordTrace (prefixWord ++ tailWord_2627127) baseStart_2627127 baseEnd_2627127 := by
    simpa [prefixWord, tailWord_2627127, baseEnd_2627127] using wordTrace_append hprefix tailTrace_2627127
  have hstable : (prefixWord ++ tailWord_2627127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627127).length < 2 ^ (prefixWord ++ tailWord_2627127).sum := by decide
  have hdescent : baseEnd_2627127 < baseStart_2627127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627210 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_2627210 : Nat := 118140960795 + 2627210 * 2 ^ 59
def prefixEnd_2627210 : Nat := 4983230072969 + 3 ^ 40 * 2627210 * 2
def baseEnd_2627210 : Nat := 899347673532514174995125

theorem tailTrace_2627210 : CollatzResearch.WordTrace tailWord_2627210 prefixEnd_2627210 899347673532514174995125 := by
  unfold tailWord_2627210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955555203018584147733771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63881480541382891060623389 23955555203018584147733771)
  ·
    refine ⟨35933332804527876221600657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23955555203018584147733771 35933332804527876221600657)
    ·
      refine ⟨26949999603395907166200493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35933332804527876221600657 26949999603395907166200493)
      ·
        refine ⟨10106249851273465187325185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26949999603395907166200493 10106249851273465187325185)
        ·
          refine ⟨7579687388455098890493889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10106249851273465187325185 7579687388455098890493889)
          ·
            refine ⟨5684765541341324167870417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7579687388455098890493889 5684765541341324167870417)
            ·
              refine ⟨4263574156005993125902813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5684765541341324167870417 4263574156005993125902813)
              ·
                refine ⟨1598840308502247422213555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4263574156005993125902813 1598840308502247422213555)
                ·
                  refine ⟨2398260462753371133320333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598840308502247422213555 2398260462753371133320333)
                  ·
                    refine ⟨899347673532514174995125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398260462753371133320333 899347673532514174995125)
                    ·
                      rfl

theorem cell22_2627210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_2627210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627210 prefixEnd_2627210 := by exact prefixLift 2627210
  have htrace : WordTrace (prefixWord ++ tailWord_2627210) baseStart_2627210 baseEnd_2627210 := by
    simpa [prefixWord, tailWord_2627210, baseEnd_2627210] using wordTrace_append hprefix tailTrace_2627210
  have hstable : (prefixWord ++ tailWord_2627210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627210).length < 2 ^ (prefixWord ++ tailWord_2627210).sum := by decide
  have hdescent : baseEnd_2627210 < baseStart_2627210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627264 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_2627264 : Nat := 118140960795 + 2627264 * 2 ^ 59
def prefixEnd_2627264 : Nat := 4983230072969 + 3 ^ 40 * 2627264 * 2
def baseEnd_2627264 : Nat := 899366158836076034144959

theorem tailTrace_2627264 : CollatzResearch.WordTrace tailWord_2627264 prefixEnd_2627264 899366158836076034144959 := by
  unfold tailWord_2627264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47912095176939351906700423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63882793569252469208933897 47912095176939351906700423)
  ·
    refine ⟨71868142765409027860050635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47912095176939351906700423 71868142765409027860050635)
    ·
      refine ⟨107802214148113541790075953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71868142765409027860050635 107802214148113541790075953)
      ·
        refine ⟨80851660611085156342556965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107802214148113541790075953 80851660611085156342556965)
        ·
          refine ⟨15159686364578466814229431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80851660611085156342556965 15159686364578466814229431)
          ·
            refine ⟨22739529546867700221344147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15159686364578466814229431 22739529546867700221344147)
            ·
              refine ⟨34109294320301550332016221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22739529546867700221344147 34109294320301550332016221)
              ·
                refine ⟨12790985370113081374506083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34109294320301550332016221 12790985370113081374506083)
                ·
                  refine ⟨19186478055169622061759125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12790985370113081374506083 19186478055169622061759125)
                  ·
                    refine ⟨899366158836076034144959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19186478055169622061759125 899366158836076034144959)
                    ·
                      rfl

theorem cell22_2627264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_2627264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627264 prefixEnd_2627264 := by exact prefixLift 2627264
  have htrace : WordTrace (prefixWord ++ tailWord_2627264) baseStart_2627264 baseEnd_2627264 := by
    simpa [prefixWord, tailWord_2627264, baseEnd_2627264] using wordTrace_append hprefix tailTrace_2627264
  have hstable : (prefixWord ++ tailWord_2627264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627264).length < 2 ^ (prefixWord ++ tailWord_2627264).sum := by decide
  have hdescent : baseEnd_2627264 < baseStart_2627264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627281 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2627281 : Nat := 118140960795 + 2627281 * 2 ^ 59
def prefixEnd_2627281 : Nat := 4983230072969 + 3 ^ 40 * 2627281 * 2
def baseEnd_2627281 : Nat := 899371978283493656469907

theorem tailTrace_2627281 : CollatzResearch.WordTrace tailWord_2627281 prefixEnd_2627281 899371978283493656469907 := by
  unfold tailWord_2627281
  simp only [CollatzResearch.WordTrace]
  refine ⟨95824810394817115716769697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63883206929878077144513131 95824810394817115716769697)
  ·
    refine ⟨71868607796112836787577273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95824810394817115716769697 71868607796112836787577273)
    ·
      refine ⟨53901455847084627590682955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71868607796112836787577273 53901455847084627590682955)
      ·
        refine ⟨80852183770626941386024433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53901455847084627590682955 80852183770626941386024433)
        ·
          refine ⟨60639137827970206039518325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80852183770626941386024433 60639137827970206039518325)
          ·
            refine ⟨5684919171372206816204843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60639137827970206039518325 5684919171372206816204843)
            ·
              refine ⟨8527378757058310224307265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684919171372206816204843 8527378757058310224307265)
              ·
                refine ⟨6395534067793732668230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8527378757058310224307265 6395534067793732668230449)
                ·
                  refine ⟨4796650550845299501172837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395534067793732668230449 4796650550845299501172837)
                  ·
                    refine ⟨899371978283493656469907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796650550845299501172837 899371978283493656469907)
                    ·
                      rfl

theorem cell22_2627281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2627281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627281 prefixEnd_2627281 := by exact prefixLift 2627281
  have htrace : WordTrace (prefixWord ++ tailWord_2627281) baseStart_2627281 baseEnd_2627281 := by
    simpa [prefixWord, tailWord_2627281, baseEnd_2627281] using wordTrace_append hprefix tailTrace_2627281
  have hstable : (prefixWord ++ tailWord_2627281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627281).length < 2 ^ (prefixWord ++ tailWord_2627281).sum := by decide
  have hdescent : baseEnd_2627281 < baseStart_2627281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627311 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 5, 3]
def baseStart_2627311 : Nat := 118140960795 + 2627311 * 2 ^ 59
def prefixEnd_2627311 : Nat := 4983230072969 + 3 ^ 40 * 2627311 * 2
def baseEnd_2627311 : Nat := 899382247896583578219815

theorem tailTrace_2627311 : CollatzResearch.WordTrace tailWord_2627311 prefixEnd_2627311 899382247896583578219815 := by
  unfold tailWord_2627311
  simp only [CollatzResearch.WordTrace]
  refine ⟨95825904584708430840361787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63883936389805620560241191 95825904584708430840361787)
  ·
    refine ⟨143738856877062646260542681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95825904584708430840361787 143738856877062646260542681)
    ·
      refine ⟨107804142657796984695407011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143738856877062646260542681 107804142657796984695407011)
      ·
        refine ⟨161706213986695477043110517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107804142657796984695407011 161706213986695477043110517)
        ·
          refine ⟨15159957561252700972791611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161706213986695477043110517 15159957561252700972791611)
          ·
            refine ⟨22739936341879051459187417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15159957561252700972791611 22739936341879051459187417)
            ·
              refine ⟨17054952256409288594390563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22739936341879051459187417 17054952256409288594390563)
              ·
                refine ⟨25582428384613932891585845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054952256409288594390563 25582428384613932891585845)
                ·
                  refine ⟨2398352661057556208586173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25582428384613932891585845 2398352661057556208586173)
                  ·
                    refine ⟨899382247896583578219815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398352661057556208586173 899382247896583578219815)
                    ·
                      rfl

theorem cell22_2627311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_2627311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627311 prefixEnd_2627311 := by exact prefixLift 2627311
  have htrace : WordTrace (prefixWord ++ tailWord_2627311) baseStart_2627311 baseEnd_2627311 := by
    simpa [prefixWord, tailWord_2627311, baseEnd_2627311] using wordTrace_append hprefix tailTrace_2627311
  have hstable : (prefixWord ++ tailWord_2627311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627311).length < 2 ^ (prefixWord ++ tailWord_2627311).sum := by decide
  have hdescent : baseEnd_2627311 < baseStart_2627311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627356 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2627356 : Nat := 118140960795 + 2627356 * 2 ^ 59
def prefixEnd_2627356 : Nat := 4983230072969 + 3 ^ 40 * 2627356 * 2
def baseEnd_2627356 : Nat := 899397652316218460844677

theorem tailTrace_2627356 : CollatzResearch.WordTrace tailWord_2627356 prefixEnd_2627356 899397652316218460844677 := by
  unfold tailWord_2627356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47913772934772701762874961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63885030579696935683833281 47913772934772701762874961)
  ·
    refine ⟨35935329701079526322156221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47913772934772701762874961 35935329701079526322156221)
    ·
      refine ⟨13475748637904822370808583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35935329701079526322156221 13475748637904822370808583)
      ·
        refine ⟨20213622956857233556212875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13475748637904822370808583 20213622956857233556212875)
        ·
          refine ⟨30320434435285850334319313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20213622956857233556212875 30320434435285850334319313)
          ·
            refine ⟨22740325826464387750739485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30320434435285850334319313 22740325826464387750739485)
            ·
              refine ⟨8527622184924145406527307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22740325826464387750739485 8527622184924145406527307)
              ·
                refine ⟨12791433277386218109790961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8527622184924145406527307 12791433277386218109790961)
                ·
                  refine ⟨9593574958039663582343221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12791433277386218109790961 9593574958039663582343221)
                  ·
                    refine ⟨899397652316218460844677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9593574958039663582343221 899397652316218460844677)
                    ·
                      rfl

theorem cell22_2627356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2627356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627356 prefixEnd_2627356 := by exact prefixLift 2627356
  have htrace : WordTrace (prefixWord ++ tailWord_2627356) baseStart_2627356 baseEnd_2627356 := by
    simpa [prefixWord, tailWord_2627356, baseEnd_2627356] using wordTrace_append hprefix tailTrace_2627356
  have hstable : (prefixWord ++ tailWord_2627356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627356).length < 2 ^ (prefixWord ++ tailWord_2627356).sum := by decide
  have hdescent : baseEnd_2627356 < baseStart_2627356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627431 : List Nat := [1, 1, 5, 1, 2, 1, 3, 8]
def baseStart_2627431 : Nat := 118140960795 + 2627431 * 2 ^ 59
def prefixEnd_2627431 : Nat := 4983230072969 + 3 ^ 40 * 2627431 * 2
def baseEnd_2627431 : Nat := 99935925149882585024383

theorem tailTrace_2627431 : CollatzResearch.WordTrace tailWord_2627431 prefixEnd_2627431 99935925149882585024383 := by
  unfold tailWord_2627431
  simp only [CollatzResearch.WordTrace]
  refine ⟨95830281344273691334730147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63886854229515794223153431 95830281344273691334730147)
  ·
    refine ⟨143745422016410537002095221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95830281344273691334730147 143745422016410537002095221)
    ·
      refine ⟨13476133314038487843946427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143745422016410537002095221 13476133314038487843946427)
      ·
        refine ⟨20214199971057731765919641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13476133314038487843946427 20214199971057731765919641)
        ·
          refine ⟨15160649978293298824439731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20214199971057731765919641 15160649978293298824439731)
          ·
            refine ⟨22740974967439948236659597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15160649978293298824439731 22740974967439948236659597)
            ·
              refine ⟨8527865612789980588747349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22740974967439948236659597 8527865612789980588747349)
              ·
                refine ⟨99935925149882585024383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8527865612789980588747349 99935925149882585024383)
                ·
                  rfl

theorem cell22_2627431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 8].length) (baseStart_2627431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627431 prefixEnd_2627431 := by exact prefixLift 2627431
  have htrace : WordTrace (prefixWord ++ tailWord_2627431) baseStart_2627431 baseEnd_2627431 := by
    simpa [prefixWord, tailWord_2627431, baseEnd_2627431] using wordTrace_append hprefix tailTrace_2627431
  have hstable : (prefixWord ++ tailWord_2627431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627431).length < 2 ^ (prefixWord ++ tailWord_2627431).sum := by decide
  have hdescent : baseEnd_2627431 < baseStart_2627431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627454 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_2627454 : Nat := 118140960795 + 2627454 * 2 ^ 59
def prefixEnd_2627454 : Nat := 4983230072969 + 3 ^ 40 * 2627454 * 2
def baseEnd_2627454 : Nat := 299810399906326290631459

theorem tailTrace_2627454 : CollatzResearch.WordTrace tailWord_2627454 prefixEnd_2627454 299810399906326290631459 := by
  unfold tailWord_2627454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11978890027898795782852177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63887413482126910841878277 11978890027898795782852177)
  ·
    refine ⟨8984167520924096837139133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11978890027898795782852177 8984167520924096837139133)
    ·
      refine ⟨3369062820346536313927175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8984167520924096837139133 3369062820346536313927175)
      ·
        refine ⟨5053594230519804470890763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369062820346536313927175 5053594230519804470890763)
        ·
          refine ⟨7580391345779706706336145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053594230519804470890763 7580391345779706706336145)
          ·
            refine ⟨5685293509334780029752109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7580391345779706706336145 5685293509334780029752109)
            ·
              refine ⟨2131985066000542511157041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5685293509334780029752109 2131985066000542511157041)
              ·
                refine ⟨1598988799500406883367781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131985066000542511157041 1598988799500406883367781)
                ·
                  refine ⟨299810399906326290631459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598988799500406883367781 299810399906326290631459)
                  ·
                    rfl

theorem cell22_2627454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_2627454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627454 prefixEnd_2627454 := by exact prefixLift 2627454
  have htrace : WordTrace (prefixWord ++ tailWord_2627454) baseStart_2627454 baseEnd_2627454 := by
    simpa [prefixWord, tailWord_2627454, baseEnd_2627454] using wordTrace_append hprefix tailTrace_2627454
  have hstable : (prefixWord ++ tailWord_2627454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627454).length < 2 ^ (prefixWord ++ tailWord_2627454).sum := by decide
  have hdescent : baseEnd_2627454 < baseStart_2627454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627461 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2627461 : Nat := 118140960795 + 2627461 * 2 ^ 59
def prefixEnd_2627461 : Nat := 4983230072969 + 3 ^ 40 * 2627461 * 2
def baseEnd_2627461 : Nat := 899433595962033186969355

theorem tailTrace_2627461 : CollatzResearch.WordTrace tailWord_2627461 prefixEnd_2627461 899433595962033186969355 := by
  unfold tailWord_2627461
  simp only [CollatzResearch.WordTrace]
  refine ⟨95831375534165006458322237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63887583689443337638881491 95831375534165006458322237)
  ·
    refine ⟨35936765825311877421870839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95831375534165006458322237 35936765825311877421870839)
    ·
      refine ⟨53905148737967816132806259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35936765825311877421870839 53905148737967816132806259)
      ·
        refine ⟨80857723106951724199209389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53905148737967816132806259 80857723106951724199209389)
        ·
          refine ⟨30321646165106896574703521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80857723106951724199209389 30321646165106896574703521)
          ·
            refine ⟨22741234623830172431027641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30321646165106896574703521 22741234623830172431027641)
            ·
              refine ⟨17055925967872629323270731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22741234623830172431027641 17055925967872629323270731)
              ·
                refine ⟨25583888951808943984906097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17055925967872629323270731 25583888951808943984906097)
                ·
                  refine ⟨19187916713856707988679573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25583888951808943984906097 19187916713856707988679573)
                  ·
                    refine ⟨899433595962033186969355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19187916713856707988679573 899433595962033186969355)
                    ·
                      rfl

theorem cell22_2627461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2627461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627461 prefixEnd_2627461 := by exact prefixLift 2627461
  have htrace : WordTrace (prefixWord ++ tailWord_2627461) baseStart_2627461 baseEnd_2627461 := by
    simpa [prefixWord, tailWord_2627461, baseEnd_2627461] using wordTrace_append hprefix tailTrace_2627461
  have hstable : (prefixWord ++ tailWord_2627461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627461).length < 2 ^ (prefixWord ++ tailWord_2627461).sum := by decide
  have hdescent : baseEnd_2627461 < baseStart_2627461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627491 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_2627491 : Nat := 118140960795 + 2627491 * 2 ^ 59
def prefixEnd_2627491 : Nat := 4983230072969 + 3 ^ 40 * 2627491 * 2
def baseEnd_2627491 : Nat := 899443865575123108719263

theorem tailTrace_2627491 : CollatzResearch.WordTrace tailWord_2627491 prefixEnd_2627491 899443865575123108719263 := by
  unfold tailWord_2627491
  simp only [CollatzResearch.WordTrace]
  refine ⟨95832469724056321581914327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63888313149370881054609551 95832469724056321581914327)
  ·
    refine ⟨143748704586084482372871491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95832469724056321581914327 143748704586084482372871491)
    ·
      refine ⟨215623056879126723559307237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143748704586084482372871491 215623056879126723559307237)
      ·
        refine ⟨40429323164836260667370107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215623056879126723559307237 40429323164836260667370107)
        ·
          refine ⟨60643984747254391001055161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40429323164836260667370107 60643984747254391001055161)
          ·
            refine ⟨45482988560440793250791371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60643984747254391001055161 45482988560440793250791371)
            ·
              refine ⟨68224482840661189876187057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45482988560440793250791371 68224482840661189876187057)
              ·
                refine ⟨51168362130495892407140293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68224482840661189876187057 51168362130495892407140293)
                ·
                  refine ⟨9594067899467979826338805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51168362130495892407140293 9594067899467979826338805)
                  ·
                    refine ⟨899443865575123108719263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9594067899467979826338805 899443865575123108719263)
                    ·
                      rfl

theorem cell22_2627491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_2627491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627491 prefixEnd_2627491 := by exact prefixLift 2627491
  have htrace : WordTrace (prefixWord ++ tailWord_2627491) baseStart_2627491 baseEnd_2627491 := by
    simpa [prefixWord, tailWord_2627491, baseEnd_2627491] using wordTrace_append hprefix tailTrace_2627491
  have hstable : (prefixWord ++ tailWord_2627491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627491).length < 2 ^ (prefixWord ++ tailWord_2627491).sum := by decide
  have hdescent : baseEnd_2627491 < baseStart_2627491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627540 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2627540 : Nat := 118140960795 + 2627540 * 2 ^ 59
def prefixEnd_2627540 : Nat := 4983230072969 + 3 ^ 40 * 2627540 * 2
def baseEnd_2627540 : Nat := 899460639276503314244113

theorem tailTrace_2627540 : CollatzResearch.WordTrace tailWord_2627540 prefixEnd_2627540 899460639276503314244113 := by
  unfold tailWord_2627540
  simp only [CollatzResearch.WordTrace]
  refine ⟨47917128450439401475224037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63889504600585868633632049 47917128450439401475224037)
  ·
    refine ⟨8984461584457387776604507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47917128450439401475224037 8984461584457387776604507)
    ·
      refine ⟨13476692376686081664906761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8984461584457387776604507 13476692376686081664906761)
      ·
        refine ⟨10107519282514561248680071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13476692376686081664906761 10107519282514561248680071)
        ·
          refine ⟨15161278923771841873020107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107519282514561248680071 15161278923771841873020107)
          ·
            refine ⟨22741918385657762809530161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15161278923771841873020107 22741918385657762809530161)
            ·
              refine ⟨17056438789243322107147621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22741918385657762809530161 17056438789243322107147621)
              ·
                refine ⟨3198082272983122895090179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17056438789243322107147621 3198082272983122895090179)
                ·
                  refine ⟨4797123409474684342635269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198082272983122895090179 4797123409474684342635269)
                  ·
                    refine ⟨899460639276503314244113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797123409474684342635269 899460639276503314244113)
                    ·
                      rfl

theorem cell22_2627540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2627540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627540 prefixEnd_2627540 := by exact prefixLift 2627540
  have htrace : WordTrace (prefixWord ++ tailWord_2627540) baseStart_2627540 baseEnd_2627540 := by
    simpa [prefixWord, tailWord_2627540, baseEnd_2627540] using wordTrace_append hprefix tailTrace_2627540
  have hstable : (prefixWord ++ tailWord_2627540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627540).length < 2 ^ (prefixWord ++ tailWord_2627540).sum := by decide
  have hdescent : baseEnd_2627540 < baseStart_2627540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627548 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2627548 : Nat := 118140960795 + 2627548 * 2 ^ 59
def prefixEnd_2627548 : Nat := 4983230072969 + 3 ^ 40 * 2627548 * 2
def baseEnd_2627548 : Nat := 899463377839993960044089

theorem tailTrace_2627548 : CollatzResearch.WordTrace tailWord_2627548 prefixEnd_2627548 899463377839993960044089 := by
  unfold tailWord_2627548
  simp only [CollatzResearch.WordTrace]
  refine ⟨47917274342424910158369649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63889699123233213544492865 47917274342424910158369649)
  ·
    refine ⟨35937955756818682618777237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47917274342424910158369649 35937955756818682618777237)
    ·
      refine ⟨1684591676100875747755183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35937955756818682618777237 1684591676100875747755183)
      ·
        refine ⟨2526887514151313621632775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684591676100875747755183 2526887514151313621632775)
        ·
          refine ⟨3790331271226970432449163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526887514151313621632775 3790331271226970432449163)
          ·
            refine ⟨5685496906840455648673745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790331271226970432449163 5685496906840455648673745)
            ·
              refine ⟨4264122680130341736505309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5685496906840455648673745 4264122680130341736505309)
              ·
                refine ⟨1599046005048878151189491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4264122680130341736505309 1599046005048878151189491)
                ·
                  refine ⟨2398569007573317226784237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599046005048878151189491 2398569007573317226784237)
                  ·
                    refine ⟨899463377839993960044089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398569007573317226784237 899463377839993960044089)
                    ·
                      rfl

theorem cell22_2627548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2627548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627548 prefixEnd_2627548 := by exact prefixLift 2627548
  have htrace : WordTrace (prefixWord ++ tailWord_2627548) baseStart_2627548 baseEnd_2627548 := by
    simpa [prefixWord, tailWord_2627548, baseEnd_2627548] using wordTrace_append hprefix tailTrace_2627548
  have hstable : (prefixWord ++ tailWord_2627548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627548).length < 2 ^ (prefixWord ++ tailWord_2627548).sum := by decide
  have hdescent : baseEnd_2627548 < baseStart_2627548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627553 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2627553 : Nat := 118140960795 + 2627553 * 2 ^ 59
def prefixEnd_2627553 : Nat := 4983230072969 + 3 ^ 40 * 2627553 * 2
def baseEnd_2627553 : Nat := 899465089442175613669073

theorem tailTrace_2627553 : CollatzResearch.WordTrace tailWord_2627553 prefixEnd_2627553 899465089442175613669073 := by
  unfold tailWord_2627553
  simp only [CollatzResearch.WordTrace]
  refine ⟨95834731049831706170671313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63889820699887804113780875 95834731049831706170671313)
  ·
    refine ⟨71876048287373779628003485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95834731049831706170671313 71876048287373779628003485)
    ·
      refine ⟨26953518107765167360501307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71876048287373779628003485 26953518107765167360501307)
      ·
        refine ⟨40430277161647751040751961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26953518107765167360501307 40430277161647751040751961)
        ·
          refine ⟨30322707871235813280563971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40430277161647751040751961 30322707871235813280563971)
          ·
            refine ⟨45484061806853719920845957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30322707871235813280563971 45484061806853719920845957)
            ·
              refine ⟨8528261588785072485158617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45484061806853719920845957 8528261588785072485158617)
              ·
                refine ⟨6396196191588804363868963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8528261588785072485158617 6396196191588804363868963)
                ·
                  refine ⟨9594294287383206545803445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396196191588804363868963 9594294287383206545803445)
                  ·
                    refine ⟨899465089442175613669073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9594294287383206545803445 899465089442175613669073)
                    ·
                      rfl

theorem cell22_2627553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2627553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627553 prefixEnd_2627553 := by exact prefixLift 2627553
  have htrace : WordTrace (prefixWord ++ tailWord_2627553) baseStart_2627553 baseEnd_2627553 := by
    simpa [prefixWord, tailWord_2627553, baseEnd_2627553] using wordTrace_append hprefix tailTrace_2627553
  have hstable : (prefixWord ++ tailWord_2627553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627553).length < 2 ^ (prefixWord ++ tailWord_2627553).sum := by decide
  have hdescent : baseEnd_2627553 < baseStart_2627553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627555 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 4]
def baseStart_2627555 : Nat := 118140960795 + 2627555 * 2 ^ 59
def prefixEnd_2627555 : Nat := 4983230072969 + 3 ^ 40 * 2627555 * 2
def baseEnd_2627555 : Nat := 299821924694349425039689

theorem tailTrace_2627555 : CollatzResearch.WordTrace tailWord_2627555 prefixEnd_2627555 299821924694349425039689 := by
  unfold tailWord_2627555
  simp only [CollatzResearch.WordTrace]
  refine ⟨95834803995824460512244119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63889869330549640341496079 95834803995824460512244119)
  ·
    refine ⟨143752205993736690768366179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95834803995824460512244119 143752205993736690768366179)
    ·
      refine ⟨215628308990605036152549269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143752205993736690768366179 215628308990605036152549269)
      ·
        refine ⟨10107576983934611069650747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215628308990605036152549269 10107576983934611069650747)
        ·
          refine ⟨15161365475901916604476121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107576983934611069650747 15161365475901916604476121)
          ·
            refine ⟨11371024106926437453357091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15161365475901916604476121 11371024106926437453357091)
            ·
              refine ⟨17056536160389656180035637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11371024106926437453357091 17056536160389656180035637)
              ·
                refine ⟨1599050265036530266878341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17056536160389656180035637 1599050265036530266878341)
                ·
                  refine ⟨299821924694349425039689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599050265036530266878341 299821924694349425039689)
                  ·
                    rfl

theorem cell22_2627555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 4].length) (baseStart_2627555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627555 prefixEnd_2627555 := by exact prefixLift 2627555
  have htrace : WordTrace (prefixWord ++ tailWord_2627555) baseStart_2627555 baseEnd_2627555 := by
    simpa [prefixWord, tailWord_2627555, baseEnd_2627555] using wordTrace_append hprefix tailTrace_2627555
  have hstable : (prefixWord ++ tailWord_2627555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627555).length < 2 ^ (prefixWord ++ tailWord_2627555).sum := by decide
  have hdescent : baseEnd_2627555 < baseStart_2627555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627568 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_2627568 : Nat := 118140960795 + 2627568 * 2 ^ 59
def prefixEnd_2627568 : Nat := 4983230072969 + 3 ^ 40 * 2627568 * 2
def baseEnd_2627568 : Nat := 899470224248720574544027

theorem tailTrace_2627568 : CollatzResearch.WordTrace tailWord_2627568 prefixEnd_2627568 899470224248720574544027 := by
  unfold tailWord_2627568
  simp only [CollatzResearch.WordTrace]
  refine ⟨47917639072388681866233679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63890185429851575821644905 47917639072388681866233679)
  ·
    refine ⟨71876458608583022799350519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47917639072388681866233679 71876458608583022799350519)
    ·
      refine ⟨107814687912874534199025779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71876458608583022799350519 107814687912874534199025779)
      ·
        refine ⟨161722031869311801298538669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107814687912874534199025779 161722031869311801298538669)
        ·
          refine ⟨60645761950991925486952001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161722031869311801298538669 60645761950991925486952001)
          ·
            refine ⟨45484321463243944115214001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60645761950991925486952001 45484321463243944115214001)
            ·
              refine ⟨34113241097432958086410501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45484321463243944115214001 34113241097432958086410501)
              ·
                refine ⟨6396232705768679641201969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34113241097432958086410501 6396232705768679641201969)
                ·
                  refine ⟨4797174529326509730901477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6396232705768679641201969 4797174529326509730901477)
                  ·
                    refine ⟨899470224248720574544027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797174529326509730901477 899470224248720574544027)
                    ·
                      rfl

theorem cell22_2627568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_2627568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627568 prefixEnd_2627568 := by exact prefixLift 2627568
  have htrace : WordTrace (prefixWord ++ tailWord_2627568) baseStart_2627568 baseEnd_2627568 := by
    simpa [prefixWord, tailWord_2627568, baseEnd_2627568] using wordTrace_append hprefix tailTrace_2627568
  have hstable : (prefixWord ++ tailWord_2627568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627568).length < 2 ^ (prefixWord ++ tailWord_2627568).sum := by decide
  have hdescent : baseEnd_2627568 < baseStart_2627568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627598 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2627598 : Nat := 118140960795 + 2627598 * 2 ^ 59
def prefixEnd_2627598 : Nat := 4983230072969 + 3 ^ 40 * 2627598 * 2
def baseEnd_2627598 : Nat := 899480493861810496293935

theorem tailTrace_2627598 : CollatzResearch.WordTrace tailWord_2627598 prefixEnd_2627598 899480493861810496293935 := by
  unfold tailWord_2627598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979546541833584857007431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63890914889779119237372965 11979546541833584857007431)
  ·
    refine ⟨17969319812750377285511147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11979546541833584857007431 17969319812750377285511147)
    ·
      refine ⟨26953979719125565928266721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17969319812750377285511147 26953979719125565928266721)
      ·
        refine ⟨20215484789344174446200041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26953979719125565928266721 20215484789344174446200041)
        ·
          refine ⟨15161613592008130834650031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20215484789344174446200041 15161613592008130834650031)
          ·
            refine ⟨22742420388012196251975047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15161613592008130834650031 22742420388012196251975047)
            ·
              refine ⟨34113630582018294377962571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22742420388012196251975047 34113630582018294377962571)
              ·
                refine ⟨51170445873027441566943857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34113630582018294377962571 51170445873027441566943857)
                ·
                  refine ⟨38377834404770581175207893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51170445873027441566943857 38377834404770581175207893)
                  ·
                    refine ⟨899480493861810496293935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38377834404770581175207893 899480493861810496293935)
                    ·
                      rfl

theorem cell22_2627598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2627598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627598 prefixEnd_2627598 := by exact prefixLift 2627598
  have htrace : WordTrace (prefixWord ++ tailWord_2627598) baseStart_2627598 baseEnd_2627598 := by
    simpa [prefixWord, tailWord_2627598, baseEnd_2627598] using wordTrace_append hprefix tailTrace_2627598
  have hstable : (prefixWord ++ tailWord_2627598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627598).length < 2 ^ (prefixWord ++ tailWord_2627598).sum := by decide
  have hdescent : baseEnd_2627598 < baseStart_2627598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627632 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_2627632 : Nat := 118140960795 + 2627632 * 2 ^ 59
def prefixEnd_2627632 : Nat := 4983230072969 + 3 ^ 40 * 2627632 * 2
def baseEnd_2627632 : Nat := 899492132756645740943831

theorem tailTrace_2627632 : CollatzResearch.WordTrace tailWord_2627632 prefixEnd_2627632 899492132756645740943831 := by
  unfold tailWord_2627632
  simp only [CollatzResearch.WordTrace]
  refine ⟨47918806208272751331398575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63891741611030335108531433 47918806208272751331398575)
  ·
    refine ⟨71878209312409126997097863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47918806208272751331398575 71878209312409126997097863)
    ·
      refine ⟨107817313968613690495646795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71878209312409126997097863 107817313968613690495646795)
      ·
        refine ⟨161725970952920535743470193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107817313968613690495646795 161725970952920535743470193)
        ·
          refine ⟨121294478214690401807602645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161725970952920535743470193 121294478214690401807602645)
          ·
            refine ⟨2842839333156806292365687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 121294478214690401807602645 2842839333156806292365687)
            ·
              refine ⟨4264258999735209438548531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842839333156806292365687 4264258999735209438548531)
              ·
                refine ⟨6396388499602814157822797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264258999735209438548531 6396388499602814157822797)
                ·
                  refine ⟨2398645687351055309183549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6396388499602814157822797 2398645687351055309183549)
                  ·
                    refine ⟨899492132756645740943831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398645687351055309183549 899492132756645740943831)
                    ·
                      rfl

theorem cell22_2627632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_2627632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627632 prefixEnd_2627632 := by exact prefixLift 2627632
  have htrace : WordTrace (prefixWord ++ tailWord_2627632) baseStart_2627632 baseEnd_2627632 := by
    simpa [prefixWord, tailWord_2627632, baseEnd_2627632] using wordTrace_append hprefix tailTrace_2627632
  have hstable : (prefixWord ++ tailWord_2627632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627632).length < 2 ^ (prefixWord ++ tailWord_2627632).sum := by decide
  have hdescent : baseEnd_2627632 < baseStart_2627632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627645 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2627645 : Nat := 118140960795 + 2627645 * 2 ^ 59
def prefixEnd_2627645 : Nat := 4983230072969 + 3 ^ 40 * 2627645 * 2
def baseEnd_2627645 : Nat := 299832194307439346789597

theorem tailTrace_2627645 : CollatzResearch.WordTrace tailWord_2627645 prefixEnd_2627645 299832194307439346789597 := by
  unfold tailWord_2627645
  simp only [CollatzResearch.WordTrace]
  refine ⟨95838086565498405883020389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63892057710332270588680259 95838086565498405883020389)
  ·
    refine ⟨17969641231030951103066323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95838086565498405883020389 17969641231030951103066323)
    ·
      refine ⟨26954461846546426654599485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17969641231030951103066323 26954461846546426654599485)
      ·
        refine ⟨10107923192454909995474807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26954461846546426654599485 10107923192454909995474807)
        ·
          refine ⟨15161884788682364993212211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107923192454909995474807 15161884788682364993212211)
          ·
            refine ⟨22742827183023547489818317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15161884788682364993212211 22742827183023547489818317)
            ·
              refine ⟨8528560193633830308681869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22742827183023547489818317 8528560193633830308681869)
              ·
                refine ⟨3198210072612686365755701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8528560193633830308681869 3198210072612686365755701)
                ·
                  refine ⟨299832194307439346789597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3198210072612686365755701 299832194307439346789597)
                  ·
                    rfl

theorem cell22_2627645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2627645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627645 prefixEnd_2627645 := by exact prefixLift 2627645
  have htrace : WordTrace (prefixWord ++ tailWord_2627645) baseStart_2627645 baseEnd_2627645 := by
    simpa [prefixWord, tailWord_2627645, baseEnd_2627645] using wordTrace_append hprefix tailTrace_2627645
  have hstable : (prefixWord ++ tailWord_2627645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627645).length < 2 ^ (prefixWord ++ tailWord_2627645).sum := by decide
  have hdescent : baseEnd_2627645 < baseStart_2627645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627705 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_2627705 : Nat := 118140960795 + 2627705 * 2 ^ 59
def prefixEnd_2627705 : Nat := 4983230072969 + 3 ^ 40 * 2627705 * 2
def baseEnd_2627705 : Nat := 899517122148497883868607

theorem tailTrace_2627705 : CollatzResearch.WordTrace tailWord_2627705 prefixEnd_2627705 899517122148497883868607 := by
  unfold tailWord_2627705
  simp only [CollatzResearch.WordTrace]
  refine ⟨95840274945281036130204569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63893516630187357420136379 95840274945281036130204569)
  ·
    refine ⟨71880206208960777097653427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95840274945281036130204569 71880206208960777097653427)
    ·
      refine ⟨107820309313441165646480141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71880206208960777097653427 107820309313441165646480141)
      ·
        refine ⟨40432615992540437117430053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107820309313441165646480141 40432615992540437117430053)
        ·
          refine ⟨7581115498601331959518135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40432615992540437117430053 7581115498601331959518135)
          ·
            refine ⟨11371673247901997939277203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581115498601331959518135 11371673247901997939277203)
            ·
              refine ⟨17057509871852996908915805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11371673247901997939277203 17057509871852996908915805)
              ·
                refine ⟨6396566201944873840843427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17057509871852996908915805 6396566201944873840843427)
                ·
                  refine ⟨9594849302917310761265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396566201944873840843427 9594849302917310761265141)
                  ·
                    refine ⟨899517122148497883868607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9594849302917310761265141 899517122148497883868607)
                    ·
                      rfl

theorem cell22_2627705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_2627705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627705 prefixEnd_2627705 := by exact prefixLift 2627705
  have htrace : WordTrace (prefixWord ++ tailWord_2627705) baseStart_2627705 baseEnd_2627705 := by
    simpa [prefixWord, tailWord_2627705, baseEnd_2627705] using wordTrace_append hprefix tailTrace_2627705
  have hstable : (prefixWord ++ tailWord_2627705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627705).length < 2 ^ (prefixWord ++ tailWord_2627705).sum := by decide
  have hdescent : baseEnd_2627705 < baseStart_2627705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627726 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_2627726 : Nat := 118140960795 + 2627726 * 2 ^ 59
def prefixEnd_2627726 : Nat := 4983230072969 + 3 ^ 40 * 2627726 * 2
def baseEnd_2627726 : Nat := 899524310877660829093543

theorem tailTrace_2627726 : CollatzResearch.WordTrace tailWord_2627726 prefixEnd_2627726 899524310877660829093543 := by
  unfold tailWord_2627726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980130109775619589589879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63894027252136637811146021 11980130109775619589589879)
  ·
    refine ⟨17970195164663429384384819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11980130109775619589589879 17970195164663429384384819)
    ·
      refine ⟨26955292746995144076577229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17970195164663429384384819 26955292746995144076577229)
      ·
        refine ⟨10108234780123179028716461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26955292746995144076577229 10108234780123179028716461)
        ·
          refine ⟨3790588042546192135768673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10108234780123179028716461 3790588042546192135768673)
          ·
            refine ⟨2842941031909644101826505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790588042546192135768673 2842941031909644101826505)
            ·
              refine ⟨2132205773932233076369879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842941031909644101826505 2132205773932233076369879)
              ·
                refine ⟨3198308660898349614554819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132205773932233076369879 3198308660898349614554819)
                ·
                  refine ⟨4797462991347524421832229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198308660898349614554819 4797462991347524421832229)
                  ·
                    refine ⟨899524310877660829093543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4797462991347524421832229 899524310877660829093543)
                    ·
                      rfl

theorem cell22_2627726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_2627726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627726 prefixEnd_2627726 := by exact prefixLift 2627726
  have htrace : WordTrace (prefixWord ++ tailWord_2627726) baseStart_2627726 baseEnd_2627726 := by
    simpa [prefixWord, tailWord_2627726, baseEnd_2627726] using wordTrace_append hprefix tailTrace_2627726
  have hstable : (prefixWord ++ tailWord_2627726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627726).length < 2 ^ (prefixWord ++ tailWord_2627726).sum := by decide
  have hdescent : baseEnd_2627726 < baseStart_2627726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627735 : List Nat := [1, 1, 3, 3, 4, 1, 9]
def baseStart_2627735 : Nat := 118140960795 + 2627735 * 2 ^ 59
def prefixEnd_2627735 : Nat := 4983230072969 + 3 ^ 40 * 2627735 * 2
def baseEnd_2627735 : Nat := 33315829324503252059945

theorem tailTrace_2627735 : CollatzResearch.WordTrace tailWord_2627735 prefixEnd_2627735 33315829324503252059945 := by
  unfold tailWord_2627735
  simp only [CollatzResearch.WordTrace]
  refine ⟨95841369135172351253796659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63894246090114900835864439 95841369135172351253796659)
  ·
    refine ⟨143762053702758526880694989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95841369135172351253796659 143762053702758526880694989)
    ·
      refine ⟨53910770138534447580260621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143762053702758526880694989 53910770138534447580260621)
      ·
        refine ⟨20216538801950417842597733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53910770138534447580260621 20216538801950417842597733)
        ·
          refine ⟨3790601025365703345487075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20216538801950417842597733 3790601025365703345487075)
          ·
            refine ⟨5685901538048555018230613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790601025365703345487075 5685901538048555018230613)
            ·
              refine ⟨33315829324503252059945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5685901538048555018230613 33315829324503252059945)
              ·
                rfl

theorem cell22_2627735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 9].length) (baseStart_2627735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627735 prefixEnd_2627735 := by exact prefixLift 2627735
  have htrace : WordTrace (prefixWord ++ tailWord_2627735) baseStart_2627735 baseEnd_2627735 := by
    simpa [prefixWord, tailWord_2627735, baseEnd_2627735] using wordTrace_append hprefix tailTrace_2627735
  have hstable : (prefixWord ++ tailWord_2627735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627735).length < 2 ^ (prefixWord ++ tailWord_2627735).sum := by decide
  have hdescent : baseEnd_2627735 < baseStart_2627735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627767 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 3, 3]
def baseStart_2627767 : Nat := 118140960795 + 2627767 * 2 ^ 59
def prefixEnd_2627767 : Nat := 4983230072969 + 3 ^ 40 * 2627767 * 2
def baseEnd_2627767 : Nat := 899538346015550388818417

theorem tailTrace_2627767 : CollatzResearch.WordTrace tailWord_2627767 prefixEnd_2627767 899538346015550388818417 := by
  unfold tailWord_2627767
  simp only [CollatzResearch.WordTrace]
  refine ⟨95842536271056420718961555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63895024180704280479307703 95842536271056420718961555)
  ·
    refine ⟨143763804406584631078442333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95842536271056420718961555 143763804406584631078442333)
    ·
      refine ⟨53911426652469236654415875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143763804406584631078442333 53911426652469236654415875)
      ·
        refine ⟨80867139978703854981623813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53911426652469236654415875 80867139978703854981623813)
        ·
          refine ⟨15162588746006972809054465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80867139978703854981623813 15162588746006972809054465)
          ·
            refine ⟨11371941559505229606790849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15162588746006972809054465 11371941559505229606790849)
            ·
              refine ⟨8528956169628922205093137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11371941559505229606790849 8528956169628922205093137)
              ·
                refine ⟨6396717127221691653819853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8528956169628922205093137 6396717127221691653819853)
                ·
                  refine ⟨2398768922708134370182445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6396717127221691653819853 2398768922708134370182445)
                  ·
                    refine ⟨899538346015550388818417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398768922708134370182445 899538346015550388818417)
                    ·
                      rfl

theorem cell22_2627767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_2627767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627767 prefixEnd_2627767 := by exact prefixLift 2627767
  have htrace : WordTrace (prefixWord ++ tailWord_2627767) baseStart_2627767 baseEnd_2627767 := by
    simpa [prefixWord, tailWord_2627767, baseEnd_2627767] using wordTrace_append hprefix tailTrace_2627767
  have hstable : (prefixWord ++ tailWord_2627767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627767).length < 2 ^ (prefixWord ++ tailWord_2627767).sum := by decide
  have hdescent : baseEnd_2627767 < baseStart_2627767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627825 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 6]
def baseStart_2627825 : Nat := 118140960795 + 2627825 * 2 ^ 59
def prefixEnd_2627825 : Nat := 4983230072969 + 3 ^ 40 * 2627825 * 2
def baseEnd_2627825 : Nat := 299852733533619190289413

theorem tailTrace_2627825 : CollatzResearch.WordTrace tailWord_2627825 prefixEnd_2627825 299852733533619190289413 := by
  unfold tailWord_2627825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95844651704846296624572929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63896434469897531083048619 95844651704846296624572929)
  ·
    refine ⟨71883488778634722468429697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95844651704846296624572929 71883488778634722468429697)
    ·
      refine ⟨53912616583976041851322273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71883488778634722468429697 53912616583976041851322273)
      ·
        refine ⟨40434462437982031388491705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53912616583976041851322273 40434462437982031388491705)
        ·
          refine ⟨30325846828486523541368779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40434462437982031388491705 30325846828486523541368779)
          ·
            refine ⟨45488770242729785312053169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30325846828486523541368779 45488770242729785312053169)
            ·
              refine ⟨34116577682047338984039877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45488770242729785312053169 34116577682047338984039877)
              ·
                refine ⟨6396858315383876059507477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34116577682047338984039877 6396858315383876059507477)
                ·
                  refine ⟨299852733533619190289413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6396858315383876059507477 299852733533619190289413)
                  ·
                    rfl

theorem cell22_2627825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_2627825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627825 prefixEnd_2627825 := by exact prefixLift 2627825
  have htrace : WordTrace (prefixWord ++ tailWord_2627825) baseStart_2627825 baseEnd_2627825 := by
    simpa [prefixWord, tailWord_2627825, baseEnd_2627825] using wordTrace_append hprefix tailTrace_2627825
  have hstable : (prefixWord ++ tailWord_2627825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627825).length < 2 ^ (prefixWord ++ tailWord_2627825).sum := by decide
  have hdescent : baseEnd_2627825 < baseStart_2627825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627840 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_2627840 : Nat := 118140960795 + 2627840 * 2 ^ 59
def prefixEnd_2627840 : Nat := 4983230072969 + 3 ^ 40 * 2627840 * 2
def baseEnd_2627840 : Nat := 899563335407402531743193

theorem tailTrace_2627840 : CollatzResearch.WordTrace tailWord_2627840 prefixEnd_2627840 899563335407402531743193 := by
  unfold tailWord_2627840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47922599399895977093184487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63896799199861302790912649 47922599399895977093184487)
  ·
    refine ⟨71883899099843965639776731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47922599399895977093184487 71883899099843965639776731)
    ·
      refine ⟨107825848649765948459665097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71883899099843965639776731 107825848649765948459665097)
      ·
        refine ⟨80869386487324461344748823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107825848649765948459665097 80869386487324461344748823)
        ·
          refine ⟨121304079730986692017123235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80869386487324461344748823 121304079730986692017123235)
          ·
            refine ⟨181956119596480038025684853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121304079730986692017123235 181956119596480038025684853)
            ·
              refine ⟨17058386212170003564907955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181956119596480038025684853 17058386212170003564907955)
              ·
                refine ⟨25587579318255005347361933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17058386212170003564907955 25587579318255005347361933)
                ·
                  refine ⟨9595342244345627005260725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25587579318255005347361933 9595342244345627005260725)
                  ·
                    refine ⟨899563335407402531743193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9595342244345627005260725 899563335407402531743193)
                    ·
                      rfl

theorem cell22_2627840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_2627840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627840 prefixEnd_2627840 := by exact prefixLift 2627840
  have htrace : WordTrace (prefixWord ++ tailWord_2627840) baseStart_2627840 baseEnd_2627840 := by
    simpa [prefixWord, tailWord_2627840, baseEnd_2627840] using wordTrace_append hprefix tailTrace_2627840
  have hstable : (prefixWord ++ tailWord_2627840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627840).length < 2 ^ (prefixWord ++ tailWord_2627840).sum := by decide
  have hdescent : baseEnd_2627840 < baseStart_2627840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627874 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2627874 : Nat := 118140960795 + 2627874 * 2 ^ 59
def prefixEnd_2627874 : Nat := 4983230072969 + 3 ^ 40 * 2627874 * 2
def baseEnd_2627874 : Nat := 899574974302237776393089

theorem tailTrace_2627874 : CollatzResearch.WordTrace tailWord_2627874 prefixEnd_2627874 899574974302237776393089 := by
  unfold tailWord_2627874
  simp only [CollatzResearch.WordTrace]
  refine ⟨23961609720417194498276669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63897625921112518662071117 23961609720417194498276669)
  ·
    refine ⟨8985603645156447936853751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23961609720417194498276669 8985603645156447936853751)
    ·
      refine ⟨13478405467734671905280627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8985603645156447936853751 13478405467734671905280627)
      ·
        refine ⟨20217608201602007857920941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13478405467734671905280627 20217608201602007857920941)
        ·
          refine ⟨7581603075600752946720353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20217608201602007857920941 7581603075600752946720353)
          ·
            refine ⟨5686202306700564710040265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7581603075600752946720353 5686202306700564710040265)
            ·
              refine ⟨4264651730025423532530199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686202306700564710040265 4264651730025423532530199)
              ·
                refine ⟨6396977595038135298795299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264651730025423532530199 6396977595038135298795299)
                ·
                  refine ⟨9595466392557202948192949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396977595038135298795299 9595466392557202948192949)
                  ·
                    refine ⟨899574974302237776393089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9595466392557202948192949 899574974302237776393089)
                    ·
                      rfl

theorem cell22_2627874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2627874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627874 prefixEnd_2627874 := by exact prefixLift 2627874
  have htrace : WordTrace (prefixWord ++ tailWord_2627874) baseStart_2627874 baseEnd_2627874 := by
    simpa [prefixWord, tailWord_2627874, baseEnd_2627874] using wordTrace_append hprefix tailTrace_2627874
  have hstable : (prefixWord ++ tailWord_2627874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627874).length < 2 ^ (prefixWord ++ tailWord_2627874).sum := by decide
  have hdescent : baseEnd_2627874 < baseStart_2627874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627970 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2627970 : Nat := 118140960795 + 2627970 * 2 ^ 59
def prefixEnd_2627970 : Nat := 4983230072969 + 3 ^ 40 * 2627970 * 2
def baseEnd_2627970 : Nat := 899607837064125525992795

theorem tailTrace_2627970 : CollatzResearch.WordTrace tailWord_2627970 prefixEnd_2627970 899607837064125525992795 := by
  unfold tailWord_2627970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23962485072330246597150341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63899960192880657592400909 23962485072330246597150341)
  ·
    refine ⟨4492965951061921236965689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23962485072330246597150341 4492965951061921236965689)
    ·
      refine ⟨3369724463296440927724267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4492965951061921236965689 3369724463296440927724267)
      ·
        refine ⟨5054586694944661391586401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369724463296440927724267 5054586694944661391586401)
        ·
          refine ⟨3790940021208496043689801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5054586694944661391586401 3790940021208496043689801)
          ·
            refine ⟨2843205015906372032767351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790940021208496043689801 2843205015906372032767351)
            ·
              refine ⟨4264807523859558049151027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843205015906372032767351 4264807523859558049151027)
              ·
                refine ⟨6397211285789337073726541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264807523859558049151027 6397211285789337073726541)
                ·
                  refine ⟨2398954232171001402647453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6397211285789337073726541 2398954232171001402647453)
                  ·
                    refine ⟨899607837064125525992795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2398954232171001402647453 899607837064125525992795)
                    ·
                      rfl

theorem cell22_2627970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2627970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2627970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2627970 prefixEnd_2627970 := by exact prefixLift 2627970
  have htrace : WordTrace (prefixWord ++ tailWord_2627970) baseStart_2627970 baseEnd_2627970 := by
    simpa [prefixWord, tailWord_2627970, baseEnd_2627970] using wordTrace_append hprefix tailTrace_2627970
  have hstable : (prefixWord ++ tailWord_2627970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627970).length < 2 ^ (prefixWord ++ tailWord_2627970).sum := by decide
  have hdescent : baseEnd_2627970 < baseStart_2627970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628022 : List Nat := [5, 1, 16]
def baseStart_2628022 : Nat := 118140960795 + 2628022 * 2 ^ 59
def prefixEnd_2628022 : Nat := 4983230072969 + 3 ^ 40 * 2628022 * 2
def baseEnd_2628022 : Nat := 411351457579704949105

theorem tailTrace_2628022 : CollatzResearch.WordTrace tailWord_2628022 prefixEnd_2628022 411351457579704949105 := by
  unfold tailWord_2628022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990739805320787454343395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63901224590088399512996213 5990739805320787454343395)
  ·
    refine ⟨8986109707981181181515093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5990739805320787454343395 8986109707981181181515093)
    ·
      refine ⟨411351457579704949105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 8986109707981181181515093 411351457579704949105)
      ·
        rfl

theorem cell22_2628022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 16].length) (baseStart_2628022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628022 prefixEnd_2628022 := by exact prefixLift 2628022
  have htrace : WordTrace (prefixWord ++ tailWord_2628022) baseStart_2628022 baseEnd_2628022 := by
    simpa [prefixWord, tailWord_2628022, baseEnd_2628022] using wordTrace_append hprefix tailTrace_2628022
  have hstable : (prefixWord ++ tailWord_2628022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628022).length < 2 ^ (prefixWord ++ tailWord_2628022).sum := by decide
  have hdescent : baseEnd_2628022 < baseStart_2628022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628028 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_2628028 : Nat := 118140960795 + 2628028 * 2 ^ 59
def prefixEnd_2628028 : Nat := 4983230072969 + 3 ^ 40 * 2628028 * 2
def baseEnd_2628028 : Nat := 299875897216477569347539

theorem tailTrace_2628028 : CollatzResearch.WordTrace tailWord_2628028 prefixEnd_2628028 299875897216477569347539 := by
  unfold tailWord_2628028
  simp only [CollatzResearch.WordTrace]
  refine ⟨47926027861555431147106369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63901370482073908196141825 47926027861555431147106369)
  ·
    refine ⟨35944520896166573360329777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47926027861555431147106369 35944520896166573360329777)
    ·
      refine ⟨26958390672124930020247333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35944520896166573360329777 26958390672124930020247333)
      ·
        refine ⟨5054698251023424378796375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26958390672124930020247333 5054698251023424378796375)
        ·
          refine ⟨7582047376535136568194563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054698251023424378796375 7582047376535136568194563)
          ·
            refine ⟨11373071064802704852291845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582047376535136568194563 11373071064802704852291845)
            ·
              refine ⟨2132450824650507159804721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11373071064802704852291845 2132450824650507159804721)
              ·
                refine ⟨1599338118487880369853541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132450824650507159804721 1599338118487880369853541)
                ·
                  refine ⟨299875897216477569347539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599338118487880369853541 299875897216477569347539)
                  ·
                    rfl

theorem cell22_2628028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_2628028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628028 prefixEnd_2628028 := by exact prefixLift 2628028
  have htrace : WordTrace (prefixWord ++ tailWord_2628028) baseStart_2628028 baseEnd_2628028 := by
    simpa [prefixWord, tailWord_2628028, baseEnd_2628028] using wordTrace_append hprefix tailTrace_2628028
  have hstable : (prefixWord ++ tailWord_2628028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628028).length < 2 ^ (prefixWord ++ tailWord_2628028).sum := by decide
  have hdescent : baseEnd_2628028 < baseStart_2628028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628039 : List Nat := [1, 1, 4, 1, 1, 6, 1, 7]
def baseStart_2628039 : Nat := 118140960795 + 2628039 * 2 ^ 59
def prefixEnd_2628039 : Nat := 4983230072969 + 3 ^ 40 * 2628039 * 2
def baseEnd_2628039 : Nat := 99959050797136927335287

theorem tailTrace_2628039 : CollatzResearch.WordTrace tailWord_2628039 prefixEnd_2628039 99959050797136927335287 := by
  unfold tailWord_2628039
  simp only [CollatzResearch.WordTrace]
  refine ⟨95852456926071011172863171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63901637950714007448575447 95852456926071011172863171)
  ·
    refine ⟨143778685389106516759294757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95852456926071011172863171 143778685389106516759294757)
    ·
      refine ⟨26958503510457471892367767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143778685389106516759294757 26958503510457471892367767)
      ·
        refine ⟨40437755265686207838551651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26958503510457471892367767 40437755265686207838551651)
        ·
          refine ⟨60656632898529311757827477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40437755265686207838551651 60656632898529311757827477)
          ·
            refine ⟨2843279667118561488648163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60656632898529311757827477 2843279667118561488648163)
            ·
              refine ⟨4264919500677842232972245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843279667118561488648163 4264919500677842232972245)
              ·
                refine ⟨99959050797136927335287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4264919500677842232972245 99959050797136927335287)
                ·
                  rfl

theorem cell22_2628039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 7].length) (baseStart_2628039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628039 prefixEnd_2628039 := by exact prefixLift 2628039
  have htrace : WordTrace (prefixWord ++ tailWord_2628039) baseStart_2628039 baseEnd_2628039 := by
    simpa [prefixWord, tailWord_2628039, baseEnd_2628039] using wordTrace_append hprefix tailTrace_2628039
  have hstable : (prefixWord ++ tailWord_2628039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628039).length < 2 ^ (prefixWord ++ tailWord_2628039).sum := by decide
  have hdescent : baseEnd_2628039 < baseStart_2628039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628112 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_2628112 : Nat := 118140960795 + 2628112 * 2 ^ 59
def prefixEnd_2628112 : Nat := 4983230072969 + 3 ^ 40 * 2628112 * 2
def baseEnd_2628112 : Nat := 299885482188694829647453

theorem tailTrace_2628112 : CollatzResearch.WordTrace tailWord_2628112 prefixEnd_2628112 299885482188694829647453 := by
  unfold tailWord_2628112
  simp only [CollatzResearch.WordTrace]
  refine ⟨47927559727403272320135295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63903412969871029760180393 47927559727403272320135295)
  ·
    refine ⟨71891339591104908480202943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47927559727403272320135295 71891339591104908480202943)
    ·
      refine ⟨107837009386657362720304415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71891339591104908480202943 107837009386657362720304415)
      ·
        refine ⟨161755514079986044080456623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107837009386657362720304415 161755514079986044080456623)
        ·
          refine ⟨242633271119979066120684935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161755514079986044080456623 242633271119979066120684935)
          ·
            refine ⟨363949906679968599181027403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242633271119979066120684935 363949906679968599181027403)
            ·
              refine ⟨545924860019952898771541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363949906679968599181027403 545924860019952898771541105)
              ·
                refine ⟨409443645014964674078655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545924860019952898771541105 409443645014964674078655829)
                ·
                  refine ⟨299885482188694829647453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 409443645014964674078655829 299885482188694829647453)
                  ·
                    rfl

theorem cell22_2628112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_2628112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628112 prefixEnd_2628112 := by exact prefixLift 2628112
  have htrace : WordTrace (prefixWord ++ tailWord_2628112) baseStart_2628112 baseEnd_2628112 := by
    simpa [prefixWord, tailWord_2628112, baseEnd_2628112] using wordTrace_append hprefix tailTrace_2628112
  have hstable : (prefixWord ++ tailWord_2628112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628112).length < 2 ^ (prefixWord ++ tailWord_2628112).sum := by decide
  have hdescent : baseEnd_2628112 < baseStart_2628112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628131 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 1, 4]
def baseStart_2628131 : Nat := 118140960795 + 2628131 * 2 ^ 59
def prefixEnd_2628131 : Nat := 4983230072969 + 3 ^ 40 * 2628131 * 2
def baseEnd_2628131 : Nat := 899662950654374772717301

theorem tailTrace_2628131 : CollatzResearch.WordTrace tailWord_2628131 prefixEnd_2628131 899662950654374772717301 := by
  unfold tailWord_2628131
  simp only [CollatzResearch.WordTrace]
  refine ⟨95855812441737710885212247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63903874961158473923474831 95855812441737710885212247)
  ·
    refine ⟨143783718662606566327818371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95855812441737710885212247 143783718662606566327818371)
    ·
      refine ⟨215675577993909849491727557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143783718662606566327818371 215675577993909849491727557)
      ·
        refine ⟨40439170873858096779698917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215675577993909849491727557 40439170873858096779698917)
        ·
          refine ⟨7582344538848393146193547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40439170873858096779698917 7582344538848393146193547)
          ·
            refine ⟨11373516808272589719290321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582344538848393146193547 11373516808272589719290321)
            ·
              refine ⟨8530137606204442289467741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11373516808272589719290321 8530137606204442289467741)
              ·
                refine ⟨3198801602326665858550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8530137606204442289467741 3198801602326665858550403)
                ·
                  refine ⟨4798202403489998787825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198801602326665858550403 4798202403489998787825605)
                  ·
                    refine ⟨899662950654374772717301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4798202403489998787825605 899662950654374772717301)
                    ·
                      rfl

theorem cell22_2628131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4].length) (baseStart_2628131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628131 prefixEnd_2628131 := by exact prefixLift 2628131
  have htrace : WordTrace (prefixWord ++ tailWord_2628131) baseStart_2628131 baseEnd_2628131 := by
    simpa [prefixWord, tailWord_2628131, baseEnd_2628131] using wordTrace_append hprefix tailTrace_2628131
  have hstable : (prefixWord ++ tailWord_2628131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628131).length < 2 ^ (prefixWord ++ tailWord_2628131).sum := by decide
  have hdescent : baseEnd_2628131 < baseStart_2628131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628146 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_2628146 : Nat := 118140960795 + 2628146 * 2 ^ 59
def prefixEnd_2628146 : Nat := 4983230072969 + 3 ^ 40 * 2628146 * 2
def baseEnd_2628146 : Nat := 299889361820306577864085

theorem tailTrace_2628146 : CollatzResearch.WordTrace tailWord_2628146 prefixEnd_2628146 299889361820306577864085 := by
  unfold tailWord_2628146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23964089884170842111752073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63904239691122245631338861 23964089884170842111752073)
  ·
    refine ⟨17973067413128131583814055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23964089884170842111752073 17973067413128131583814055)
    ·
      refine ⟨26959601119692197375721083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17973067413128131583814055 26959601119692197375721083)
      ·
        refine ⟨40439401679538296063581625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26959601119692197375721083 40439401679538296063581625)
        ·
          refine ⟨30329551259653722047686219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40439401679538296063581625 30329551259653722047686219)
          ·
            refine ⟨45494326889480583071529329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30329551259653722047686219 45494326889480583071529329)
            ·
              refine ⟨34120745167110437303646997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45494326889480583071529329 34120745167110437303646997)
              ·
                refine ⟨1599409929708301748608453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34120745167110437303646997 1599409929708301748608453)
                ·
                  refine ⟨299889361820306577864085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599409929708301748608453 299889361820306577864085)
                  ·
                    rfl

theorem cell22_2628146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_2628146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628146 prefixEnd_2628146 := by exact prefixLift 2628146
  have htrace : WordTrace (prefixWord ++ tailWord_2628146) baseStart_2628146 baseEnd_2628146 := by
    simpa [prefixWord, tailWord_2628146, baseEnd_2628146] using wordTrace_append hprefix tailTrace_2628146
  have hstable : (prefixWord ++ tailWord_2628146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628146).length < 2 ^ (prefixWord ++ tailWord_2628146).sum := by decide
  have hdescent : baseEnd_2628146 < baseStart_2628146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628159 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_2628159 : Nat := 118140960795 + 2628159 * 2 ^ 59
def prefixEnd_2628159 : Nat := 4983230072969 + 3 ^ 40 * 2628159 * 2
def baseEnd_2628159 : Nat := 899672535626592033017215

theorem tailTrace_2628159 : CollatzResearch.WordTrace tailWord_2628159 prefixEnd_2628159 899672535626592033017215 := by
  unfold tailWord_2628159
  simp only [CollatzResearch.WordTrace]
  refine ⟨95856833685636271667231531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63904555790424181111487687 95856833685636271667231531)
  ·
    refine ⟨143785250528454407500847297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95856833685636271667231531 143785250528454407500847297)
    ·
      refine ⟨107838937896340805625635473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143785250528454407500847297 107838937896340805625635473)
      ·
        refine ⟨80879203422255604219226605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107838937896340805625635473 80879203422255604219226605)
        ·
          refine ⟨30329701283345851582209977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80879203422255604219226605 30329701283345851582209977)
          ·
            refine ⟨22747275962509388686657483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30329701283345851582209977 22747275962509388686657483)
            ·
              refine ⟨34120913943764083029986225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22747275962509388686657483 34120913943764083029986225)
              ·
                refine ⟨25590685457823062272489669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34120913943764083029986225 25590685457823062272489669)
                ·
                  refine ⟨4798253523341824176091813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25590685457823062272489669 4798253523341824176091813)
                  ·
                    refine ⟨899672535626592033017215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4798253523341824176091813 899672535626592033017215)
                    ·
                      rfl

theorem cell22_2628159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_2628159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628159 prefixEnd_2628159 := by exact prefixLift 2628159
  have htrace : WordTrace (prefixWord ++ tailWord_2628159) baseStart_2628159 baseEnd_2628159 := by
    simpa [prefixWord, tailWord_2628159, baseEnd_2628159] using wordTrace_append hprefix tailTrace_2628159
  have hstable : (prefixWord ++ tailWord_2628159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628159).length < 2 ^ (prefixWord ++ tailWord_2628159).sum := by decide
  have hdescent : baseEnd_2628159 < baseStart_2628159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628174 : List Nat := [4, 1, 1, 1, 1, 2, 4, 8]
def baseStart_2628174 : Nat := 118140960795 + 2628174 * 2 ^ 59
def prefixEnd_2628174 : Nat := 4983230072969 + 3 ^ 40 * 2628174 * 2
def baseEnd_2628174 : Nat := 99964185603681888210241

theorem tailTrace_2628174 : CollatzResearch.WordTrace tailWord_2628174 prefixEnd_2628174 99964185603681888210241 := by
  unfold tailWord_2628174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11982172597572741153628447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63904920520387952819351717 11982172597572741153628447)
  ·
    refine ⟨17973258896359111730442671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11982172597572741153628447 17973258896359111730442671)
    ·
      refine ⟨26959888344538667595664007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17973258896359111730442671 26959888344538667595664007)
      ·
        refine ⟨40439832516808001393496011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26959888344538667595664007 40439832516808001393496011)
        ·
          refine ⟨60659748775212002090244017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40439832516808001393496011 60659748775212002090244017)
          ·
            refine ⟨45494811581409001567683013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60659748775212002090244017 45494811581409001567683013)
            ·
              refine ⟨8530277171514187793940565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45494811581409001567683013 8530277171514187793940565)
              ·
                refine ⟨99964185603681888210241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8530277171514187793940565 99964185603681888210241)
                ·
                  rfl

theorem cell22_2628174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_2628174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628174 prefixEnd_2628174 := by exact prefixLift 2628174
  have htrace : WordTrace (prefixWord ++ tailWord_2628174) baseStart_2628174 baseEnd_2628174 := by
    simpa [prefixWord, tailWord_2628174, baseEnd_2628174] using wordTrace_append hprefix tailTrace_2628174
  have hstable : (prefixWord ++ tailWord_2628174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628174).length < 2 ^ (prefixWord ++ tailWord_2628174).sum := by decide
  have hdescent : baseEnd_2628174 < baseStart_2628174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628197 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 4]
def baseStart_2628197 : Nat := 118140960795 + 2628197 * 2 ^ 59
def prefixEnd_2628197 : Nat := 4983230072969 + 3 ^ 40 * 2628197 * 2
def baseEnd_2628197 : Nat := 299895181267724200189033

theorem tailTrace_2628197 : CollatzResearch.WordTrace tailWord_2628197 prefixEnd_2628197 299895181267724200189033 := by
  unfold tailWord_2628197
  simp only [CollatzResearch.WordTrace]
  refine ⟨95858219659498604157114845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63905479772999069438076563 95858219659498604157114845)
  ·
    refine ⟨35946832372311976558918067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95858219659498604157114845 35946832372311976558918067)
    ·
      refine ⟨53920248558467964838377101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35946832372311976558918067 53920248558467964838377101)
      ·
        refine ⟨20220093209425486814391413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53920248558467964838377101 20220093209425486814391413)
        ·
          refine ⟨1895633738383639388849195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20220093209425486814391413 1895633738383639388849195)
          ·
            refine ⟨2843450607575459083273793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895633738383639388849195 2843450607575459083273793)
            ·
              refine ⟨2132587955681594312455345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843450607575459083273793 2132587955681594312455345)
              ·
                refine ⟨1599440966761195734341509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132587955681594312455345 1599440966761195734341509)
                ·
                  refine ⟨299895181267724200189033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599440966761195734341509 299895181267724200189033)
                  ·
                    rfl

theorem cell22_2628197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_2628197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628197 prefixEnd_2628197 := by exact prefixLift 2628197
  have htrace : WordTrace (prefixWord ++ tailWord_2628197) baseStart_2628197 baseEnd_2628197 := by
    simpa [prefixWord, tailWord_2628197, baseEnd_2628197] using wordTrace_append hprefix tailTrace_2628197
  have hstable : (prefixWord ++ tailWord_2628197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628197).length < 2 ^ (prefixWord ++ tailWord_2628197).sum := by decide
  have hdescent : baseEnd_2628197 < baseStart_2628197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628204 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2628204 : Nat := 118140960795 + 2628204 * 2 ^ 59
def prefixEnd_2628204 : Nat := 4983230072969 + 3 ^ 40 * 2628204 * 2
def baseEnd_2628204 : Nat := 899687940046226915642077

theorem tailTrace_2628204 : CollatzResearch.WordTrace tailWord_2628204 prefixEnd_2628204 899687940046226915642077 := by
  unfold tailWord_2628204
  simp only [CollatzResearch.WordTrace]
  refine ⟨47929237485236622176309833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63905649980315496235079777 47929237485236622176309833)
  ·
    refine ⟨35946928113927466632232375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47929237485236622176309833 35946928113927466632232375)
    ·
      refine ⟨53920392170891199948348563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35946928113927466632232375 53920392170891199948348563)
      ·
        refine ⟨80880588256336799922522845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53920392170891199948348563 80880588256336799922522845)
        ·
          refine ⟨30330220596126299970946067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80880588256336799922522845 30330220596126299970946067)
          ·
            refine ⟨45495330894189449956419101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30330220596126299970946067 45495330894189449956419101)
            ·
              refine ⟨17060749085321043733657163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45495330894189449956419101 17060749085321043733657163)
              ·
                refine ⟨25591123627981565600485745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17060749085321043733657163 25591123627981565600485745)
                ·
                  refine ⟨19193342720986174200364309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25591123627981565600485745 19193342720986174200364309)
                  ·
                    refine ⟨899687940046226915642077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19193342720986174200364309 899687940046226915642077)
                    ·
                      rfl

theorem cell22_2628204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2628204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628204 prefixEnd_2628204 := by exact prefixLift 2628204
  have htrace : WordTrace (prefixWord ++ tailWord_2628204) baseStart_2628204 baseEnd_2628204 := by
    simpa [prefixWord, tailWord_2628204, baseEnd_2628204] using wordTrace_append hprefix tailTrace_2628204
  have hstable : (prefixWord ++ tailWord_2628204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628204).length < 2 ^ (prefixWord ++ tailWord_2628204).sum := by decide
  have hdescent : baseEnd_2628204 < baseStart_2628204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628208 : List Nat := [2, 1, 1, 1, 8, 1, 1, 7]
def baseStart_2628208 : Nat := 118140960795 + 2628208 * 2 ^ 59
def prefixEnd_2628208 : Nat := 4983230072969 + 3 ^ 40 * 2628208 * 2
def baseEnd_2628208 : Nat := 99965478814219137615785

theorem tailTrace_2628208 : CollatzResearch.WordTrace tailWord_2628208 prefixEnd_2628208 99965478814219137615785 := by
  unfold tailWord_2628208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47929310431229376517882639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63905747241639168690510185 47929310431229376517882639)
  ·
    refine ⟨71893965646844064776823959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47929310431229376517882639 71893965646844064776823959)
    ·
      refine ⟨107840948470266097165235939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71893965646844064776823959 107840948470266097165235939)
      ·
        refine ⟨161761422705399145747853909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107840948470266097165235939 161761422705399145747853909)
        ·
          refine ⟨1895641672328896239232663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 161761422705399145747853909 1895641672328896239232663)
          ·
            refine ⟨2843462508493344358848995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895641672328896239232663 2843462508493344358848995)
            ·
              refine ⟨4265193762740016538273493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843462508493344358848995 4265193762740016538273493)
              ·
                refine ⟨99965478814219137615785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4265193762740016538273493 99965478814219137615785)
                ·
                  rfl

theorem cell22_2628208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_2628208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628208 prefixEnd_2628208 := by exact prefixLift 2628208
  have htrace : WordTrace (prefixWord ++ tailWord_2628208) baseStart_2628208 baseEnd_2628208 := by
    simpa [prefixWord, tailWord_2628208, baseEnd_2628208] using wordTrace_append hprefix tailTrace_2628208
  have hstable : (prefixWord ++ tailWord_2628208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628208).length < 2 ^ (prefixWord ++ tailWord_2628208).sum := by decide
  have hdescent : baseEnd_2628208 < baseStart_2628208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628311 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2628311 : Nat := 118140960795 + 2628311 * 2 ^ 59
def prefixEnd_2628311 : Nat := 4983230072969 + 3 ^ 40 * 2628311 * 2
def baseEnd_2628311 : Nat := 899724568332914303216749

theorem tailTrace_2628311 : CollatzResearch.WordTrace tailWord_2628311 prefixEnd_2628311 899724568332914303216749 := by
  unfold tailWord_2628311
  simp only [CollatzResearch.WordTrace]
  refine ⟨95862377581085601626764787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63908251720723734417843191 95862377581085601626764787)
  ·
    refine ⟨143793566371628402440147181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95862377581085601626764787 143793566371628402440147181)
    ·
      refine ⟨53922587389360650915055193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143793566371628402440147181 53922587389360650915055193)
      ·
        refine ⟨40441940542020488186291395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53922587389360650915055193 40441940542020488186291395)
        ·
          refine ⟨60662910813030732279437093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40441940542020488186291395 60662910813030732279437093)
          ·
            refine ⟨11374295777443262302394455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60662910813030732279437093 11374295777443262302394455)
            ·
              refine ⟨17061443666164893453591683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11374295777443262302394455 17061443666164893453591683)
              ·
                refine ⟨25592165499247340180387525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17061443666164893453591683 25592165499247340180387525)
                ·
                  refine ⟨4798531031108876283822661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25592165499247340180387525 4798531031108876283822661)
                  ·
                    refine ⟨899724568332914303216749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4798531031108876283822661 899724568332914303216749)
                    ·
                      rfl

theorem cell22_2628311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2628311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628311 prefixEnd_2628311 := by exact prefixLift 2628311
  have htrace : WordTrace (prefixWord ++ tailWord_2628311) baseStart_2628311 baseEnd_2628311 := by
    simpa [prefixWord, tailWord_2628311, baseEnd_2628311] using wordTrace_append hprefix tailTrace_2628311
  have hstable : (prefixWord ++ tailWord_2628311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628311).length < 2 ^ (prefixWord ++ tailWord_2628311).sum := by decide
  have hdescent : baseEnd_2628311 < baseStart_2628311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628313 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_2628313 : Nat := 118140960795 + 2628313 * 2 ^ 59
def prefixEnd_2628313 : Nat := 4983230072969 + 3 ^ 40 * 2628313 * 2
def baseEnd_2628313 : Nat := 899725252973786964666743

theorem tailTrace_2628313 : CollatzResearch.WordTrace tailWord_2628313 prefixEnd_2628313 899725252973786964666743 := by
  unfold tailWord_2628313
  simp only [CollatzResearch.WordTrace]
  refine ⟨95862450527078355968337593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63908300351385570645558395 95862450527078355968337593)
  ·
    refine ⟨71896837895308766976253195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95862450527078355968337593 71896837895308766976253195)
    ·
      refine ⟨107845256842963150464379793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71896837895308766976253195 107845256842963150464379793)
      ·
        refine ⟨80883942632222362848284845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107845256842963150464379793 80883942632222362848284845)
        ·
          refine ⟨30331478487083386068106817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80883942632222362848284845 30331478487083386068106817)
          ·
            refine ⟨22748608865312539551080113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30331478487083386068106817 22748608865312539551080113)
            ·
              refine ⟨17061456648984404663310085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22748608865312539551080113 17061456648984404663310085)
              ·
                refine ⟨3199023121684575874370641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17061456648984404663310085 3199023121684575874370641)
                ·
                  refine ⟨2399267341263431905777981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199023121684575874370641 2399267341263431905777981)
                  ·
                    refine ⟨899725252973786964666743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399267341263431905777981 899725252973786964666743)
                    ·
                      rfl

theorem cell22_2628313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_2628313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628313 prefixEnd_2628313 := by exact prefixLift 2628313
  have htrace : WordTrace (prefixWord ++ tailWord_2628313) baseStart_2628313 baseEnd_2628313 := by
    simpa [prefixWord, tailWord_2628313, baseEnd_2628313] using wordTrace_append hprefix tailTrace_2628313
  have hstable : (prefixWord ++ tailWord_2628313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628313).length < 2 ^ (prefixWord ++ tailWord_2628313).sum := by decide
  have hdescent : baseEnd_2628313 < baseStart_2628313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628422 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2628422 : Nat := 118140960795 + 2628422 * 2 ^ 59
def prefixEnd_2628422 : Nat := 4983230072969 + 3 ^ 40 * 2628422 * 2
def baseEnd_2628422 : Nat := 299920855300449004563803

theorem tailTrace_2628422 : CollatzResearch.WordTrace tailWord_2628422 prefixEnd_2628422 299920855300449004563803 := by
  unfold tailWord_2628422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995825815115108362001735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63910950722455645056037013 2995825815115108362001735)
  ·
    refine ⟨4493738722672662543002603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2995825815115108362001735 4493738722672662543002603)
    ·
      refine ⟨6740608084008993814503905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493738722672662543002603 6740608084008993814503905)
      ·
        refine ⟨5055456063006745360877929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6740608084008993814503905 5055456063006745360877929)
        ·
          refine ⟨3791592047255059020658447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5055456063006745360877929 3791592047255059020658447)
          ·
            refine ⟨5687388070882588530987671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791592047255059020658447 5687388070882588530987671)
            ·
              refine ⟨8531082106323882796481507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5687388070882588530987671 8531082106323882796481507)
              ·
                refine ⟨12796623159485824194722261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8531082106323882796481507 12796623159485824194722261)
                ·
                  refine ⟨299920855300449004563803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12796623159485824194722261 299920855300449004563803)
                  ·
                    rfl

theorem cell22_2628422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2628422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628422 prefixEnd_2628422 := by exact prefixLift 2628422
  have htrace : WordTrace (prefixWord ++ tailWord_2628422) baseStart_2628422 baseEnd_2628422 := by
    simpa [prefixWord, tailWord_2628422, baseEnd_2628422] using wordTrace_append hprefix tailTrace_2628422
  have hstable : (prefixWord ++ tailWord_2628422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628422).length < 2 ^ (prefixWord ++ tailWord_2628422).sum := by decide
  have hdescent : baseEnd_2628422 < baseStart_2628422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628538 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_2628538 : Nat := 118140960795 + 2628538 * 2 ^ 59
def prefixEnd_2628538 : Nat := 4983230072969 + 3 ^ 40 * 2628538 * 2
def baseEnd_2628538 : Nat := 899802275071961377791053

theorem tailTrace_2628538 : CollatzResearch.WordTrace tailWord_2628538 prefixEnd_2628538 899802275071961377791053 := by
  unfold tailWord_2628538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23967664237815804848819567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63913771300842146263518845 23967664237815804848819567)
  ·
    refine ⟨35951496356723707273229351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23967664237815804848819567 35951496356723707273229351)
    ·
      refine ⟨53927244535085560909844027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35951496356723707273229351 53927244535085560909844027)
      ·
        refine ⟨80890866802628341364766041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53927244535085560909844027 80890866802628341364766041)
        ·
          refine ⟨60668150101971256023574531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80890866802628341364766041 60668150101971256023574531)
          ·
            refine ⟨91002225152956884035361797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60668150101971256023574531 91002225152956884035361797)
            ·
              refine ⟨17062917216179415756630337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91002225152956884035361797 17062917216179415756630337)
              ·
                refine ⟨12797187912134561817472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17062917216179415756630337 12797187912134561817472753)
                ·
                  refine ⟨9597890934100921363104565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12797187912134561817472753 9597890934100921363104565)
                  ·
                    refine ⟨899802275071961377791053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9597890934100921363104565 899802275071961377791053)
                    ·
                      rfl

theorem cell22_2628538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_2628538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628538 prefixEnd_2628538 := by exact prefixLift 2628538
  have htrace : WordTrace (prefixWord ++ tailWord_2628538) baseStart_2628538 baseEnd_2628538 := by
    simpa [prefixWord, tailWord_2628538, baseEnd_2628538] using wordTrace_append hprefix tailTrace_2628538
  have hstable : (prefixWord ++ tailWord_2628538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628538).length < 2 ^ (prefixWord ++ tailWord_2628538).sum := by decide
  have hdescent : baseEnd_2628538 < baseStart_2628538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628544 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 1, 3]
def baseStart_2628544 : Nat := 118140960795 + 2628544 * 2 ^ 59
def prefixEnd_2628544 : Nat := 4983230072969 + 3 ^ 40 * 2628544 * 2
def baseEnd_2628544 : Nat := 899804328994579362141035

theorem tailTrace_2628544 : CollatzResearch.WordTrace tailWord_2628544 prefixEnd_2628544 899804328994579362141035 := by
  unfold tailWord_2628544
  simp only [CollatzResearch.WordTrace]
  refine ⟨47935437894620741209998343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63913917192827654946664457 47935437894620741209998343)
  ·
    refine ⟨71903156841931111814997515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47935437894620741209998343 71903156841931111814997515)
    ·
      refine ⟨107854735262896667722496273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71903156841931111814997515 107854735262896667722496273)
      ·
        refine ⟨80891051447172500791872205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107854735262896667722496273 80891051447172500791872205)
        ·
          refine ⟨30334144292689687796952077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80891051447172500791872205 30334144292689687796952077)
          ·
            refine ⟨11375304109758632923857029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30334144292689687796952077 11375304109758632923857029)
            ·
              refine ⟨2132869520579743673223193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11375304109758632923857029 2132869520579743673223193)
              ·
                refine ⟨1599652140434807754917395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132869520579743673223193 1599652140434807754917395)
                ·
                  refine ⟨2399478210652211632376093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599652140434807754917395 2399478210652211632376093)
                  ·
                    refine ⟨899804328994579362141035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399478210652211632376093 899804328994579362141035)
                    ·
                      rfl

theorem cell22_2628544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_2628544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628544 prefixEnd_2628544 := by exact prefixLift 2628544
  have htrace : WordTrace (prefixWord ++ tailWord_2628544) baseStart_2628544 baseEnd_2628544 := by
    simpa [prefixWord, tailWord_2628544, baseEnd_2628544] using wordTrace_append hprefix tailTrace_2628544
  have hstable : (prefixWord ++ tailWord_2628544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628544).length < 2 ^ (prefixWord ++ tailWord_2628544).sum := by decide
  have hdescent : baseEnd_2628544 < baseStart_2628544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628568 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_2628568 : Nat := 118140960795 + 2628568 * 2 ^ 59
def prefixEnd_2628568 : Nat := 4983230072969 + 3 ^ 40 * 2628568 * 2
def baseEnd_2628568 : Nat := 299937514895017099846987

theorem tailTrace_2628568 : CollatzResearch.WordTrace tailWord_2628568 prefixEnd_2628568 299937514895017099846987 := by
  unfold tailWord_2628568
  simp only [CollatzResearch.WordTrace]
  refine ⟨47935875570577267259435179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63914500760769689679246905 47935875570577267259435179)
  ·
    refine ⟨71903813355865900889152769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47935875570577267259435179 71903813355865900889152769)
    ·
      refine ⟨53927860016899425666864577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71903813355865900889152769 53927860016899425666864577)
      ·
        refine ⟨40445895012674569250148433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53927860016899425666864577 40445895012674569250148433)
        ·
          refine ⟨30334421259505926937611325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40445895012674569250148433 30334421259505926937611325)
          ·
            refine ⟨11375407972314722601604247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30334421259505926937611325 11375407972314722601604247)
            ·
              refine ⟨17063111958472083902406371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11375407972314722601604247 17063111958472083902406371)
              ·
                refine ⟨25594667937708125853609557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17063111958472083902406371 25594667937708125853609557)
                ·
                  refine ⟨299937514895017099846987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25594667937708125853609557 299937514895017099846987)
                  ·
                    rfl

theorem cell22_2628568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_2628568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628568 prefixEnd_2628568 := by exact prefixLift 2628568
  have htrace : WordTrace (prefixWord ++ tailWord_2628568) baseStart_2628568 baseEnd_2628568 := by
    simpa [prefixWord, tailWord_2628568, baseEnd_2628568] using wordTrace_append hprefix tailTrace_2628568
  have hstable : (prefixWord ++ tailWord_2628568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628568).length < 2 ^ (prefixWord ++ tailWord_2628568).sum := by decide
  have hdescent : baseEnd_2628568 < baseStart_2628568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628570 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_2628570 : Nat := 118140960795 + 2628570 * 2 ^ 59
def prefixEnd_2628570 : Nat := 4983230072969 + 3 ^ 40 * 2628570 * 2
def baseEnd_2628570 : Nat := 899813229325923960990955

theorem tailTrace_2628570 : CollatzResearch.WordTrace tailWord_2628570 prefixEnd_2628570 899813229325923960990955 := by
  unfold tailWord_2628570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23967956021786822215110791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63914549391431525906962109 23967956021786822215110791)
  ·
    refine ⟨35951934032680233322666187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23967956021786822215110791 35951934032680233322666187)
    ·
      refine ⟨53927901049020349983999281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35951934032680233322666187 53927901049020349983999281)
      ·
        refine ⟨40445925786765262487999461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53927901049020349983999281 40445925786765262487999461)
        ·
          refine ⟨7583611085018486716499899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40445925786765262487999461 7583611085018486716499899)
          ·
            refine ⟨11375416627527730074749849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7583611085018486716499899 11375416627527730074749849)
            ·
              refine ⟨8531562470645797556062387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11375416627527730074749849 8531562470645797556062387)
              ·
                refine ⟨12797343705968696334093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8531562470645797556062387 12797343705968696334093581)
                ·
                  refine ⟨4799003889738261125285093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12797343705968696334093581 4799003889738261125285093)
                  ·
                    refine ⟨899813229325923960990955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799003889738261125285093 899813229325923960990955)
                    ·
                      rfl

theorem cell22_2628570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_2628570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628570 prefixEnd_2628570 := by exact prefixLift 2628570
  have htrace : WordTrace (prefixWord ++ tailWord_2628570) baseStart_2628570 baseEnd_2628570 := by
    simpa [prefixWord, tailWord_2628570, baseEnd_2628570] using wordTrace_append hprefix tailTrace_2628570
  have hstable : (prefixWord ++ tailWord_2628570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628570).length < 2 ^ (prefixWord ++ tailWord_2628570).sum := by decide
  have hdescent : baseEnd_2628570 < baseStart_2628570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628613 : List Nat := [1, 3, 1, 1, 2, 3, 2, 9]
def baseStart_2628613 : Nat := 118140960795 + 2628613 * 2 ^ 59
def prefixEnd_2628613 : Nat := 4983230072969 + 3 ^ 40 * 2628613 * 2
def baseEnd_2628613 : Nat := 99980883233854020240647

theorem tailTrace_2628613 : CollatzResearch.WordTrace tailWord_2628613 prefixEnd_2628613 99980883233854020240647 := by
  unfold tailWord_2628613
  simp only [CollatzResearch.WordTrace]
  refine ⟨95873392425991507204258493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63915594950661004802838995 95873392425991507204258493)
  ·
    refine ⟨35952522159746815201596935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95873392425991507204258493 35952522159746815201596935)
    ·
      refine ⟨53928783239620222802395403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35952522159746815201596935 53928783239620222802395403)
      ·
        refine ⟨80893174859430334203593105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53928783239620222802395403 80893174859430334203593105)
        ·
          refine ⟨60669881144572750652694829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80893174859430334203593105 60669881144572750652694829)
          ·
            refine ⟨22751205429214781494760561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60669881144572750652694829 22751205429214781494760561)
            ·
              refine ⟨17063404071911086121070421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22751205429214781494760561 17063404071911086121070421)
              ·
                refine ⟨99980883233854020240647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17063404071911086121070421 99980883233854020240647)
                ·
                  rfl

theorem cell22_2628613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 9].length) (baseStart_2628613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628613 prefixEnd_2628613 := by exact prefixLift 2628613
  have htrace : WordTrace (prefixWord ++ tailWord_2628613) baseStart_2628613 baseEnd_2628613 := by
    simpa [prefixWord, tailWord_2628613, baseEnd_2628613] using wordTrace_append hprefix tailTrace_2628613
  have hstable : (prefixWord ++ tailWord_2628613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628613).length < 2 ^ (prefixWord ++ tailWord_2628613).sum := by decide
  have hdescent : baseEnd_2628613 < baseStart_2628613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628636 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_2628636 : Nat := 118140960795 + 2628636 * 2 ^ 59
def prefixEnd_2628636 : Nat := 4983230072969 + 3 ^ 40 * 2628636 * 2
def baseEnd_2628636 : Nat := 299945274158240596280251

theorem tailTrace_2628636 : CollatzResearch.WordTrace tailWord_2628636 prefixEnd_2628636 299945274158240596280251 := by
  unfold tailWord_2628636
  simp only [CollatzResearch.WordTrace]
  refine ⟨47937115652454091066172881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63916154203272121421563841 47937115652454091066172881)
  ·
    refine ⟨35952836739340568299629661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47937115652454091066172881 35952836739340568299629661)
    ·
      refine ⟨13482313777252713112361123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35952836739340568299629661 13482313777252713112361123)
      ·
        refine ⟨20223470665879069668541685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13482313777252713112361123 20223470665879069668541685)
        ·
          refine ⟨1895950374926162781425783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20223470665879069668541685 1895950374926162781425783)
          ·
            refine ⟨2843925562389244172138675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895950374926162781425783 2843925562389244172138675)
            ·
              refine ⟨4265888343583866258208013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843925562389244172138675 4265888343583866258208013)
              ·
                refine ⟨1599708128843949846828005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4265888343583866258208013 1599708128843949846828005)
                ·
                  refine ⟨299945274158240596280251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599708128843949846828005 299945274158240596280251)
                  ·
                    rfl

theorem cell22_2628636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_2628636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628636 prefixEnd_2628636 := by exact prefixLift 2628636
  have htrace : WordTrace (prefixWord ++ tailWord_2628636) baseStart_2628636 baseEnd_2628636 := by
    simpa [prefixWord, tailWord_2628636, baseEnd_2628636] using wordTrace_append hprefix tailTrace_2628636
  have hstable : (prefixWord ++ tailWord_2628636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628636).length < 2 ^ (prefixWord ++ tailWord_2628636).sum := by decide
  have hdescent : baseEnd_2628636 < baseStart_2628636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628647 : List Nat := [1, 1, 7, 1, 1, 3, 8]
def baseStart_2628647 : Nat := 118140960795 + 2628647 * 2 ^ 59
def prefixEnd_2628647 : Nat := 4983230072969 + 3 ^ 40 * 2628647 * 2
def baseEnd_2628647 : Nat := 33327392148130423215397

theorem tailTrace_2628647 : CollatzResearch.WordTrace tailWord_2628647 prefixEnd_2628647 33327392148130423215397 := by
  unfold tailWord_2628647
  simp only [CollatzResearch.WordTrace]
  refine ⟨95874632507868331010996195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63916421671912220673997463 95874632507868331010996195)
  ·
    refine ⟨143811948761802496516494293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95874632507868331010996195 143811948761802496516494293)
    ·
      refine ⟨3370592549104746012105335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 143811948761802496516494293 3370592549104746012105335)
      ·
        refine ⟨5055888823657119018158003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370592549104746012105335 5055888823657119018158003)
        ·
          refine ⟨7583833235485678527237005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055888823657119018158003 7583833235485678527237005)
          ·
            refine ⟨2843937463307129447713877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7583833235485678527237005 2843937463307129447713877)
            ·
              refine ⟨33327392148130423215397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2843937463307129447713877 33327392148130423215397)
              ·
                rfl

theorem cell22_2628647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 8].length) (baseStart_2628647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628647 prefixEnd_2628647 := by exact prefixLift 2628647
  have htrace : WordTrace (prefixWord ++ tailWord_2628647) baseStart_2628647 baseEnd_2628647 := by
    simpa [prefixWord, tailWord_2628647, baseEnd_2628647] using wordTrace_append hprefix tailTrace_2628647
  have hstable : (prefixWord ++ tailWord_2628647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628647).length < 2 ^ (prefixWord ++ tailWord_2628647).sum := by decide
  have hdescent : baseEnd_2628647 < baseStart_2628647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628675 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 5]
def baseStart_2628675 : Nat := 118140960795 + 2628675 * 2 ^ 59
def prefixEnd_2628675 : Nat := 4983230072969 + 3 ^ 40 * 2628675 * 2
def baseEnd_2628675 : Nat := 299949724323912895705211

theorem tailTrace_2628675 : CollatzResearch.WordTrace tailWord_2628675 prefixEnd_2628675 299949724323912895705211 := by
  unfold tailWord_2628675
  simp only [CollatzResearch.WordTrace]
  refine ⟨95875653751766891793015479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63917102501177927862010319 95875653751766891793015479)
  ·
    refine ⟨143813480627650337689523219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95875653751766891793015479 143813480627650337689523219)
    ·
      refine ⟨215720220941475506534284829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143813480627650337689523219 215720220941475506534284829)
      ·
        refine ⟨80895082853053314950356811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215720220941475506534284829 80895082853053314950356811)
        ·
          refine ⟨121342624279579972425535217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80895082853053314950356811 121342624279579972425535217)
          ·
            refine ⟨91006968209684979319151413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121342624279579972425535217 91006968209684979319151413)
            ·
              refine ⟨8531903269657966811170445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91006968209684979319151413 8531903269657966811170445)
              ·
                refine ⟨3199463726121737554188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8531903269657966811170445 3199463726121737554188917)
                ·
                  refine ⟨299949724323912895705211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3199463726121737554188917 299949724323912895705211)
                  ·
                    rfl

theorem cell22_2628675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 5].length) (baseStart_2628675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628675 prefixEnd_2628675 := by exact prefixLift 2628675
  have htrace : WordTrace (prefixWord ++ tailWord_2628675) baseStart_2628675 baseEnd_2628675 := by
    simpa [prefixWord, tailWord_2628675, baseEnd_2628675] using wordTrace_append hprefix tailTrace_2628675
  have hstable : (prefixWord ++ tailWord_2628675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628675).length < 2 ^ (prefixWord ++ tailWord_2628675).sum := by decide
  have hdescent : baseEnd_2628675 < baseStart_2628675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628720 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_2628720 : Nat := 118140960795 + 2628720 * 2 ^ 59
def prefixEnd_2628720 : Nat := 4983230072969 + 3 ^ 40 * 2628720 * 2
def baseEnd_2628720 : Nat := 299954859130457856580165

theorem tailTrace_2628720 : CollatzResearch.WordTrace tailWord_2628720 prefixEnd_2628720 299954859130457856580165 := by
  unfold tailWord_2628720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938647518301932239201807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63918196691069242985602409 47938647518301932239201807)
  ·
    refine ⟨71907971277452898358802711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47938647518301932239201807 71907971277452898358802711)
    ·
      refine ⟨107861956916179347538204067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71907971277452898358802711 107861956916179347538204067)
      ·
        refine ⟨161792935374269021307306101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107861956916179347538204067 161792935374269021307306101)
        ·
          refine ⟨15168087691337720747559947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161792935374269021307306101 15168087691337720747559947)
          ·
            refine ⟨22752131537006581121339921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15168087691337720747559947 22752131537006581121339921)
            ·
              refine ⟨17064098652754935841004941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22752131537006581121339921 17064098652754935841004941)
              ·
                refine ⟨6399036994783100940376853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17064098652754935841004941 6399036994783100940376853)
                ·
                  refine ⟨299954859130457856580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6399036994783100940376853 299954859130457856580165)
                  ·
                    rfl

theorem cell22_2628720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_2628720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628720 prefixEnd_2628720 := by exact prefixLift 2628720
  have htrace : WordTrace (prefixWord ++ tailWord_2628720) baseStart_2628720 baseEnd_2628720 := by
    simpa [prefixWord, tailWord_2628720, baseEnd_2628720] using wordTrace_append hprefix tailTrace_2628720
  have hstable : (prefixWord ++ tailWord_2628720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628720).length < 2 ^ (prefixWord ++ tailWord_2628720).sum := by decide
  have hdescent : baseEnd_2628720 < baseStart_2628720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628737 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 6]
def baseStart_2628737 : Nat := 118140960795 + 2628737 * 2 ^ 59
def prefixEnd_2628737 : Nat := 4983230072969 + 3 ^ 40 * 2628737 * 2
def baseEnd_2628737 : Nat := 299956798946263730688481

theorem tailTrace_2628737 : CollatzResearch.WordTrace tailWord_2628737 prefixEnd_2628737 299956798946263730688481 := by
  unfold tailWord_2628737
  simp only [CollatzResearch.WordTrace]
  refine ⟨95877915077542276381772465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63918610051694850921181643 95877915077542276381772465)
  ·
    refine ⟨71908436308156707286329349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95877915077542276381772465 71908436308156707286329349)
    ·
      refine ⟨13482831807779382616186753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71908436308156707286329349 13482831807779382616186753)
      ·
        refine ⟨10112123855834536962140065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13482831807779382616186753 10112123855834536962140065)
        ·
          refine ⟨7584092891875902721605049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10112123855834536962140065 7584092891875902721605049)
          ·
            refine ⟨5688069668906927041203787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7584092891875902721605049 5688069668906927041203787)
            ·
              refine ⟨8532104503360390561805681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5688069668906927041203787 8532104503360390561805681)
              ·
                refine ⟨6399078377520292921354261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8532104503360390561805681 6399078377520292921354261)
                ·
                  refine ⟨299956798946263730688481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6399078377520292921354261 299956798946263730688481)
                  ·
                    rfl

theorem cell22_2628737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_2628737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628737 prefixEnd_2628737 := by exact prefixLift 2628737
  have htrace : WordTrace (prefixWord ++ tailWord_2628737) baseStart_2628737 baseEnd_2628737 := by
    simpa [prefixWord, tailWord_2628737, baseEnd_2628737] using wordTrace_append hprefix tailTrace_2628737
  have hstable : (prefixWord ++ tailWord_2628737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628737).length < 2 ^ (prefixWord ++ tailWord_2628737).sum := by decide
  have hdescent : baseEnd_2628737 < baseStart_2628737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628754 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_2628754 : Nat := 118140960795 + 2628754 * 2 ^ 59
def prefixEnd_2628754 : Nat := 4983230072969 + 3 ^ 40 * 2628754 * 2
def baseEnd_2628754 : Nat := 299958738762069604796797

theorem tailTrace_2628754 : CollatzResearch.WordTrace tailWord_2628754 prefixEnd_2628754 299958738762069604796797 := by
  unfold tailWord_2628754
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969633779620172071285329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63919023412320458856760877 23969633779620172071285329)
  ·
    refine ⟨17977225334715129053463997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23969633779620172071285329 17977225334715129053463997)
    ·
      refine ⟨6741459500518173395048999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17977225334715129053463997 6741459500518173395048999)
      ·
        refine ⟨10112189250777260092573499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6741459500518173395048999 10112189250777260092573499)
        ·
          refine ⟨15168283876165890138860249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10112189250777260092573499 15168283876165890138860249)
          ·
            refine ⟨11376212907124417604145187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15168283876165890138860249 11376212907124417604145187)
            ·
              refine ⟨17064319360686626406217781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11376212907124417604145187 17064319360686626406217781)
              ·
                refine ⟨1599779940064371225582917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17064319360686626406217781 1599779940064371225582917)
                ·
                  refine ⟨299958738762069604796797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599779940064371225582917 299958738762069604796797)
                  ·
                    rfl

theorem cell22_2628754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_2628754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628754 prefixEnd_2628754 := by exact prefixLift 2628754
  have htrace : WordTrace (prefixWord ++ tailWord_2628754) baseStart_2628754 baseEnd_2628754 := by
    simpa [prefixWord, tailWord_2628754, baseEnd_2628754] using wordTrace_append hprefix tailTrace_2628754
  have hstable : (prefixWord ++ tailWord_2628754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628754).length < 2 ^ (prefixWord ++ tailWord_2628754).sum := by decide
  have hdescent : baseEnd_2628754 < baseStart_2628754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628765 : List Nat := [1, 4, 2, 1, 1, 2, 11]
def baseStart_2628765 : Nat := 118140960795 + 2628765 * 2 ^ 59
def prefixEnd_2628765 : Nat := 4983230072969 + 3 ^ 40 * 2628765 * 2
def baseEnd_2628765 : Nat := 33328888215222535272791

theorem tailTrace_2628765 : CollatzResearch.WordTrace tailWord_2628765 prefixEnd_2628765 33328888215222535272791 := by
  unfold tailWord_2628765
  simp only [CollatzResearch.WordTrace]
  refine ⟨95878936321440837163791749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63919290880960558109194499 95878936321440837163791749)
  ·
    refine ⟨17977300560270156968210953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95878936321440837163791749 17977300560270156968210953)
    ·
      refine ⟨13482975420202617726158215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17977300560270156968210953 13482975420202617726158215)
      ·
        refine ⟨20224463130303926589237323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13482975420202617726158215 20224463130303926589237323)
        ·
          refine ⟨30336694695455889883855985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20224463130303926589237323 30336694695455889883855985)
          ·
            refine ⟨22752521021591917412891989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30336694695455889883855985 22752521021591917412891989)
            ·
              refine ⟨33328888215222535272791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22752521021591917412891989 33328888215222535272791)
              ·
                rfl

theorem cell22_2628765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 11].length) (baseStart_2628765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628765 prefixEnd_2628765 := by exact prefixLift 2628765
  have htrace : WordTrace (prefixWord ++ tailWord_2628765) baseStart_2628765 baseEnd_2628765 := by
    simpa [prefixWord, tailWord_2628765, baseEnd_2628765] using wordTrace_append hprefix tailTrace_2628765
  have hstable : (prefixWord ++ tailWord_2628765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628765).length < 2 ^ (prefixWord ++ tailWord_2628765).sum := by decide
  have hdescent : baseEnd_2628765 < baseStart_2628765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628786 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_2628786 : Nat := 118140960795 + 2628786 * 2 ^ 59
def prefixEnd_2628786 : Nat := 4983230072969 + 3 ^ 40 * 2628786 * 2
def baseEnd_2628786 : Nat := 899887170540171397590293

theorem tailTrace_2628786 : CollatzResearch.WordTrace tailWord_2628786 prefixEnd_2628786 899887170540171397590293 := by
  unfold tailWord_2628786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969925563591189437576553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63919801502909838500204141 23969925563591189437576553)
  ·
    refine ⟨17977444172693392078182415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23969925563591189437576553 17977444172693392078182415)
    ·
      refine ⟨26966166259040088117273623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17977444172693392078182415 26966166259040088117273623)
      ·
        refine ⟨40449249388560132175910435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26966166259040088117273623 40449249388560132175910435)
        ·
          refine ⟨60673874082840198263865653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40449249388560132175910435 60673874082840198263865653)
          ·
            refine ⟨5688175695266268587237405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60673874082840198263865653 5688175695266268587237405)
            ·
              refine ⟨2133065885724850720214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5688175695266268587237405 2133065885724850720214027)
              ·
                refine ⟨3199598828587276080321041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133065885724850720214027 3199598828587276080321041)
                ·
                  refine ⟨2399699121440457060240781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199598828587276080321041 2399699121440457060240781)
                  ·
                    refine ⟨899887170540171397590293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399699121440457060240781 899887170540171397590293)
                    ·
                      rfl

theorem cell22_2628786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_2628786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628786 prefixEnd_2628786 := by exact prefixLift 2628786
  have htrace : WordTrace (prefixWord ++ tailWord_2628786) baseStart_2628786 baseEnd_2628786 := by
    simpa [prefixWord, tailWord_2628786, baseEnd_2628786] using wordTrace_append hprefix tailTrace_2628786
  have hstable : (prefixWord ++ tailWord_2628786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628786).length < 2 ^ (prefixWord ++ tailWord_2628786).sum := by decide
  have hdescent : baseEnd_2628786 < baseStart_2628786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628844 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_2628844 : Nat := 118140960795 + 2628844 * 2 ^ 59
def prefixEnd_2628844 : Nat := 4983230072969 + 3 ^ 40 * 2628844 * 2
def baseEnd_2628844 : Nat := 299969008375159526546705

theorem tailTrace_2628844 : CollatzResearch.WordTrace tailWord_2628844 prefixEnd_2628844 299969008375159526546705 := by
  unfold tailWord_2628844
  simp only [CollatzResearch.WordTrace]
  refine ⟨47940908844077316827958793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63921211792103089103945057 47940908844077316827958793)
  ·
    refine ⟨35955681633057987620969095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47940908844077316827958793 35955681633057987620969095)
    ·
      refine ⟨53933522449586981431453643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35955681633057987620969095 53933522449586981431453643)
      ·
        refine ⟨80900283674380472147180465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53933522449586981431453643 80900283674380472147180465)
        ·
          refine ⟨60675212755785354110385349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80900283674380472147180465 60675212755785354110385349)
          ·
            refine ⟨11376602391709753895697253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60675212755785354110385349 11376602391709753895697253)
            ·
              refine ⟨2133112948445578855443235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11376602391709753895697253 2133112948445578855443235)
              ·
                refine ⟨3199669422668368283164853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133112948445578855443235 3199669422668368283164853)
                ·
                  refine ⟨299969008375159526546705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3199669422668368283164853 299969008375159526546705)
                  ·
                    rfl

theorem cell22_2628844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_2628844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628844 prefixEnd_2628844 := by exact prefixLift 2628844
  have htrace : WordTrace (prefixWord ++ tailWord_2628844) baseStart_2628844 baseEnd_2628844 := by
    simpa [prefixWord, tailWord_2628844, baseEnd_2628844] using wordTrace_append hprefix tailTrace_2628844
  have hstable : (prefixWord ++ tailWord_2628844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628844).length < 2 ^ (prefixWord ++ tailWord_2628844).sum := by decide
  have hdescent : baseEnd_2628844 < baseStart_2628844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628857 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_2628857 : Nat := 118140960795 + 2628857 * 2 ^ 59
def prefixEnd_2628857 : Nat := 4983230072969 + 3 ^ 40 * 2628857 * 2
def baseEnd_2628857 : Nat := 899911475291150879065075

theorem tailTrace_2628857 : CollatzResearch.WordTrace tailWord_2628857 prefixEnd_2628857 899911475291150879065075 := by
  unfold tailWord_2628857
  simp only [CollatzResearch.WordTrace]
  refine ⟨95882291837107536876140825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63921527891405024584093883 95882291837107536876140825)
  ·
    refine ⟨71911718877830652657105619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95882291837107536876140825 71911718877830652657105619)
    ·
      refine ⟨107867578316745978985658429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71911718877830652657105619 107867578316745978985658429)
      ·
        refine ⟨40450341868779742119621911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107867578316745978985658429 40450341868779742119621911)
        ·
          refine ⟨60675512803169613179432867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40450341868779742119621911 60675512803169613179432867)
          ·
            refine ⟨91013269204754419769149301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60675512803169613179432867 91013269204754419769149301)
            ·
              refine ⟨8532493987945726853357747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91013269204754419769149301 8532493987945726853357747)
              ·
                refine ⟨12798740981918590280036621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8532493987945726853357747 12798740981918590280036621)
                ·
                  refine ⟨4799527868219471355013733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12798740981918590280036621 4799527868219471355013733)
                  ·
                    refine ⟨899911475291150879065075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799527868219471355013733 899911475291150879065075)
                    ·
                      rfl

theorem cell22_2628857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_2628857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628857 prefixEnd_2628857 := by exact prefixLift 2628857
  have htrace : WordTrace (prefixWord ++ tailWord_2628857) baseStart_2628857 baseEnd_2628857 := by
    simpa [prefixWord, tailWord_2628857, baseEnd_2628857] using wordTrace_append hprefix tailTrace_2628857
  have hstable : (prefixWord ++ tailWord_2628857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628857).length < 2 ^ (prefixWord ++ tailWord_2628857).sum := by decide
  have hdescent : baseEnd_2628857 < baseStart_2628857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628887 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2628887 : Nat := 118140960795 + 2628887 * 2 ^ 59
def prefixEnd_2628887 : Nat := 4983230072969 + 3 ^ 40 * 2628887 * 2
def baseEnd_2628887 : Nat := 899921744904240800814983

theorem tailTrace_2628887 : CollatzResearch.WordTrace tailWord_2628887 prefixEnd_2628887 899921744904240800814983 := by
  unfold tailWord_2628887
  simp only [CollatzResearch.WordTrace]
  refine ⟨95883386026998851999732915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63922257351332567999821943 95883386026998851999732915)
  ·
    refine ⟨143825079040498277999599373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95883386026998851999732915 143825079040498277999599373)
    ·
      refine ⟨53934404640186854249849765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143825079040498277999599373 53934404640186854249849765)
      ·
        refine ⟨10112700870035035171846831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53934404640186854249849765 10112700870035035171846831)
        ·
          refine ⟨15169051305052552757770247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10112700870035035171846831 15169051305052552757770247)
          ·
            refine ⟨22753576957578829136655371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15169051305052552757770247 22753576957578829136655371)
            ·
              refine ⟨34130365436368243704983057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22753576957578829136655371 34130365436368243704983057)
              ·
                refine ⟨25597774077276182778737293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34130365436368243704983057 25597774077276182778737293)
                ·
                  refine ⟨9599165278978568542026485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25597774077276182778737293 9599165278978568542026485)
                  ·
                    refine ⟨899921744904240800814983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9599165278978568542026485 899921744904240800814983)
                    ·
                      rfl

theorem cell22_2628887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2628887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628887 prefixEnd_2628887 := by exact prefixLift 2628887
  have htrace : WordTrace (prefixWord ++ tailWord_2628887) baseStart_2628887 baseEnd_2628887 := by
    simpa [prefixWord, tailWord_2628887, baseEnd_2628887] using wordTrace_append hprefix tailTrace_2628887
  have hstable : (prefixWord ++ tailWord_2628887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628887).length < 2 ^ (prefixWord ++ tailWord_2628887).sum := by decide
  have hdescent : baseEnd_2628887 < baseStart_2628887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628904 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2628904 : Nat := 118140960795 + 2628904 * 2 ^ 59
def prefixEnd_2628904 : Nat := 4983230072969 + 3 ^ 40 * 2628904 * 2
def baseEnd_2628904 : Nat := 899927564351658423139931

theorem tailTrace_2628904 : CollatzResearch.WordTrace tailWord_2628904 prefixEnd_2628904 899927564351658423139931 := by
  unfold tailWord_2628904
  simp only [CollatzResearch.WordTrace]
  refine ⟨47942003033968631951550883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63922670711958175935401177 47942003033968631951550883)
  ·
    refine ⟨71913004550952947927326325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47942003033968631951550883 71913004550952947927326325)
    ·
      refine ⟨6741844176651838868186843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71913004550952947927326325 6741844176651838868186843)
      ·
        refine ⟨10112766264977758302280265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6741844176651838868186843 10112766264977758302280265)
        ·
          refine ⟨7584574698733318726710199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10112766264977758302280265 7584574698733318726710199)
          ·
            refine ⟨11376862048099978090065299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584574698733318726710199 11376862048099978090065299)
            ·
              refine ⟨17065293072149967135097949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11376862048099978090065299 17065293072149967135097949)
              ·
                refine ⟨6399484902056237675661731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17065293072149967135097949 6399484902056237675661731)
                ·
                  refine ⟨9599227353084356513492597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6399484902056237675661731 9599227353084356513492597)
                  ·
                    refine ⟨899927564351658423139931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9599227353084356513492597 899927564351658423139931)
                    ·
                      rfl

theorem cell22_2628904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2628904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628904 prefixEnd_2628904 := by exact prefixLift 2628904
  have htrace : WordTrace (prefixWord ++ tailWord_2628904) baseStart_2628904 baseEnd_2628904 := by
    simpa [prefixWord, tailWord_2628904, baseEnd_2628904] using wordTrace_append hprefix tailTrace_2628904
  have hstable : (prefixWord ++ tailWord_2628904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628904).length < 2 ^ (prefixWord ++ tailWord_2628904).sum := by decide
  have hdescent : baseEnd_2628904 < baseStart_2628904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628925 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_2628925 : Nat := 118140960795 + 2628925 * 2 ^ 59
def prefixEnd_2628925 : Nat := 4983230072969 + 3 ^ 40 * 2628925 * 2
def baseEnd_2628925 : Nat := 899934753080821368364867

theorem tailTrace_2628925 : CollatzResearch.WordTrace tailWord_2628925 prefixEnd_2628925 899934753080821368364867 := by
  unfold tailWord_2628925
  simp only [CollatzResearch.WordTrace]
  refine ⟨95884772000861184489616229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63923181333907456326410819 95884772000861184489616229)
  ·
    refine ⟨17978394750161472091803043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95884772000861184489616229 17978394750161472091803043)
    ·
      refine ⟨26967592125242208137704565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17978394750161472091803043 26967592125242208137704565)
      ·
        refine ⟨2528211761741457012909803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26967592125242208137704565 2528211761741457012909803)
        ·
          refine ⟨3792317642612185519364705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528211761741457012909803 3792317642612185519364705)
          ·
            refine ⟨2844238231959139139523529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792317642612185519364705 2844238231959139139523529)
            ·
              refine ⟨2133178673969354354642647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844238231959139139523529 2133178673969354354642647)
              ·
                refine ⟨3199768010954031531963971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133178673969354354642647 3199768010954031531963971)
                ·
                  refine ⟨4799652016431047297945957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199768010954031531963971 4799652016431047297945957)
                  ·
                    refine ⟨899934753080821368364867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799652016431047297945957 899934753080821368364867)
                    ·
                      rfl

theorem cell22_2628925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_2628925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628925 prefixEnd_2628925 := by exact prefixLift 2628925
  have htrace : WordTrace (prefixWord ++ tailWord_2628925) baseStart_2628925 baseEnd_2628925 := by
    simpa [prefixWord, tailWord_2628925, baseEnd_2628925] using wordTrace_append hprefix tailTrace_2628925
  have hstable : (prefixWord ++ tailWord_2628925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628925).length < 2 ^ (prefixWord ++ tailWord_2628925).sum := by decide
  have hdescent : baseEnd_2628925 < baseStart_2628925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628968 : List Nat := [2, 1, 4, 2, 4, 1, 2, 6]
def baseStart_2628968 : Nat := 118140960795 + 2628968 * 2 ^ 59
def prefixEnd_2628968 : Nat := 4983230072969 + 3 ^ 40 * 2628968 * 2
def baseEnd_2628968 : Nat := 99994385873287065504415

theorem tailTrace_2628968 : CollatzResearch.WordTrace tailWord_2628968 prefixEnd_2628968 99994385873287065504415 := by
  unfold tailWord_2628968
  simp only [CollatzResearch.WordTrace]
  refine ⟨47943170169852701416715779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63924226893136935222287705 47943170169852701416715779)
  ·
    refine ⟨71914755254779052125073669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47943170169852701416715779 71914755254779052125073669)
    ·
      refine ⟨13484016610271072273451313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71914755254779052125073669 13484016610271072273451313)
      ·
        refine ⟨10113012457703304205088485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13484016610271072273451313 10113012457703304205088485)
        ·
          refine ⟨1896189835819369538454091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10113012457703304205088485 1896189835819369538454091)
          ·
            refine ⟨2844284753729054307681137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896189835819369538454091 2844284753729054307681137)
            ·
              refine ⟨2133213565296790730760853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844284753729054307681137 2133213565296790730760853)
              ·
                refine ⟨99994385873287065504415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2133213565296790730760853 99994385873287065504415)
                ·
                  rfl

theorem cell22_2628968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_2628968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628968 prefixEnd_2628968 := by exact prefixLift 2628968
  have htrace : WordTrace (prefixWord ++ tailWord_2628968) baseStart_2628968 baseEnd_2628968 := by
    simpa [prefixWord, tailWord_2628968, baseEnd_2628968] using wordTrace_append hprefix tailTrace_2628968
  have hstable : (prefixWord ++ tailWord_2628968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628968).length < 2 ^ (prefixWord ++ tailWord_2628968).sum := by decide
  have hdescent : baseEnd_2628968 < baseStart_2628968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628977 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2628977 : Nat := 118140960795 + 2628977 * 2 ^ 59
def prefixEnd_2628977 : Nat := 4983230072969 + 3 ^ 40 * 2628977 * 2
def baseEnd_2628977 : Nat := 899952553743510566064707

theorem tailTrace_2628977 : CollatzResearch.WordTrace tailWord_2628977 prefixEnd_2628977 899952553743510566064707 := by
  unfold tailWord_2628977
  simp only [CollatzResearch.WordTrace]
  refine ⟨95886668596672797370509185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63924445731115198247006123 95886668596672797370509185)
  ·
    refine ⟨71915001447504598027881889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95886668596672797370509185 71915001447504598027881889)
    ·
      refine ⟨53936251085628448520911417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71915001447504598027881889 53936251085628448520911417)
      ·
        refine ⟨40452188314221336390683563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53936251085628448520911417 40452188314221336390683563)
        ·
          refine ⟨60678282471332004586025345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40452188314221336390683563 60678282471332004586025345)
          ·
            refine ⟨45508711853499003439519009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60678282471332004586025345 45508711853499003439519009)
            ·
              refine ⟨34131533890124252579639257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45508711853499003439519009 34131533890124252579639257)
              ·
                refine ⟨25598650417593189434729443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34131533890124252579639257 25598650417593189434729443)
                ·
                  refine ⟨38397975626389784152094165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25598650417593189434729443 38397975626389784152094165)
                  ·
                    refine ⟨899952553743510566064707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38397975626389784152094165 899952553743510566064707)
                    ·
                      rfl

theorem cell22_2628977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2628977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2628977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2628977 prefixEnd_2628977 := by exact prefixLift 2628977
  have htrace : WordTrace (prefixWord ++ tailWord_2628977) baseStart_2628977 baseEnd_2628977 := by
    simpa [prefixWord, tailWord_2628977, baseEnd_2628977] using wordTrace_append hprefix tailTrace_2628977
  have hstable : (prefixWord ++ tailWord_2628977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628977).length < 2 ^ (prefixWord ++ tailWord_2628977).sum := by decide
  have hdescent : baseEnd_2628977 < baseStart_2628977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629000 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 1, 3]
def baseStart_2629000 : Nat := 118140960795 + 2629000 * 2 ^ 59
def prefixEnd_2629000 : Nat := 4983230072969 + 3 ^ 40 * 2629000 * 2
def baseEnd_2629000 : Nat := 899960427113546172739637

theorem tailTrace_2629000 : CollatzResearch.WordTrace tailWord_2629000 prefixEnd_2629000 899960427113546172739637 := by
  unfold tailWord_2629000
  simp only [CollatzResearch.WordTrace]
  refine ⟨47943753737794736149298227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63925004983726314865730969 47943753737794736149298227)
  ·
    refine ⟨71915630606692104223947341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47943753737794736149298227 71915630606692104223947341)
    ·
      refine ⟨26968361477509539083980253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71915630606692104223947341 26968361477509539083980253)
      ·
        refine ⟨10113135554066077156492595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26968361477509539083980253 10113135554066077156492595)
        ·
          refine ⟨15169703331099115734738893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10113135554066077156492595 15169703331099115734738893)
          ·
            refine ⟨5688638749162168400527085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15169703331099115734738893 5688638749162168400527085)
            ·
              refine ⟨2133239530935813150197657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5688638749162168400527085 2133239530935813150197657)
              ·
                refine ⟨1599929648201859862648243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133239530935813150197657 1599929648201859862648243)
                ·
                  refine ⟨2399894472302789793972365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599929648201859862648243 2399894472302789793972365)
                  ·
                    refine ⟨899960427113546172739637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399894472302789793972365 899960427113546172739637)
                    ·
                      rfl

theorem cell22_2629000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_2629000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629000 prefixEnd_2629000 := by exact prefixLift 2629000
  have htrace : WordTrace (prefixWord ++ tailWord_2629000) baseStart_2629000 baseEnd_2629000 := by
    simpa [prefixWord, tailWord_2629000, baseEnd_2629000] using wordTrace_append hprefix tailTrace_2629000
  have hstable : (prefixWord ++ tailWord_2629000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629000).length < 2 ^ (prefixWord ++ tailWord_2629000).sum := by decide
  have hdescent : baseEnd_2629000 < baseStart_2629000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629026 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2629026 : Nat := 118140960795 + 2629026 * 2 ^ 59
def prefixEnd_2629026 : Nat := 4983230072969 + 3 ^ 40 * 2629026 * 2
def baseEnd_2629026 : Nat := 899969327444890771589557

theorem tailTrace_2629026 : CollatzResearch.WordTrace tailWord_2629026 prefixEnd_2629026 899969327444890771589557 := by
  unfold tailWord_2629026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972113943373819684760733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63925637182330185826028621 23972113943373819684760733)
  ·
    refine ⟨8989542728765182381785275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23972113943373819684760733 8989542728765182381785275)
    ·
      refine ⟨13484314093147773572677913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8989542728765182381785275 13484314093147773572677913)
      ·
        refine ⟨10113235569860830179508435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13484314093147773572677913 10113235569860830179508435)
        ·
          refine ⟨15169853354791245269262653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10113235569860830179508435 15169853354791245269262653)
          ·
            refine ⟨5688695008046716975973495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15169853354791245269262653 5688695008046716975973495)
            ·
              refine ⟨8533042512070075463960243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5688695008046716975973495 8533042512070075463960243)
              ·
                refine ⟨12799563768105113195940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533042512070075463960243 12799563768105113195940365)
                ·
                  refine ⟨4799836413039417448477637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12799563768105113195940365 4799836413039417448477637)
                  ·
                    refine ⟨899969327444890771589557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799836413039417448477637 899969327444890771589557)
                    ·
                      rfl

theorem cell22_2629026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2629026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629026 prefixEnd_2629026 := by exact prefixLift 2629026
  have htrace : WordTrace (prefixWord ++ tailWord_2629026) baseStart_2629026 baseEnd_2629026 := by
    simpa [prefixWord, tailWord_2629026, baseEnd_2629026] using wordTrace_append hprefix tailTrace_2629026
  have hstable : (prefixWord ++ tailWord_2629026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629026).length < 2 ^ (prefixWord ++ tailWord_2629026).sum := by decide
  have hdescent : baseEnd_2629026 < baseStart_2629026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629039 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 6, 3]
def baseStart_2629039 : Nat := 118140960795 + 2629039 * 2 ^ 59
def prefixEnd_2629039 : Nat := 4983230072969 + 3 ^ 40 * 2629039 * 2
def baseEnd_2629039 : Nat := 899973777610563071014517

theorem tailTrace_2629039 : CollatzResearch.WordTrace tailWord_2629039 prefixEnd_2629039 899973777610563071014517 := by
  unfold tailWord_2629039
  simp only [CollatzResearch.WordTrace]
  refine ⟨95888929922448181959266171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63925953281632121306177447 95888929922448181959266171)
  ·
    refine ⟨143833394883672272938899257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95888929922448181959266171 143833394883672272938899257)
    ·
      refine ⟨107875046162754204704174443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143833394883672272938899257 107875046162754204704174443)
      ·
        refine ⟨161812569244131307056261665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107875046162754204704174443 161812569244131307056261665)
        ·
          refine ⟨121359426933098480292196249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161812569244131307056261665 121359426933098480292196249)
          ·
            refine ⟨91019570199823860219147187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121359426933098480292196249 91019570199823860219147187)
            ·
              refine ⟨136529355299735790328720781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91019570199823860219147187 136529355299735790328720781)
              ·
                refine ⟨51198508237400921373270293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136529355299735790328720781 51198508237400921373270293)
                ·
                  refine ⟨2399930073628168189372045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51198508237400921373270293 2399930073628168189372045)
                  ·
                    refine ⟨899973777610563071014517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399930073628168189372045 899973777610563071014517)
                    ·
                      rfl

theorem cell22_2629039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_2629039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629039 prefixEnd_2629039 := by exact prefixLift 2629039
  have htrace : WordTrace (prefixWord ++ tailWord_2629039) baseStart_2629039 baseEnd_2629039 := by
    simpa [prefixWord, tailWord_2629039, baseEnd_2629039] using wordTrace_append hprefix tailTrace_2629039
  have hstable : (prefixWord ++ tailWord_2629039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629039).length < 2 ^ (prefixWord ++ tailWord_2629039).sum := by decide
  have hdescent : baseEnd_2629039 < baseStart_2629039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629041 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 4]
def baseStart_2629041 : Nat := 118140960795 + 2629041 * 2 ^ 59
def prefixEnd_2629041 : Nat := 4983230072969 + 3 ^ 40 * 2629041 * 2
def baseEnd_2629041 : Nat := 299991487417145244154837

theorem tailTrace_2629041 : CollatzResearch.WordTrace tailWord_2629041 prefixEnd_2629041 299991487417145244154837 := by
  unfold tailWord_2629041
  simp only [CollatzResearch.WordTrace]
  refine ⟨95889002868440936300838977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63926001912293957533892651 95889002868440936300838977)
  ·
    refine ⟨71916752151330702225629233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95889002868440936300838977 71916752151330702225629233)
    ·
      refine ⟨53937564113498026669221925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71916752151330702225629233 53937564113498026669221925)
      ·
        refine ⟨10113293271280880000479111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53937564113498026669221925 10113293271280880000479111)
        ·
          refine ⟨15169939906921320000718667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10113293271280880000479111 15169939906921320000718667)
          ·
            refine ⟨22754909860381980001078001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15169939906921320000718667 22754909860381980001078001)
            ·
              refine ⟨17066182395286485000808501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22754909860381980001078001 17066182395286485000808501)
              ·
                refine ⟨1599954599558107968825797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17066182395286485000808501 1599954599558107968825797)
                ·
                  refine ⟨299991487417145244154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599954599558107968825797 299991487417145244154837)
                  ·
                    rfl

theorem cell22_2629041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_2629041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629041 prefixEnd_2629041 := by exact prefixLift 2629041
  have htrace : WordTrace (prefixWord ++ tailWord_2629041) baseStart_2629041 baseEnd_2629041 := by
    simpa [prefixWord, tailWord_2629041, baseEnd_2629041] using wordTrace_append hprefix tailTrace_2629041
  have hstable : (prefixWord ++ tailWord_2629041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629041).length < 2 ^ (prefixWord ++ tailWord_2629041).sum := by decide
  have hdescent : baseEnd_2629041 < baseStart_2629041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629054 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2629054 : Nat := 118140960795 + 2629054 * 2 ^ 59
def prefixEnd_2629054 : Nat := 4983230072969 + 3 ^ 40 * 2629054 * 2
def baseEnd_2629054 : Nat := 899978912417108031889471

theorem tailTrace_2629054 : CollatzResearch.WordTrace tailWord_2629054 prefixEnd_2629054 899978912417108031889471 := by
  unfold tailWord_2629054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11986184627174229940132777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63926318011595893014041477 11986184627174229940132777)
  ·
    refine ⟨8989638470380672455099583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11986184627174229940132777 8989638470380672455099583)
    ·
      refine ⟨13484457705571008682649375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8989638470380672455099583 13484457705571008682649375)
      ·
        refine ⟨20226686558356513023974063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13484457705571008682649375 20226686558356513023974063)
        ·
          refine ⟨30340029837534769535961095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20226686558356513023974063 30340029837534769535961095)
          ·
            refine ⟨45510044756302154303941643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30340029837534769535961095 45510044756302154303941643)
            ·
              refine ⟨68265067134453231455912465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45510044756302154303941643 68265067134453231455912465)
              ·
                refine ⟨51198800350839923591934349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68265067134453231455912465 51198800350839923591934349)
                ·
                  refine ⟨19199550131564971346975381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51198800350839923591934349 19199550131564971346975381)
                  ·
                    refine ⟨899978912417108031889471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19199550131564971346975381 899978912417108031889471)
                    ·
                      rfl

theorem cell22_2629054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2629054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629054 prefixEnd_2629054 := by exact prefixLift 2629054
  have htrace : WordTrace (prefixWord ++ tailWord_2629054) baseStart_2629054 baseEnd_2629054 := by
    simpa [prefixWord, tailWord_2629054, baseEnd_2629054] using wordTrace_append hprefix tailTrace_2629054
  have hstable : (prefixWord ++ tailWord_2629054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629054).length < 2 ^ (prefixWord ++ tailWord_2629054).sum := by decide
  have hdescent : baseEnd_2629054 < baseStart_2629054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629056 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_2629056 : Nat := 118140960795 + 2629056 * 2 ^ 59
def prefixEnd_2629056 : Nat := 4983230072969 + 3 ^ 40 * 2629056 * 2
def baseEnd_2629056 : Nat := 899979597057980693339465

theorem tailTrace_2629056 : CollatzResearch.WordTrace tailWord_2629056 prefixEnd_2629056 899979597057980693339465 := by
  unfold tailWord_2629056
  simp only [CollatzResearch.WordTrace]
  refine ⟨47944774981693296931317511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63926366642257729241756681 47944774981693296931317511)
  ·
    refine ⟨71917162472539945396976267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47944774981693296931317511 71917162472539945396976267)
    ·
      refine ⟨107875743708809918095464401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71917162472539945396976267 107875743708809918095464401)
      ·
        refine ⟨80906807781607438571598301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107875743708809918095464401 80906807781607438571598301)
        ·
          refine ⟨30340052918102789464349363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80906807781607438571598301 30340052918102789464349363)
          ·
            refine ⟨45510079377154184196524045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30340052918102789464349363 45510079377154184196524045)
            ·
              refine ⟨17066279766432819073696517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45510079377154184196524045 17066279766432819073696517)
              ·
                refine ⟨3199927456206153576318097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17066279766432819073696517 3199927456206153576318097)
                ·
                  refine ⟨2399945592154615182238573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199927456206153576318097 2399945592154615182238573)
                  ·
                    refine ⟨899979597057980693339465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399945592154615182238573 899979597057980693339465)
                    ·
                      rfl

theorem cell22_2629056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_2629056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629056 prefixEnd_2629056 := by exact prefixLift 2629056
  have htrace : WordTrace (prefixWord ++ tailWord_2629056) baseStart_2629056 baseEnd_2629056 := by
    simpa [prefixWord, tailWord_2629056, baseEnd_2629056] using wordTrace_append hprefix tailTrace_2629056
  have hstable : (prefixWord ++ tailWord_2629056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629056).length < 2 ^ (prefixWord ++ tailWord_2629056).sum := by decide
  have hdescent : baseEnd_2629056 < baseStart_2629056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629114 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_2629114 : Nat := 118140960795 + 2629114 * 2 ^ 59
def prefixEnd_2629114 : Nat := 4983230072969 + 3 ^ 40 * 2629114 * 2
def baseEnd_2629114 : Nat := 299999817214429291796429

theorem tailTrace_2629114 : CollatzResearch.WordTrace tailWord_2629114 prefixEnd_2629114 299999817214429291796429 := by
  unfold tailWord_2629114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972916349294117442061599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63927776931450979845497597 23972916349294117442061599)
  ·
    refine ⟨35959374523941176163092399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23972916349294117442061599 35959374523941176163092399)
    ·
      refine ⟨53939061785911764244638599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35959374523941176163092399 53939061785911764244638599)
      ·
        refine ⟨80908592678867646366957899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53939061785911764244638599 80908592678867646366957899)
        ·
          refine ⟨121362889018301469550436849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80908592678867646366957899 121362889018301469550436849)
          ·
            refine ⟨91022166763726102162827637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121362889018301469550436849 91022166763726102162827637)
            ·
              refine ⟨8533328134099322077765091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91022166763726102162827637 8533328134099322077765091)
              ·
                refine ⟨12799992201148983116647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533328134099322077765091 12799992201148983116647637)
                ·
                  refine ⟨299999817214429291796429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12799992201148983116647637 299999817214429291796429)
                  ·
                    rfl

theorem cell22_2629114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_2629114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629114 prefixEnd_2629114 := by exact prefixLift 2629114
  have htrace : WordTrace (prefixWord ++ tailWord_2629114) baseStart_2629114 baseEnd_2629114 := by
    simpa [prefixWord, tailWord_2629114, baseEnd_2629114] using wordTrace_append hprefix tailTrace_2629114
  have hstable : (prefixWord ++ tailWord_2629114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629114).length < 2 ^ (prefixWord ++ tailWord_2629114).sum := by decide
  have hdescent : baseEnd_2629114 < baseStart_2629114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629129 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_2629129 : Nat := 118140960795 + 2629129 * 2 ^ 59
def prefixEnd_2629129 : Nat := 4983230072969 + 3 ^ 40 * 2629129 * 2
def baseEnd_2629129 : Nat := 900004586449832836264241

theorem tailTrace_2629129 : CollatzResearch.WordTrace tailWord_2629129 prefixEnd_2629129 900004586449832836264241 := by
  unfold tailWord_2629129
  simp only [CollatzResearch.WordTrace]
  refine ⟨95892212492122127330042441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63928141661414751553361627 95892212492122127330042441)
  ·
    refine ⟨71919159369091595497531831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95892212492122127330042441 71919159369091595497531831)
    ·
      refine ⟨107878739053637393246297747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71919159369091595497531831 107878739053637393246297747)
      ·
        refine ⟨161818108580456089869446621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107878739053637393246297747 161818108580456089869446621)
        ·
          refine ⟨60681790717671033701042483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161818108580456089869446621 60681790717671033701042483)
          ·
            refine ⟨91022686076506550551563725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60681790717671033701042483 91022686076506550551563725)
            ·
              refine ⟨34133507278689956456836397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91022686076506550551563725 34133507278689956456836397)
              ·
                refine ⟨12800065229508733671313649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34133507278689956456836397 12800065229508733671313649)
                ·
                  refine ⟨9600048922131550253485237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12800065229508733671313649 9600048922131550253485237)
                  ·
                    refine ⟨900004586449832836264241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9600048922131550253485237 900004586449832836264241)
                    ·
                      rfl

theorem cell22_2629129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_2629129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629129 prefixEnd_2629129 := by exact prefixLift 2629129
  have htrace : WordTrace (prefixWord ++ tailWord_2629129) baseStart_2629129 baseEnd_2629129 := by
    simpa [prefixWord, tailWord_2629129, baseEnd_2629129] using wordTrace_append hprefix tailTrace_2629129
  have hstable : (prefixWord ++ tailWord_2629129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629129).length < 2 ^ (prefixWord ++ tailWord_2629129).sum := by decide
  have hdescent : baseEnd_2629129 < baseStart_2629129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629152 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 1, 3]
def baseStart_2629152 : Nat := 118140960795 + 2629152 * 2 ^ 59
def prefixEnd_2629152 : Nat := 4983230072969 + 3 ^ 40 * 2629152 * 2
def baseEnd_2629152 : Nat := 900012459819868442939171

theorem tailTrace_2629152 : CollatzResearch.WordTrace tailWord_2629152 prefixEnd_2629152 900012459819868442939171 := by
  unfold tailWord_2629152
  simp only [CollatzResearch.WordTrace]
  refine ⟨47946525685519401129064855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63928700914025868172086473 47946525685519401129064855)
  ·
    refine ⟨71919788528279101693597283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47946525685519401129064855 71919788528279101693597283)
    ·
      refine ⟨107879682792418652540395925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71919788528279101693597283 107879682792418652540395925)
      ·
        refine ⟨5056860130894624337831059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107879682792418652540395925 5056860130894624337831059)
        ·
          refine ⟨7585290196341936506746589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056860130894624337831059 7585290196341936506746589)
          ·
            refine ⟨2844483823628226190029971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7585290196341936506746589 2844483823628226190029971)
            ·
              refine ⟨4266725735442339285044957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844483823628226190029971 4266725735442339285044957)
              ·
                refine ⟨1600022150790877231891859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4266725735442339285044957 1600022150790877231891859)
                ·
                  refine ⟨2400033226186315847837789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600022150790877231891859 2400033226186315847837789)
                  ·
                    refine ⟨900012459819868442939171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400033226186315847837789 900012459819868442939171)
                    ·
                      rfl

theorem cell22_2629152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_2629152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629152 prefixEnd_2629152 := by exact prefixLift 2629152
  have htrace : WordTrace (prefixWord ++ tailWord_2629152) baseStart_2629152 baseEnd_2629152 := by
    simpa [prefixWord, tailWord_2629152, baseEnd_2629152] using wordTrace_append hprefix tailTrace_2629152
  have hstable : (prefixWord ++ tailWord_2629152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629152).length < 2 ^ (prefixWord ++ tailWord_2629152).sum := by decide
  have hdescent : baseEnd_2629152 < baseStart_2629152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629176 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_2629176 : Nat := 118140960795 + 2629176 * 2 ^ 59
def prefixEnd_2629176 : Nat := 4983230072969 + 3 ^ 40 * 2629176 * 2
def baseEnd_2629176 : Nat := 300006891836780126779699

theorem tailTrace_2629176 : CollatzResearch.WordTrace tailWord_2629176 prefixEnd_2629176 300006891836780126779699 := by
  unfold tailWord_2629176
  simp only [CollatzResearch.WordTrace]
  refine ⟨47946963361475927178501691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63929284481967902904668921 47946963361475927178501691)
  ·
    refine ⟨71920445042213890767752537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47946963361475927178501691 71920445042213890767752537)
    ·
      refine ⟨53940333781660418075814403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71920445042213890767752537 53940333781660418075814403)
      ·
        refine ⟨80910500672490627113721605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53940333781660418075814403 80910500672490627113721605)
        ·
          refine ⟨15170718876091992583822801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80910500672490627113721605 15170718876091992583822801)
          ·
            refine ⟨11378039157068994437867101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15170718876091992583822801 11378039157068994437867101)
            ·
              refine ⟨4266764683900872914200163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11378039157068994437867101 4266764683900872914200163)
              ·
                refine ⟨6400147025851309371300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266764683900872914200163 6400147025851309371300245)
                ·
                  refine ⟨300006891836780126779699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6400147025851309371300245 300006891836780126779699)
                  ·
                    rfl

theorem cell22_2629176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_2629176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629176 prefixEnd_2629176 := by exact prefixLift 2629176
  have htrace : WordTrace (prefixWord ++ tailWord_2629176) baseStart_2629176 baseEnd_2629176 := by
    simpa [prefixWord, tailWord_2629176, baseEnd_2629176] using wordTrace_append hprefix tailTrace_2629176
  have hstable : (prefixWord ++ tailWord_2629176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629176).length < 2 ^ (prefixWord ++ tailWord_2629176).sum := by decide
  have hdescent : baseEnd_2629176 < baseStart_2629176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629238 : List Nat := [5, 1, 1, 2, 2, 1, 3, 7]
def baseStart_2629238 : Nat := 118140960795 + 2629238 * 2 ^ 59
def prefixEnd_2629238 : Nat := 4983230072969 + 3 ^ 40 * 2629238 * 2
def baseEnd_2629238 : Nat := 100004655486376987254323

theorem tailTrace_2629238 : CollatzResearch.WordTrace tailWord_2629238 prefixEnd_2629238 100004655486376987254323 := by
  unfold tailWord_2629238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5993511753045452434110023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63930792032484825963840245 5993511753045452434110023)
  ·
    refine ⟨8990267629568178651165035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5993511753045452434110023 8990267629568178651165035)
    ·
      refine ⟨13485401444352267976747553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8990267629568178651165035 13485401444352267976747553)
      ·
        refine ⟨10114051083264200982560665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13485401444352267976747553 10114051083264200982560665)
        ·
          refine ⟨7585538312448150736920499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10114051083264200982560665 7585538312448150736920499)
          ·
            refine ⟨11378307468672226105380749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585538312448150736920499 11378307468672226105380749)
            ·
              refine ⟨4266865300752084789517781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11378307468672226105380749 4266865300752084789517781)
              ·
                refine ⟨100004655486376987254323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4266865300752084789517781 100004655486376987254323)
                ·
                  rfl

theorem cell22_2629238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_2629238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629238 prefixEnd_2629238 := by exact prefixLift 2629238
  have htrace : WordTrace (prefixWord ++ tailWord_2629238) baseStart_2629238 baseEnd_2629238 := by
    simpa [prefixWord, tailWord_2629238, baseEnd_2629238] using wordTrace_append hprefix tailTrace_2629238
  have hstable : (prefixWord ++ tailWord_2629238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629238).length < 2 ^ (prefixWord ++ tailWord_2629238).sum := by decide
  have hdescent : baseEnd_2629238 < baseStart_2629238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629253 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_2629253 : Nat := 118140960795 + 2629253 * 2 ^ 59
def prefixEnd_2629253 : Nat := 4983230072969 + 3 ^ 40 * 2629253 * 2
def baseEnd_2629253 : Nat := 900047034183937846163861

theorem tailTrace_2629253 : CollatzResearch.WordTrace tailWord_2629253 prefixEnd_2629253 900047034183937846163861 := by
  unfold tailWord_2629253
  simp only [CollatzResearch.WordTrace]
  refine ⟨95896735143672896507556413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63931156762448597671704275 95896735143672896507556413)
  ·
    refine ⟨35961275678877336190333655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95896735143672896507556413 35961275678877336190333655)
    ·
      refine ⟨53941913518316004285500483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35961275678877336190333655 53941913518316004285500483)
      ·
        refine ⟨80912870277474006428250725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53941913518316004285500483 80912870277474006428250725)
        ·
          refine ⟨15171163177026376205297011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80912870277474006428250725 15171163177026376205297011)
          ·
            refine ⟨22756744765539564307945517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15171163177026376205297011 22756744765539564307945517)
            ·
              refine ⟨8533779287077336615479569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22756744765539564307945517 8533779287077336615479569)
              ·
                refine ⟨6400334465308002461609677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8533779287077336615479569 6400334465308002461609677)
                ·
                  refine ⟨2400125424490500923103629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6400334465308002461609677 2400125424490500923103629)
                  ·
                    refine ⟨900047034183937846163861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400125424490500923103629 900047034183937846163861)
                    ·
                      rfl

theorem cell22_2629253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_2629253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629253 prefixEnd_2629253 := by exact prefixLift 2629253
  have htrace : WordTrace (prefixWord ++ tailWord_2629253) baseStart_2629253 baseEnd_2629253 := by
    simpa [prefixWord, tailWord_2629253, baseEnd_2629253] using wordTrace_append hprefix tailTrace_2629253
  have hstable : (prefixWord ++ tailWord_2629253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629253).length < 2 ^ (prefixWord ++ tailWord_2629253).sum := by decide
  have hdescent : baseEnd_2629253 < baseStart_2629253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629296 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_2629296 : Nat := 118140960795 + 2629296 * 2 ^ 59
def prefixEnd_2629296 : Nat := 4983230072969 + 3 ^ 40 * 2629296 * 2
def baseEnd_2629296 : Nat := 900061753962700067338729

theorem tailTrace_2629296 : CollatzResearch.WordTrace tailWord_2629296 prefixEnd_2629296 900061753962700067338729 := by
  unfold tailWord_2629296
  simp only [CollatzResearch.WordTrace]
  refine ⟨47949151741258557425685871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63932202321678076567581161 47949151741258557425685871)
  ·
    refine ⟨71923727611887836138528807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47949151741258557425685871 71923727611887836138528807)
    ·
      refine ⟨107885591417831754207793211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71923727611887836138528807 107885591417831754207793211)
      ·
        refine ⟨161828387126747631311689817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107885591417831754207793211 161828387126747631311689817)
        ·
          refine ⟨121371290345060723483767363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161828387126747631311689817 121371290345060723483767363)
          ·
            refine ⟨182056935517591085225651045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121371290345060723483767363 182056935517591085225651045)
            ·
              refine ⟨34135675409548328479809571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182056935517591085225651045 34135675409548328479809571)
              ·
                refine ⟨51203513114322492719714357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34135675409548328479809571 51203513114322492719714357)
                ·
                  refine ⟨4800329354467733692473221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51203513114322492719714357 4800329354467733692473221)
                  ·
                    refine ⟨900061753962700067338729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800329354467733692473221 900061753962700067338729)
                    ·
                      rfl

theorem cell22_2629296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_2629296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629296 prefixEnd_2629296 := by exact prefixLift 2629296
  have htrace : WordTrace (prefixWord ++ tailWord_2629296) baseStart_2629296 baseEnd_2629296 := by
    simpa [prefixWord, tailWord_2629296, baseEnd_2629296] using wordTrace_append hprefix tailTrace_2629296
  have hstable : (prefixWord ++ tailWord_2629296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629296).length < 2 ^ (prefixWord ++ tailWord_2629296).sum := by decide
  have hdescent : baseEnd_2629296 < baseStart_2629296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629311 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 6]
def baseStart_2629311 : Nat := 118140960795 + 2629311 * 2 ^ 59
def prefixEnd_2629311 : Nat := 4983230072969 + 3 ^ 40 * 2629311 * 2
def baseEnd_2629311 : Nat := 300022296256415009404561

theorem tailTrace_2629311 : CollatzResearch.WordTrace tailWord_2629311 prefixEnd_2629311 300022296256415009404561 := by
  unfold tailWord_2629311
  simp only [CollatzResearch.WordTrace]
  refine ⟨95898850577462772413167787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63932567051641848275445191 95898850577462772413167787)
  ·
    refine ⟨143848275866194158619751681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95898850577462772413167787 143848275866194158619751681)
    ·
      refine ⟨107886206899645618964813761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143848275866194158619751681 107886206899645618964813761)
      ·
        refine ⟨80914655174734214223610321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107886206899645618964813761 80914655174734214223610321)
        ·
          refine ⟨60685991381050660667707741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80914655174734214223610321 60685991381050660667707741)
          ·
            refine ⟨22757246767893997750390403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60685991381050660667707741 22757246767893997750390403)
            ·
              refine ⟨34135870151840996625585605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22757246767893997750390403 34135870151840996625585605)
              ·
                refine ⟨6400475653470186867297301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34135870151840996625585605 6400475653470186867297301)
                ·
                  refine ⟨300022296256415009404561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6400475653470186867297301 300022296256415009404561)
                  ·
                    rfl

theorem cell22_2629311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_2629311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629311 prefixEnd_2629311 := by exact prefixLift 2629311
  have htrace : WordTrace (prefixWord ++ tailWord_2629311) baseStart_2629311 baseEnd_2629311 := by
    simpa [prefixWord, tailWord_2629311, baseEnd_2629311] using wordTrace_append hprefix tailTrace_2629311
  have hstable : (prefixWord ++ tailWord_2629311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629311).length < 2 ^ (prefixWord ++ tailWord_2629311).sum := by decide
  have hdescent : baseEnd_2629311 < baseStart_2629311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629328 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_2629328 : Nat := 118140960795 + 2629328 * 2 ^ 59
def prefixEnd_2629328 : Nat := 4983230072969 + 3 ^ 40 * 2629328 * 2
def baseEnd_2629328 : Nat := 300024236072220883512877

theorem tailTrace_2629328 : CollatzResearch.WordTrace tailWord_2629328 prefixEnd_2629328 300024236072220883512877 := by
  unfold tailWord_2629328
  simp only [CollatzResearch.WordTrace]
  refine ⟨47949735309200592158268319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63932980412267456211024425 47949735309200592158268319)
  ·
    refine ⟨71924602963800888237402479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47949735309200592158268319 71924602963800888237402479)
    ·
      refine ⟨107886904445701332356103719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71924602963800888237402479 107886904445701332356103719)
      ·
        refine ⟨161830356668551998534155579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107886904445701332356103719 161830356668551998534155579)
        ·
          refine ⟨242745535002827997801233369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161830356668551998534155579 242745535002827997801233369)
          ·
            refine ⟨182059151252120998350925027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242745535002827997801233369 182059151252120998350925027)
            ·
              refine ⟨273088726878181497526387541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182059151252120998350925027 273088726878181497526387541)
              ·
                refine ⟨1600129259051844712068677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 273088726878181497526387541 1600129259051844712068677)
                ·
                  refine ⟨300024236072220883512877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600129259051844712068677 300024236072220883512877)
                  ·
                    rfl

theorem cell22_2629328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_2629328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629328 prefixEnd_2629328 := by exact prefixLift 2629328
  have htrace : WordTrace (prefixWord ++ tailWord_2629328) baseStart_2629328 baseEnd_2629328 := by
    simpa [prefixWord, tailWord_2629328, baseEnd_2629328] using wordTrace_append hprefix tailTrace_2629328
  have hstable : (prefixWord ++ tailWord_2629328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629328).length < 2 ^ (prefixWord ++ tailWord_2629328).sum := by decide
  have hdescent : baseEnd_2629328 < baseStart_2629328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629330 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2629330 : Nat := 118140960795 + 2629330 * 2 ^ 59
def prefixEnd_2629330 : Nat := 4983230072969 + 3 ^ 40 * 2629330 * 2
def baseEnd_2629330 : Nat := 900073392857535311988625

theorem tailTrace_2629330 : CollatzResearch.WordTrace tailWord_2629330 prefixEnd_2629330 900073392857535311988625 := by
  unfold tailWord_2629330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23974885891098484664527361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63933029042929292438739629 23974885891098484664527361)
  ·
    refine ⟨17981164418323863498395521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23974885891098484664527361 17981164418323863498395521)
    ·
      refine ⟨13485873313742897623796641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17981164418323863498395521 13485873313742897623796641)
      ·
        refine ⟨10114404985307173217847481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13485873313742897623796641 10114404985307173217847481)
        ·
          refine ⟨7585803738980379913385611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10114404985307173217847481 7585803738980379913385611)
          ·
            refine ⟨11378705608470569870078417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585803738980379913385611 11378705608470569870078417)
            ·
              refine ⟨8534029206352927402558813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11378705608470569870078417 8534029206352927402558813)
              ·
                refine ⟨3200260952382347775959555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8534029206352927402558813 3200260952382347775959555)
                ·
                  refine ⟨4800391428573521663939333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200260952382347775959555 4800391428573521663939333)
                  ·
                    refine ⟨900073392857535311988625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800391428573521663939333 900073392857535311988625)
                    ·
                      rfl

theorem cell22_2629330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2629330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629330 prefixEnd_2629330 := by exact prefixLift 2629330
  have htrace : WordTrace (prefixWord ++ tailWord_2629330) baseStart_2629330 baseEnd_2629330 := by
    simpa [prefixWord, tailWord_2629330, baseEnd_2629330] using wordTrace_append hprefix tailTrace_2629330
  have hstable : (prefixWord ++ tailWord_2629330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629330).length < 2 ^ (prefixWord ++ tailWord_2629330).sum := by decide
  have hdescent : baseEnd_2629330 < baseStart_2629330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629343 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 4, 3]
def baseStart_2629343 : Nat := 118140960795 + 2629343 * 2 ^ 59
def prefixEnd_2629343 : Nat := 4983230072969 + 3 ^ 40 * 2629343 * 2
def baseEnd_2629343 : Nat := 900077843023207611413585

theorem tailTrace_2629343 : CollatzResearch.WordTrace tailWord_2629343 prefixEnd_2629343 900077843023207611413585 := by
  unfold tailWord_2629343
  simp only [CollatzResearch.WordTrace]
  refine ⟨95900017713346841878332683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63933345142231227918888455 95900017713346841878332683)
  ·
    refine ⟨143850026570020262817499025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95900017713346841878332683 143850026570020262817499025)
    ·
      refine ⟨107887519927515197113124269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143850026570020262817499025 107887519927515197113124269)
      ·
        refine ⟨40457819972818198917421601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107887519927515197113124269 40457819972818198917421601)
        ·
          refine ⟨30343364979613649188066201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40457819972818198917421601 30343364979613649188066201)
          ·
            refine ⟨22757523734710236891049651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30343364979613649188066201 22757523734710236891049651)
            ·
              refine ⟨34136285602065355336574477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22757523734710236891049651 34136285602065355336574477)
              ·
                refine ⟨12801107100774508251215429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34136285602065355336574477 12801107100774508251215429)
                ·
                  refine ⟨2400207581395220297102893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12801107100774508251215429 2400207581395220297102893)
                  ·
                    refine ⟨900077843023207611413585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400207581395220297102893 900077843023207611413585)
                    ·
                      rfl

theorem cell22_2629343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_2629343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629343 prefixEnd_2629343 := by exact prefixLift 2629343
  have htrace : WordTrace (prefixWord ++ tailWord_2629343) baseStart_2629343 baseEnd_2629343 := by
    simpa [prefixWord, tailWord_2629343, baseEnd_2629343] using wordTrace_append hprefix tailTrace_2629343
  have hstable : (prefixWord ++ tailWord_2629343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629343).length < 2 ^ (prefixWord ++ tailWord_2629343).sum := by decide
  have hdescent : baseEnd_2629343 < baseStart_2629343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629345 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 6]
def baseStart_2629345 : Nat := 118140960795 + 2629345 * 2 ^ 59
def prefixEnd_2629345 : Nat := 4983230072969 + 3 ^ 40 * 2629345 * 2
def baseEnd_2629345 : Nat := 300026175888026757621193

theorem tailTrace_2629345 : CollatzResearch.WordTrace tailWord_2629345 prefixEnd_2629345 300026175888026757621193 := by
  unfold tailWord_2629345
  simp only [CollatzResearch.WordTrace]
  refine ⟨95900090659339596219905489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63933393772893064146603659 95900090659339596219905489)
  ·
    refine ⟨71925067994504697164929117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95900090659339596219905489 71925067994504697164929117)
    ·
      refine ⟨26971900497939261436848419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71925067994504697164929117 26971900497939261436848419)
      ·
        refine ⟨40457850746908892155272629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26971900497939261436848419 40457850746908892155272629)
        ·
          refine ⟨3792923507522708639556809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40457850746908892155272629 3792923507522708639556809)
          ·
            refine ⟨2844692630642031479667607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792923507522708639556809 2844692630642031479667607)
            ·
              refine ⟨4267038945963047219501411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844692630642031479667607 4267038945963047219501411)
              ·
                refine ⟨6400558418944570829252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267038945963047219501411 6400558418944570829252117)
                ·
                  refine ⟨300026175888026757621193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6400558418944570829252117 300026175888026757621193)
                  ·
                    rfl

theorem cell22_2629345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_2629345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629345 prefixEnd_2629345 := by exact prefixLift 2629345
  have htrace : WordTrace (prefixWord ++ tailWord_2629345) baseStart_2629345 baseEnd_2629345 := by
    simpa [prefixWord, tailWord_2629345, baseEnd_2629345] using wordTrace_append hprefix tailTrace_2629345
  have hstable : (prefixWord ++ tailWord_2629345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629345).length < 2 ^ (prefixWord ++ tailWord_2629345).sum := by decide
  have hdescent : baseEnd_2629345 < baseStart_2629345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629356 : List Nat := [2, 2, 1, 1, 2, 2, 3, 9]
def baseStart_2629356 : Nat := 118140960795 + 2629356 * 2 ^ 59
def prefixEnd_2629356 : Nat := 4983230072969 + 3 ^ 40 * 2629356 * 2
def baseEnd_2629356 : Nat := 100009143687653323426505

theorem tailTrace_2629356 : CollatzResearch.WordTrace tailWord_2629356 prefixEnd_2629356 100009143687653323426505 := by
  unfold tailWord_2629356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47950245931149872549277961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63933661241533163399037281 47950245931149872549277961)
  ·
    refine ⟨35962684448362404411958471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47950245931149872549277961 35962684448362404411958471)
    ·
      refine ⟨53944026672543606617937707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35962684448362404411958471 53944026672543606617937707)
      ·
        refine ⟨80916040008815409926906561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53944026672543606617937707 80916040008815409926906561)
        ·
          refine ⟨60687030006611557445179921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80916040008815409926906561 60687030006611557445179921)
          ·
            refine ⟨45515272504958668083884941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60687030006611557445179921 45515272504958668083884941)
            ·
              refine ⟨17068227189359500531456853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45515272504958668083884941 17068227189359500531456853)
              ·
                refine ⟨100009143687653323426505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17068227189359500531456853 100009143687653323426505)
                ·
                  rfl

theorem cell22_2629356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_2629356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629356 prefixEnd_2629356 := by exact prefixLift 2629356
  have htrace : WordTrace (prefixWord ++ tailWord_2629356) baseStart_2629356 baseEnd_2629356 := by
    simpa [prefixWord, tailWord_2629356, baseEnd_2629356] using wordTrace_append hprefix tailTrace_2629356
  have hstable : (prefixWord ++ tailWord_2629356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629356).length < 2 ^ (prefixWord ++ tailWord_2629356).sum := by decide
  have hdescent : baseEnd_2629356 < baseStart_2629356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629358 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2629358 : Nat := 118140960795 + 2629358 * 2 ^ 59
def prefixEnd_2629358 : Nat := 4983230072969 + 3 ^ 40 * 2629358 * 2
def baseEnd_2629358 : Nat := 900082977829752572288539

theorem tailTrace_2629358 : CollatzResearch.WordTrace tailWord_2629358 prefixEnd_2629358 900082977829752572288539 := by
  unfold tailWord_2629358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987570601036562430016091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63933709872194999626752485 11987570601036562430016091)
  ·
    refine ⟨17981355901554843645024137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11987570601036562430016091 17981355901554843645024137)
    ·
      refine ⟨13486016926166132733768103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17981355901554843645024137 13486016926166132733768103)
      ·
        refine ⟨20229025389249199100652155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13486016926166132733768103 20229025389249199100652155)
        ·
          refine ⟨30343538083873798650978233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20229025389249199100652155 30343538083873798650978233)
          ·
            refine ⟨22757653562905348988233675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30343538083873798650978233 22757653562905348988233675)
            ·
              refine ⟨34136480344358023482350513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22757653562905348988233675 34136480344358023482350513)
              ·
                refine ⟨25602360258268517611762885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34136480344358023482350513 25602360258268517611762885)
                ·
                  refine ⟨4800442548425347052205541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25602360258268517611762885 4800442548425347052205541)
                  ·
                    refine ⟨900082977829752572288539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800442548425347052205541 900082977829752572288539)
                    ·
                      rfl

theorem cell22_2629358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2629358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629358 prefixEnd_2629358 := by exact prefixLift 2629358
  have htrace : WordTrace (prefixWord ++ tailWord_2629358) baseStart_2629358 baseEnd_2629358 := by
    simpa [prefixWord, tailWord_2629358, baseEnd_2629358] using wordTrace_append hprefix tailTrace_2629358
  have hstable : (prefixWord ++ tailWord_2629358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629358).length < 2 ^ (prefixWord ++ tailWord_2629358).sum := by decide
  have hdescent : baseEnd_2629358 < baseStart_2629358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629364 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2629364 : Nat := 118140960795 + 2629364 * 2 ^ 59
def prefixEnd_2629364 : Nat := 4983230072969 + 3 ^ 40 * 2629364 * 2
def baseEnd_2629364 : Nat := 900085031752370556638521

theorem tailTrace_2629364 : CollatzResearch.WordTrace tailWord_2629364 prefixEnd_2629364 900085031752370556638521 := by
  unfold tailWord_2629364
  simp only [CollatzResearch.WordTrace]
  refine ⟨47950391823135381232423573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63933855764180508309898097 47950391823135381232423573)
  ·
    refine ⟨2247674616709470995269855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47950391823135381232423573 2247674616709470995269855)
    ·
      refine ⟨3371511925064206492904783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247674616709470995269855 3371511925064206492904783)
      ·
        refine ⟨5057267887596309739357175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371511925064206492904783 5057267887596309739357175)
        ·
          refine ⟨7585901831394464609035763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5057267887596309739357175 7585901831394464609035763)
          ·
            refine ⟨11378852747091696913553645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585901831394464609035763 11378852747091696913553645)
            ·
              refine ⟨4267069780159386342582617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11378852747091696913553645 4267069780159386342582617)
              ·
                refine ⟨3200302335119539756936963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267069780159386342582617 3200302335119539756936963)
                ·
                  refine ⟨4800453502679309635405445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200302335119539756936963 4800453502679309635405445)
                  ·
                    refine ⟨900085031752370556638521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800453502679309635405445 900085031752370556638521)
                    ·
                      rfl

theorem cell22_2629364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2629364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629364 prefixEnd_2629364 := by exact prefixLift 2629364
  have htrace : WordTrace (prefixWord ++ tailWord_2629364) baseStart_2629364 baseEnd_2629364 := by
    simpa [prefixWord, tailWord_2629364, baseEnd_2629364] using wordTrace_append hprefix tailTrace_2629364
  have hstable : (prefixWord ++ tailWord_2629364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629364).length < 2 ^ (prefixWord ++ tailWord_2629364).sum := by decide
  have hdescent : baseEnd_2629364 < baseStart_2629364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629394 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2629394 : Nat := 118140960795 + 2629394 * 2 ^ 59
def prefixEnd_2629394 : Nat := 4983230072969 + 3 ^ 40 * 2629394 * 2
def baseEnd_2629394 : Nat := 900095301365460478388429

theorem tailTrace_2629394 : CollatzResearch.WordTrace tailWord_2629394 prefixEnd_2629394 900095301365460478388429 := by
  unfold tailWord_2629394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23975469459040519397109809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63934585224108051725626157 23975469459040519397109809)
  ·
    refine ⟨17981602094280389547832357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23975469459040519397109809 17981602094280389547832357)
    ·
      refine ⟨3371550392677573040218567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17981602094280389547832357 3371550392677573040218567)
      ·
        refine ⟨5057325589016359560327851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371550392677573040218567 5057325589016359560327851)
        ·
          refine ⟨7585988383524539340491777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5057325589016359560327851 7585988383524539340491777)
          ·
            refine ⟨5689491287643404505368833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7585988383524539340491777 5689491287643404505368833)
            ·
              refine ⟨4267118465732553379026625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5689491287643404505368833 4267118465732553379026625)
              ·
                refine ⟨3200338849299415034269969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267118465732553379026625 3200338849299415034269969)
                ·
                  refine ⟨2400254136974561275702477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200338849299415034269969 2400254136974561275702477)
                  ·
                    refine ⟨900095301365460478388429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400254136974561275702477 900095301365460478388429)
                    ·
                      rfl

theorem cell22_2629394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2629394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629394 prefixEnd_2629394 := by exact prefixLift 2629394
  have htrace : WordTrace (prefixWord ++ tailWord_2629394) baseStart_2629394 baseEnd_2629394 := by
    simpa [prefixWord, tailWord_2629394, baseEnd_2629394] using wordTrace_append hprefix tailTrace_2629394
  have hstable : (prefixWord ++ tailWord_2629394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629394).length < 2 ^ (prefixWord ++ tailWord_2629394).sum := by decide
  have hdescent : baseEnd_2629394 < baseStart_2629394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629396 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2629396 : Nat := 118140960795 + 2629396 * 2 ^ 59
def prefixEnd_2629396 : Nat := 4983230072969 + 3 ^ 40 * 2629396 * 2
def baseEnd_2629396 : Nat := 300031995335444379946141

theorem tailTrace_2629396 : CollatzResearch.WordTrace tailWord_2629396 prefixEnd_2629396 300031995335444379946141 := by
  unfold tailWord_2629396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47950975391077415965006021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63934633854769887953341361 47950975391077415965006021)
  ·
    refine ⟨8990807885827015493438629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47950975391077415965006021 8990807885827015493438629)
    ·
      refine ⟨1685776478592565405019743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8990807885827015493438629 1685776478592565405019743)
      ·
        refine ⟨2528664717888848107529615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685776478592565405019743 2528664717888848107529615)
        ·
          refine ⟨3792997076833272161294423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528664717888848107529615 3792997076833272161294423)
          ·
            refine ⟨5689495615249908241941635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792997076833272161294423 5689495615249908241941635)
            ·
              refine ⟨8534243422874862362912453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689495615249908241941635 8534243422874862362912453)
              ·
                refine ⟨1600170641789036693046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8534243422874862362912453 1600170641789036693046085)
                ·
                  refine ⟨300031995335444379946141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600170641789036693046085 300031995335444379946141)
                  ·
                    rfl

theorem cell22_2629396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2629396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629396 prefixEnd_2629396 := by exact prefixLift 2629396
  have htrace : WordTrace (prefixWord ++ tailWord_2629396) baseStart_2629396 baseEnd_2629396 := by
    simpa [prefixWord, tailWord_2629396, baseEnd_2629396] using wordTrace_append hprefix tailTrace_2629396
  have hstable : (prefixWord ++ tailWord_2629396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629396).length < 2 ^ (prefixWord ++ tailWord_2629396).sum := by decide
  have hdescent : baseEnd_2629396 < baseStart_2629396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629401 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 11]
def baseStart_2629401 : Nat := 118140960795 + 2629401 * 2 ^ 59
def prefixEnd_2629401 : Nat := 4983230072969 + 3 ^ 40 * 2629401 * 2
def baseEnd_2629401 : Nat := 300032565869504931154469

theorem tailTrace_2629401 : CollatzResearch.WordTrace tailWord_2629401 prefixEnd_2629401 300032565869504931154469 := by
  unfold tailWord_2629401
  simp only [CollatzResearch.WordTrace]
  refine ⟨95902133147136717783944057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63934755431424478522629371 95902133147136717783944057)
  ·
    refine ⟨71926599860352538337958043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95902133147136717783944057 71926599860352538337958043)
    ·
      refine ⟨107889899790528807506937065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71926599860352538337958043 107889899790528807506937065)
      ·
        refine ⟨80917424842896605630202799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107889899790528807506937065 80917424842896605630202799)
        ·
          refine ⟨121376137264344908445304199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80917424842896605630202799 121376137264344908445304199)
          ·
            refine ⟨182064205896517362667956299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121376137264344908445304199 182064205896517362667956299)
            ·
              refine ⟨273096308844776044001934449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182064205896517362667956299 273096308844776044001934449)
              ·
                refine ⟨204822231633582033001450837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273096308844776044001934449 204822231633582033001450837)
                ·
                  refine ⟨300032565869504931154469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 204822231633582033001450837 300032565869504931154469)
                  ·
                    rfl

theorem cell22_2629401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_2629401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629401 prefixEnd_2629401 := by exact prefixLift 2629401
  have htrace : WordTrace (prefixWord ++ tailWord_2629401) baseStart_2629401 baseEnd_2629401 := by
    simpa [prefixWord, tailWord_2629401, baseEnd_2629401] using wordTrace_append hprefix tailTrace_2629401
  have hstable : (prefixWord ++ tailWord_2629401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629401).length < 2 ^ (prefixWord ++ tailWord_2629401).sum := by decide
  have hdescent : baseEnd_2629401 < baseStart_2629401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629439 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 1, 3]
def baseStart_2629439 : Nat := 118140960795 + 2629439 * 2 ^ 59
def prefixEnd_2629439 : Nat := 4983230072969 + 3 ^ 40 * 2629439 * 2
def baseEnd_2629439 : Nat := 900110705785095361013291

theorem tailTrace_2629439 : CollatzResearch.WordTrace tailWord_2629439 prefixEnd_2629439 900110705785095361013291 := by
  unfold tailWord_2629439
  simp only [CollatzResearch.WordTrace]
  refine ⟨95903519120999050273827371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63935679413999366849218247 95903519120999050273827371)
  ·
    refine ⟨143855278681498575410741057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95903519120999050273827371 143855278681498575410741057)
    ·
      refine ⟨107891459011123931558055793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143855278681498575410741057 107891459011123931558055793)
      ·
        refine ⟨80918594258342948668541845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107891459011123931558055793 80918594258342948668541845)
        ·
          refine ⟨3793059105859825718837899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80918594258342948668541845 3793059105859825718837899)
          ·
            refine ⟨5689588658789738578256849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793059105859825718837899 5689588658789738578256849)
            ·
              refine ⟨4267191494092303933692637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5689588658789738578256849 4267191494092303933692637)
              ·
                refine ⟨1600196810284613975134739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4267191494092303933692637 1600196810284613975134739)
                ·
                  refine ⟨2400295215426920962702109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600196810284613975134739 2400295215426920962702109)
                  ·
                    refine ⟨900110705785095361013291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400295215426920962702109 900110705785095361013291)
                    ·
                      rfl

theorem cell22_2629439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_2629439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629439 prefixEnd_2629439 := by exact prefixLift 2629439
  have htrace : WordTrace (prefixWord ++ tailWord_2629439) baseStart_2629439 baseEnd_2629439 := by
    simpa [prefixWord, tailWord_2629439, baseEnd_2629439] using wordTrace_append hprefix tailTrace_2629439
  have hstable : (prefixWord ++ tailWord_2629439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629439).length < 2 ^ (prefixWord ++ tailWord_2629439).sum := by decide
  have hdescent : baseEnd_2629439 < baseStart_2629439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629452 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_2629452 : Nat := 118140960795 + 2629452 * 2 ^ 59
def prefixEnd_2629452 : Nat := 4983230072969 + 3 ^ 40 * 2629452 * 2
def baseEnd_2629452 : Nat := 300038385316922553479417

theorem tailTrace_2629452 : CollatzResearch.WordTrace tailWord_2629452 prefixEnd_2629452 300038385316922553479417 := by
  unfold tailWord_2629452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47951996634975976747025305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63935995513301302329367073 47951996634975976747025305)
  ·
    refine ⟨35963997476231982560268979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47951996634975976747025305 35963997476231982560268979)
    ·
      refine ⟨53945996214347973840403469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35963997476231982560268979 53945996214347973840403469)
      ·
        refine ⟨20229748580380490190151301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53945996214347973840403469 20229748580380490190151301)
        ·
          refine ⟨3793077858821341910653369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20229748580380490190151301 3793077858821341910653369)
          ·
            refine ⟨2844808394116006432990027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793077858821341910653369 2844808394116006432990027)
            ·
              refine ⟨4267212591174009649485041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844808394116006432990027 4267212591174009649485041)
              ·
                refine ⟨3200409443380507237113781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267212591174009649485041 3200409443380507237113781)
                ·
                  refine ⟨300038385316922553479417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3200409443380507237113781 300038385316922553479417)
                  ·
                    rfl

theorem cell22_2629452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_2629452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629452 prefixEnd_2629452 := by exact prefixLift 2629452
  have htrace : WordTrace (prefixWord ++ tailWord_2629452) baseStart_2629452 baseEnd_2629452 := by
    simpa [prefixWord, tailWord_2629452, baseEnd_2629452] using wordTrace_append hprefix tailTrace_2629452
  have hstable : (prefixWord ++ tailWord_2629452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629452).length < 2 ^ (prefixWord ++ tailWord_2629452).sum := by decide
  have hdescent : baseEnd_2629452 < baseStart_2629452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629508 : List Nat := [2, 3, 2, 1, 1, 1, 12]
def baseStart_2629508 : Nat := 118140960795 + 2629508 * 2 ^ 59
def prefixEnd_2629508 : Nat := 4983230072969 + 3 ^ 40 * 2629508 * 2
def baseEnd_2629508 : Nat := 33338308366488969668077

theorem tailTrace_2629508 : CollatzResearch.WordTrace tailWord_2629508 prefixEnd_2629508 33338308366488969668077 := by
  unfold tailWord_2629508
  simp only [CollatzResearch.WordTrace]
  refine ⟨47953017878874537529044589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63937357171832716705392785 47953017878874537529044589)
  ·
    refine ⟨17982381704577951573391721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47953017878874537529044589 17982381704577951573391721)
    ·
      refine ⟨13486786278433463680043791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17982381704577951573391721 13486786278433463680043791)
      ·
        refine ⟨20230179417650195520065687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13486786278433463680043791 20230179417650195520065687)
        ·
          refine ⟨30345269126475293280098531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20230179417650195520065687 30345269126475293280098531)
          ·
            refine ⟨45517903689712939920147797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30345269126475293280098531 45517903689712939920147797)
            ·
              refine ⟨33338308366488969668077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 45517903689712939920147797 33338308366488969668077)
              ·
                rfl

theorem cell22_2629508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 12].length) (baseStart_2629508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629508 prefixEnd_2629508 := by exact prefixLift 2629508
  have htrace : WordTrace (prefixWord ++ tailWord_2629508) baseStart_2629508 baseEnd_2629508 := by
    simpa [prefixWord, tailWord_2629508, baseEnd_2629508] using wordTrace_append hprefix tailTrace_2629508
  have hstable : (prefixWord ++ tailWord_2629508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629508).length < 2 ^ (prefixWord ++ tailWord_2629508).sum := by decide
  have hdescent : baseEnd_2629508 < baseStart_2629508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629514 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_2629514 : Nat := 118140960795 + 2629514 * 2 ^ 59
def prefixEnd_2629514 : Nat := 4983230072969 + 3 ^ 40 * 2629514 * 2
def baseEnd_2629514 : Nat := 300045459939273388462687

theorem tailTrace_2629514 : CollatzResearch.WordTrace tailWord_2629514 prefixEnd_2629514 300045459939273388462687 := by
  unfold tailWord_2629514
  simp only [CollatzResearch.WordTrace]
  refine ⟨23976563648931834520701899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63937503063818225388538397 23976563648931834520701899)
  ·
    refine ⟨35964845473397751781052849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23976563648931834520701899 35964845473397751781052849)
    ·
      refine ⟨26973634105048313835789637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35964845473397751781052849 26973634105048313835789637)
      ·
        refine ⟨5057556394696558844210557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26973634105048313835789637 5057556394696558844210557)
        ·
          refine ⟨1896583648011209566578959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5057556394696558844210557 1896583648011209566578959)
          ·
            refine ⟨2844875472016814349868439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896583648011209566578959 2844875472016814349868439)
            ·
              refine ⟨4267313208025221524802659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844875472016814349868439 4267313208025221524802659)
              ·
                refine ⟨6400969812037832287203989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267313208025221524802659 6400969812037832287203989)
                ·
                  refine ⟨300045459939273388462687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6400969812037832287203989 300045459939273388462687)
                  ·
                    rfl

theorem cell22_2629514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_2629514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629514 prefixEnd_2629514 := by exact prefixLift 2629514
  have htrace : WordTrace (prefixWord ++ tailWord_2629514) baseStart_2629514 baseEnd_2629514 := by
    simpa [prefixWord, tailWord_2629514, baseEnd_2629514] using wordTrace_append hprefix tailTrace_2629514
  have hstable : (prefixWord ++ tailWord_2629514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629514).length < 2 ^ (prefixWord ++ tailWord_2629514).sum := by decide
  have hdescent : baseEnd_2629514 < baseStart_2629514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629690 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_2629690 : Nat := 118140960795 + 2629690 * 2 ^ 59
def prefixEnd_2629690 : Nat := 4983230072969 + 3 ^ 40 * 2629690 * 2
def baseEnd_2629690 : Nat := 900196628214614372987521

theorem tailTrace_2629690 : CollatzResearch.WordTrace tailWord_2629690 prefixEnd_2629690 900196628214614372987521 := by
  unfold tailWord_2629690
  simp only [CollatzResearch.WordTrace]
  refine ⟨23978168460772430035303631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63941782562059813427476349 23978168460772430035303631)
  ·
    refine ⟨35967252691158645052955447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23978168460772430035303631 35967252691158645052955447)
    ·
      refine ⟨53950879036737967579433171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35967252691158645052955447 53950879036737967579433171)
      ·
        refine ⟨80926318555106951369149757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53950879036737967579433171 80926318555106951369149757)
        ·
          refine ⟨30347369458165106763431159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80926318555106951369149757 30347369458165106763431159)
          ·
            refine ⟨45521054187247660145146739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30347369458165106763431159 45521054187247660145146739)
            ·
              refine ⟨68281581280871490217720109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45521054187247660145146739 68281581280871490217720109)
              ·
                refine ⟨25605592980326808831645041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68281581280871490217720109 25605592980326808831645041)
                ·
                  refine ⟨19204194735245106623733781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25605592980326808831645041 19204194735245106623733781)
                  ·
                    refine ⟨900196628214614372987521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19204194735245106623733781 900196628214614372987521)
                    ·
                      rfl

theorem cell22_2629690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_2629690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629690 prefixEnd_2629690 := by exact prefixLift 2629690
  have htrace : WordTrace (prefixWord ++ tailWord_2629690) baseStart_2629690 baseEnd_2629690 := by
    simpa [prefixWord, tailWord_2629690, baseEnd_2629690] using wordTrace_append hprefix tailTrace_2629690
  have hstable : (prefixWord ++ tailWord_2629690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629690).length < 2 ^ (prefixWord ++ tailWord_2629690).sum := by decide
  have hdescent : baseEnd_2629690 < baseStart_2629690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629694 : List Nat := [4, 2, 1, 3, 2, 1, 2, 7]
def baseStart_2629694 : Nat := 118140960795 + 2629694 * 2 ^ 59
def prefixEnd_2629694 : Nat := 4983230072969 + 3 ^ 40 * 2629694 * 2
def baseEnd_2629694 : Nat := 100021999721817743987501

theorem tailTrace_2629694 : CollatzResearch.WordTrace tailWord_2629694 prefixEnd_2629694 100021999721817743987501 := by
  unfold tailWord_2629694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11989102466884403603045017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63941879823383485882906757 11989102466884403603045017)
  ·
    refine ⟨8991826850163302702283763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11989102466884403603045017 8991826850163302702283763)
    ·
      refine ⟨13487740275244954053425645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991826850163302702283763 13487740275244954053425645)
      ·
        refine ⟨5057902603216857770034617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13487740275244954053425645 5057902603216857770034617)
        ·
          refine ⟨3793426952412643327525963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057902603216857770034617 3793426952412643327525963)
          ·
            refine ⟨5690140428618964991288945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793426952412643327525963 5690140428618964991288945)
            ·
              refine ⟨4267605321464223743466709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5690140428618964991288945 4267605321464223743466709)
              ·
                refine ⟨100021999721817743987501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4267605321464223743466709 100021999721817743987501)
                ·
                  rfl

theorem cell22_2629694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_2629694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629694 prefixEnd_2629694 := by exact prefixLift 2629694
  have htrace : WordTrace (prefixWord ++ tailWord_2629694) baseStart_2629694 baseEnd_2629694 := by
    simpa [prefixWord, tailWord_2629694, baseEnd_2629694] using wordTrace_append hprefix tailTrace_2629694
  have hstable : (prefixWord ++ tailWord_2629694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629694).length < 2 ^ (prefixWord ++ tailWord_2629694).sum := by decide
  have hdescent : baseEnd_2629694 < baseStart_2629694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629709 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2629709 : Nat := 118140960795 + 2629709 * 2 ^ 59
def prefixEnd_2629709 : Nat := 4983230072969 + 3 ^ 40 * 2629709 * 2
def baseEnd_2629709 : Nat := 900203132302904656762463

theorem tailTrace_2629709 : CollatzResearch.WordTrace tailWord_2629709 prefixEnd_2629709 900203132302904656762463 := by
  unfold tailWord_2629709
  simp only [CollatzResearch.WordTrace]
  refine ⟨95913366830020886386156181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63942244553347257590770787 95913366830020886386156181)
  ·
    refine ⟨4495939070157229049351071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95913366830020886386156181 4495939070157229049351071)
    ·
      refine ⟨6743908605235843574026607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495939070157229049351071 6743908605235843574026607)
      ·
        refine ⟨10115862907853765361039911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743908605235843574026607 10115862907853765361039911)
        ·
          refine ⟨15173794361780648041559867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115862907853765361039911 15173794361780648041559867)
          ·
            refine ⟨22760691542670972062339801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15173794361780648041559867 22760691542670972062339801)
            ·
              refine ⟨17070518657003229046754851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22760691542670972062339801 17070518657003229046754851)
              ·
                refine ⟨25605777985504843570132277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17070518657003229046754851 25605777985504843570132277)
                ·
                  refine ⟨2400541686141079084699901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25605777985504843570132277 2400541686141079084699901)
                  ·
                    refine ⟨900203132302904656762463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400541686141079084699901 900203132302904656762463)
                    ·
                      rfl

theorem cell22_2629709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2629709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629709 prefixEnd_2629709 := by exact prefixLift 2629709
  have htrace : WordTrace (prefixWord ++ tailWord_2629709) baseStart_2629709 baseEnd_2629709 := by
    simpa [prefixWord, tailWord_2629709, baseEnd_2629709] using wordTrace_append hprefix tailTrace_2629709
  have hstable : (prefixWord ++ tailWord_2629709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629709).length < 2 ^ (prefixWord ++ tailWord_2629709).sum := by decide
  have hdescent : baseEnd_2629709 < baseStart_2629709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629743 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 1, 3]
def baseStart_2629743 : Nat := 118140960795 + 2629743 * 2 ^ 59
def prefixEnd_2629743 : Nat := 4983230072969 + 3 ^ 40 * 2629743 * 2
def baseEnd_2629743 : Nat := 900214771197739901412359

theorem tailTrace_2629743 : CollatzResearch.WordTrace tailWord_2629743 prefixEnd_2629743 900214771197739901412359 := by
  unfold tailWord_2629743
  simp only [CollatzResearch.WordTrace]
  refine ⟨95914606911897710192893883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63943071274598473461929255 95914606911897710192893883)
  ·
    refine ⟨143871910367846565289340825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95914606911897710192893883 143871910367846565289340825)
    ·
      refine ⟨107903932775884923967005619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143871910367846565289340825 107903932775884923967005619)
      ·
        refine ⟨161855899163827385950508429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107903932775884923967005619 161855899163827385950508429)
        ·
          refine ⟨60695962186435269731440661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161855899163827385950508429 60695962186435269731440661)
          ·
            refine ⟨2845123227489153268661281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60695962186435269731440661 2845123227489153268661281)
            ·
              refine ⟨2133842420616864951495961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845123227489153268661281 2133842420616864951495961)
              ·
                refine ⟨1600381815462648713621971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133842420616864951495961 1600381815462648713621971)
                ·
                  refine ⟨2400572723193973070432957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600381815462648713621971 2400572723193973070432957)
                  ·
                    refine ⟨900214771197739901412359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400572723193973070432957 900214771197739901412359)
                    ·
                      rfl

theorem cell22_2629743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_2629743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629743 prefixEnd_2629743 := by exact prefixLift 2629743
  have htrace : WordTrace (prefixWord ++ tailWord_2629743) baseStart_2629743 baseEnd_2629743 := by
    simpa [prefixWord, tailWord_2629743, baseEnd_2629743] using wordTrace_append hprefix tailTrace_2629743
  have hstable : (prefixWord ++ tailWord_2629743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629743).length < 2 ^ (prefixWord ++ tailWord_2629743).sum := by decide
  have hdescent : baseEnd_2629743 < baseStart_2629743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629786 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_2629786 : Nat := 118140960795 + 2629786 * 2 ^ 59
def prefixEnd_2629786 : Nat := 4983230072969 + 3 ^ 40 * 2629786 * 2
def baseEnd_2629786 : Nat := 900229490976502122587227

theorem tailTrace_2629786 : CollatzResearch.WordTrace tailWord_2629786 prefixEnd_2629786 900229490976502122587227 := by
  unfold tailWord_2629786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23979043812685482134177303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63944116833827952357806141 23979043812685482134177303)
  ·
    refine ⟨35968565719028223201265955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23979043812685482134177303 35968565719028223201265955)
    ·
      refine ⟨53952848578542334801898933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35968565719028223201265955 53952848578542334801898933)
      ·
        refine ⟨5058079554238343887678025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53952848578542334801898933 5058079554238343887678025)
        ·
          refine ⟨3793559665678757915758519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5058079554238343887678025 3793559665678757915758519)
          ·
            refine ⟨5690339498518136873637779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793559665678757915758519 5690339498518136873637779)
            ·
              refine ⟨8535509247777205310456669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690339498518136873637779 8535509247777205310456669)
              ·
                refine ⟨3200815967916451991421251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8535509247777205310456669 3200815967916451991421251)
                ·
                  refine ⟨4801223951874677987131877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200815967916451991421251 4801223951874677987131877)
                  ·
                    refine ⟨900229490976502122587227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801223951874677987131877 900229490976502122587227)
                    ·
                      rfl

theorem cell22_2629786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_2629786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629786 prefixEnd_2629786 := by exact prefixLift 2629786
  have htrace : WordTrace (prefixWord ++ tailWord_2629786) baseStart_2629786 baseEnd_2629786 := by
    simpa [prefixWord, tailWord_2629786, baseEnd_2629786] using wordTrace_append hprefix tailTrace_2629786
  have hstable : (prefixWord ++ tailWord_2629786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629786).length < 2 ^ (prefixWord ++ tailWord_2629786).sum := by decide
  have hdescent : baseEnd_2629786 < baseStart_2629786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629797 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_2629797 : Nat := 118140960795 + 2629797 * 2 ^ 59
def prefixEnd_2629797 : Nat := 4983230072969 + 3 ^ 40 * 2629797 * 2
def baseEnd_2629797 : Nat := 900233256501301760562193

theorem tailTrace_2629797 : CollatzResearch.WordTrace tailWord_2629797 prefixEnd_2629797 900233256501301760562193 := by
  unfold tailWord_2629797
  simp only [CollatzResearch.WordTrace]
  refine ⟨95916576453702077415359645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63944384302468051610239763 95916576453702077415359645)
  ·
    refine ⟨35968716170138279030759867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95916576453702077415359645 35968716170138279030759867)
    ·
      refine ⟨53953074255207418546139801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35968716170138279030759867 53953074255207418546139801)
      ·
        refine ⟨40464805691405563909604851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53953074255207418546139801 40464805691405563909604851)
        ·
          refine ⟨60697208537108345864407277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40464805691405563909604851 60697208537108345864407277)
          ·
            refine ⟨22761453201415629699152729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60697208537108345864407277 22761453201415629699152729)
            ·
              refine ⟨17071089901061722274364547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22761453201415629699152729 17071089901061722274364547)
              ·
                refine ⟨25606634851592583411546821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17071089901061722274364547 25606634851592583411546821)
                ·
                  refine ⟨4801244034673609389665029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25606634851592583411546821 4801244034673609389665029)
                  ·
                    refine ⟨900233256501301760562193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4801244034673609389665029 900233256501301760562193)
                    ·
                      rfl

theorem cell22_2629797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_2629797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629797 prefixEnd_2629797 := by exact prefixLift 2629797
  have htrace : WordTrace (prefixWord ++ tailWord_2629797) baseStart_2629797 baseEnd_2629797 := by
    simpa [prefixWord, tailWord_2629797, baseEnd_2629797] using wordTrace_append hprefix tailTrace_2629797
  have hstable : (prefixWord ++ tailWord_2629797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629797).length < 2 ^ (prefixWord ++ tailWord_2629797).sum := by decide
  have hdescent : baseEnd_2629797 < baseStart_2629797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629816 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_2629816 : Nat := 118140960795 + 2629816 * 2 ^ 59
def prefixEnd_2629816 : Nat := 4983230072969 + 3 ^ 40 * 2629816 * 2
def baseEnd_2629816 : Nat := 900239760589592044337135

theorem tailTrace_2629816 : CollatzResearch.WordTrace tailWord_2629816 prefixEnd_2629816 900239760589592044337135 := by
  unfold tailWord_2629816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47958634720316621830150651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63944846293755495773534201 47958634720316621830150651)
  ·
    refine ⟨71937952080474932745225977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47958634720316621830150651 71937952080474932745225977)
    ·
      refine ⟨53953464060356199558919483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71937952080474932745225977 53953464060356199558919483)
      ·
        refine ⟨80930196090534299338379225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53953464060356199558919483 80930196090534299338379225)
        ·
          refine ⟨60697647067900724503784419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80930196090534299338379225 60697647067900724503784419)
          ·
            refine ⟨91046470601851086755676629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60697647067900724503784419 91046470601851086755676629)
            ·
              refine ⟨2133901654730884845836171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91046470601851086755676629 2133901654730884845836171)
              ·
                refine ⟨3200852482096327268754257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133901654730884845836171 3200852482096327268754257)
                ·
                  refine ⟨2400639361572245451565693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200852482096327268754257 2400639361572245451565693)
                  ·
                    refine ⟨900239760589592044337135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400639361572245451565693 900239760589592044337135)
                    ·
                      rfl

theorem cell22_2629816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_2629816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629816 prefixEnd_2629816 := by exact prefixLift 2629816
  have htrace : WordTrace (prefixWord ++ tailWord_2629816) baseStart_2629816 baseEnd_2629816 := by
    simpa [prefixWord, tailWord_2629816, baseEnd_2629816] using wordTrace_append hprefix tailTrace_2629816
  have hstable : (prefixWord ++ tailWord_2629816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629816).length < 2 ^ (prefixWord ++ tailWord_2629816).sum := by decide
  have hdescent : baseEnd_2629816 < baseStart_2629816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629846 : List Nat := [5, 2, 1, 2, 1, 3, 8]
def baseStart_2629846 : Nat := 118140960795 + 2629846 * 2 ^ 59
def prefixEnd_2629846 : Nat := 4983230072969 + 3 ^ 40 * 2629846 * 2
def baseEnd_2629846 : Nat := 33342593711210443188409

theorem tailTrace_2629846 : CollatzResearch.WordTrace tailWord_2629846 prefixEnd_2629846 33342593711210443188409 := by
  unfold tailWord_2629846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994897726907784923993337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63945575753683039189262261 5994897726907784923993337)
  ·
    refine ⟨4496173295180838692995003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5994897726907784923993337 4496173295180838692995003)
    ·
      refine ⟨6744259942771258039492505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496173295180838692995003 6744259942771258039492505)
      ·
        refine ⟨5058194957078443529619379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6744259942771258039492505 5058194957078443529619379)
        ·
          refine ⟨7587292435617665294429069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058194957078443529619379 7587292435617665294429069)
          ·
            refine ⟨2845234663356624485410901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7587292435617665294429069 2845234663356624485410901)
            ·
              refine ⟨33342593711210443188409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2845234663356624485410901 33342593711210443188409)
              ·
                rfl

theorem cell22_2629846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 8].length) (baseStart_2629846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629846 prefixEnd_2629846 := by exact prefixLift 2629846
  have htrace : WordTrace (prefixWord ++ tailWord_2629846) baseStart_2629846 baseEnd_2629846 := by
    simpa [prefixWord, tailWord_2629846, baseEnd_2629846] using wordTrace_append hprefix tailTrace_2629846
  have hstable : (prefixWord ++ tailWord_2629846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629846).length < 2 ^ (prefixWord ++ tailWord_2629846).sum := by decide
  have hdescent : baseEnd_2629846 < baseStart_2629846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629857 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 7]
def baseStart_2629857 : Nat := 118140960795 + 2629857 * 2 ^ 59
def prefixEnd_2629857 : Nat := 4983230072969 + 3 ^ 40 * 2629857 * 2
def baseEnd_2629857 : Nat := 300084598575827201354003

theorem tailTrace_2629857 : CollatzResearch.WordTrace tailWord_2629857 prefixEnd_2629857 300084598575827201354003 := by
  unfold tailWord_2629857
  simp only [CollatzResearch.WordTrace]
  refine ⟨95918764833484707662543825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63945843222323138441695883 95918764833484707662543825)
  ·
    refine ⟨71939073625113530746907869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95918764833484707662543825 71939073625113530746907869)
    ·
      refine ⟨26977152609417574030090451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71939073625113530746907869 26977152609417574030090451)
      ·
        refine ⟨40465728914126361045135677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26977152609417574030090451 40465728914126361045135677)
        ·
          refine ⟨15174648342797385391925879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40465728914126361045135677 15174648342797385391925879)
          ·
            refine ⟨22761972514196078087888819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15174648342797385391925879 22761972514196078087888819)
            ·
              refine ⟨34142958771294117131833229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22761972514196078087888819 34142958771294117131833229)
              ·
                refine ⟨12803609539235293924437461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34142958771294117131833229 12803609539235293924437461)
                ·
                  refine ⟨300084598575827201354003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12803609539235293924437461 300084598575827201354003)
                  ·
                    rfl

theorem cell22_2629857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_2629857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629857 prefixEnd_2629857 := by exact prefixLift 2629857
  have htrace : WordTrace (prefixWord ++ tailWord_2629857) baseStart_2629857 baseEnd_2629857 := by
    simpa [prefixWord, tailWord_2629857, baseEnd_2629857] using wordTrace_append hprefix tailTrace_2629857
  have hstable : (prefixWord ++ tailWord_2629857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629857).length < 2 ^ (prefixWord ++ tailWord_2629857).sum := by decide
  have hdescent : baseEnd_2629857 < baseStart_2629857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629861 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_2629861 : Nat := 118140960795 + 2629861 * 2 ^ 59
def prefixEnd_2629861 : Nat := 4983230072969 + 3 ^ 40 * 2629861 * 2
def baseEnd_2629861 : Nat := 900255165009226926961997

theorem tailTrace_2629861 : CollatzResearch.WordTrace tailWord_2629861 prefixEnd_2629861 900255165009226926961997 := by
  unfold tailWord_2629861
  simp only [CollatzResearch.WordTrace]
  refine ⟨95918910725470216345689437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63945940483646810897126291 95918910725470216345689437)
  ·
    refine ⟨35969591522051331129633539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95918910725470216345689437 35969591522051331129633539)
    ·
      refine ⟨53954387283076996694450309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969591522051331129633539 53954387283076996694450309)
      ·
        refine ⟨10116447615576936880209433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53954387283076996694450309 10116447615576936880209433)
        ·
          refine ⟨7587335711682702660157075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10116447615576936880209433 7587335711682702660157075)
          ·
            refine ⟨11381003567524053990235613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587335711682702660157075 11381003567524053990235613)
            ·
              refine ⟨4267876337821520246338355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11381003567524053990235613 4267876337821520246338355)
              ·
                refine ⟨6401814506732280369507533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267876337821520246338355 6401814506732280369507533)
                ·
                  refine ⟨2400680440024605138565325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6401814506732280369507533 2400680440024605138565325)
                  ·
                    refine ⟨900255165009226926961997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400680440024605138565325 900255165009226926961997)
                    ·
                      rfl

theorem cell22_2629861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_2629861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629861 prefixEnd_2629861 := by exact prefixLift 2629861
  have htrace : WordTrace (prefixWord ++ tailWord_2629861) baseStart_2629861 baseEnd_2629861 := by
    simpa [prefixWord, tailWord_2629861, baseEnd_2629861] using wordTrace_append hprefix tailTrace_2629861
  have hstable : (prefixWord ++ tailWord_2629861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629861).length < 2 ^ (prefixWord ++ tailWord_2629861).sum := by decide
  have hdescent : baseEnd_2629861 < baseStart_2629861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629872 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_2629872 : Nat := 118140960795 + 2629872 * 2 ^ 59
def prefixEnd_2629872 : Nat := 4983230072969 + 3 ^ 40 * 2629872 * 2
def baseEnd_2629872 : Nat := 900258930534026564936963

theorem tailTrace_2629872 : CollatzResearch.WordTrace tailWord_2629872 prefixEnd_2629872 900258930534026564936963 := by
  unfold tailWord_2629872
  simp only [CollatzResearch.WordTrace]
  refine ⟨47959655964215182612169935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63946207952286910149559913 47959655964215182612169935)
  ·
    refine ⟨71939483946322773918254903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47959655964215182612169935 71939483946322773918254903)
    ·
      refine ⟨107909225919484160877382355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71939483946322773918254903 107909225919484160877382355)
      ·
        refine ⟨161863838879226241316073533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107909225919484160877382355 161863838879226241316073533)
        ·
          refine ⟨60698939579709840493527575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161863838879226241316073533 60698939579709840493527575)
          ·
            refine ⟨91048409369564760740291363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60698939579709840493527575 91048409369564760740291363)
            ·
              refine ⟨136572614054347141110437045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91048409369564760740291363 136572614054347141110437045)
              ·
                refine ⟨12803682567595044479103473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136572614054347141110437045 12803682567595044479103473)
                ·
                  refine ⟨9602761925696283359327605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12803682567595044479103473 9602761925696283359327605)
                  ·
                    refine ⟨900258930534026564936963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9602761925696283359327605 900258930534026564936963)
                    ·
                      rfl

theorem cell22_2629872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_2629872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629872 prefixEnd_2629872 := by exact prefixLift 2629872
  have htrace : WordTrace (prefixWord ++ tailWord_2629872) baseStart_2629872 baseEnd_2629872 := by
    simpa [prefixWord, tailWord_2629872, baseEnd_2629872] using wordTrace_append hprefix tailTrace_2629872
  have hstable : (prefixWord ++ tailWord_2629872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629872).length < 2 ^ (prefixWord ++ tailWord_2629872).sum := by decide
  have hdescent : baseEnd_2629872 < baseStart_2629872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629968 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_2629968 : Nat := 118140960795 + 2629968 * 2 ^ 59
def prefixEnd_2629968 : Nat := 4983230072969 + 3 ^ 40 * 2629968 * 2
def baseEnd_2629968 : Nat := 900291793295914314536669

theorem tailTrace_2629968 : CollatzResearch.WordTrace tailWord_2629968 prefixEnd_2629968 900291793295914314536669 := by
  unfold tailWord_2629968
  simp only [CollatzResearch.WordTrace]
  refine ⟨47961406668041286809917279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63948542224055049079889705 47961406668041286809917279)
  ·
    refine ⟨71942110002061930214875919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47961406668041286809917279 71942110002061930214875919)
    ·
      refine ⟨107913165003092895322313879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71942110002061930214875919 107913165003092895322313879)
      ·
        refine ⟨161869747504639342983470819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107913165003092895322313879 161869747504639342983470819)
        ·
          refine ⟨242804621256959014475206229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161869747504639342983470819 242804621256959014475206229)
          ·
            refine ⟨2845366655354988450881323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 242804621256959014475206229 2845366655354988450881323)
            ·
              refine ⟨4268049983032482676321985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845366655354988450881323 4268049983032482676321985)
              ·
                refine ⟨3201037487274362007241489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268049983032482676321985 3201037487274362007241489)
                ·
                  refine ⟨2400778115455771505431117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201037487274362007241489 2400778115455771505431117)
                  ·
                    refine ⟨900291793295914314536669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400778115455771505431117 900291793295914314536669)
                    ·
                      rfl

theorem cell22_2629968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_2629968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2629968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2629968 prefixEnd_2629968 := by exact prefixLift 2629968
  have htrace : WordTrace (prefixWord ++ tailWord_2629968) baseStart_2629968 baseEnd_2629968 := by
    simpa [prefixWord, tailWord_2629968, baseEnd_2629968] using wordTrace_append hprefix tailTrace_2629968
  have hstable : (prefixWord ++ tailWord_2629968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629968).length < 2 ^ (prefixWord ++ tailWord_2629968).sum := by decide
  have hdescent : baseEnd_2629968 < baseStart_2629968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630030 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_2630030 : Nat := 118140960795 + 2630030 * 2 ^ 59
def prefixEnd_2630030 : Nat := 4983230072969 + 3 ^ 40 * 2630030 * 2
def baseEnd_2630030 : Nat := 900313017162966819486479

theorem tailTrace_2630030 : CollatzResearch.WordTrace tailWord_2630030 prefixEnd_2630030 900313017162966819486479 := by
  unfold tailWord_2630030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990634332732244776073943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63950049774571972139061029 11990634332732244776073943)
  ·
    refine ⟨17985951499098367164110915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11990634332732244776073943 17985951499098367164110915)
    ·
      refine ⟨26978927248647550746166373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17985951499098367164110915 26978927248647550746166373)
      ·
        refine ⟨5058548859121415764906195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26978927248647550746166373 5058548859121415764906195)
        ·
          refine ⟨7587823288682123647359293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058548859121415764906195 7587823288682123647359293)
          ·
            refine ⟨2845433733255796367759735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7587823288682123647359293 2845433733255796367759735)
            ·
              refine ⟨4268150599883694551639603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845433733255796367759735 4268150599883694551639603)
              ·
                refine ⟨6402225899825541827459405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268150599883694551639603 6402225899825541827459405)
                ·
                  refine ⟨2400834712434578185297277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6402225899825541827459405 2400834712434578185297277)
                  ·
                    refine ⟨900313017162966819486479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400834712434578185297277 900313017162966819486479)
                    ·
                      rfl

theorem cell22_2630030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_2630030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630030 prefixEnd_2630030 := by exact prefixLift 2630030
  have htrace : WordTrace (prefixWord ++ tailWord_2630030) baseStart_2630030 baseEnd_2630030 := by
    simpa [prefixWord, tailWord_2630030, baseEnd_2630030] using wordTrace_append hprefix tailTrace_2630030
  have hstable : (prefixWord ++ tailWord_2630030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630030).length < 2 ^ (prefixWord ++ tailWord_2630030).sum := by decide
  have hdescent : baseEnd_2630030 < baseStart_2630030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630088 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 4]
def baseStart_2630088 : Nat := 118140960795 + 2630088 * 2 ^ 59
def prefixEnd_2630088 : Nat := 4983230072969 + 3 ^ 40 * 2630088 * 2
def baseEnd_2630088 : Nat := 300110957249424667178767

theorem tailTrace_2630088 : CollatzResearch.WordTrace tailWord_2630088 prefixEnd_2630088 300110957249424667178767 := by
  unfold tailWord_2630088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47963595047823917057101459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63951460063765222742801945 47963595047823917057101459)
  ·
    refine ⟨71945392571735875585652189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47963595047823917057101459 71945392571735875585652189)
    ·
      refine ⟨26979522214400953344619571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71945392571735875585652189 26979522214400953344619571)
      ·
        refine ⟨40469283321601430016929357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26979522214400953344619571 40469283321601430016929357)
        ·
          refine ⟨15175981245600536256348509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40469283321601430016929357 15175981245600536256348509)
          ·
            refine ⟨5690992967100201096130691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15175981245600536256348509 5690992967100201096130691)
            ·
              refine ⟨8536489450650301644196037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690992967100201096130691 8536489450650301644196037)
              ·
                refine ⟨1600591771996931558286757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8536489450650301644196037 1600591771996931558286757)
                ·
                  refine ⟨300110957249424667178767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600591771996931558286757 300110957249424667178767)
                  ·
                    rfl

theorem cell22_2630088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_2630088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630088 prefixEnd_2630088 := by exact prefixLift 2630088
  have htrace : WordTrace (prefixWord ++ tailWord_2630088) baseStart_2630088 baseEnd_2630088 := by
    simpa [prefixWord, tailWord_2630088, baseEnd_2630088] using wordTrace_append hprefix tailTrace_2630088
  have hstable : (prefixWord ++ tailWord_2630088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630088).length < 2 ^ (prefixWord ++ tailWord_2630088).sum := by decide
  have hdescent : baseEnd_2630088 < baseStart_2630088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630131 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 5, 3]
def baseStart_2630131 : Nat := 118140960795 + 2630131 * 2 ^ 59
def prefixEnd_2630131 : Nat := 4983230072969 + 3 ^ 40 * 2630131 * 2
def baseEnd_2630131 : Nat := 900347591527036222711169

theorem tailTrace_2630131 : CollatzResearch.WordTrace tailWord_2630131 prefixEnd_2630131 900347591527036222711169 := by
  unfold tailWord_2630131
  simp only [CollatzResearch.WordTrace]
  refine ⟨95928758434492052458018247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63952505622994701638678831 95928758434492052458018247)
  ·
    refine ⟨143893137651738078687027371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95928758434492052458018247 143893137651738078687027371)
    ·
      refine ⟨215839706477607118030541057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143893137651738078687027371 215839706477607118030541057)
      ·
        refine ⟨161879779858205338522905793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215839706477607118030541057 161879779858205338522905793)
        ·
          refine ⟨121409834893654003892179345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161879779858205338522905793 121409834893654003892179345)
          ·
            refine ⟨91057376170240502919134509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121409834893654003892179345 91057376170240502919134509)
            ·
              refine ⟨34146516063840188594675441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91057376170240502919134509 34146516063840188594675441)
              ·
                refine ⟨25609887047880141446006581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34146516063840188594675441 25609887047880141446006581)
                ·
                  refine ⟨2400926910738763260563117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25609887047880141446006581 2400926910738763260563117)
                  ·
                    refine ⟨900347591527036222711169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400926910738763260563117 900347591527036222711169)
                    ·
                      rfl

theorem cell22_2630131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3].length) (baseStart_2630131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630131 prefixEnd_2630131 := by exact prefixLift 2630131
  have htrace : WordTrace (prefixWord ++ tailWord_2630131) baseStart_2630131 baseEnd_2630131 := by
    simpa [prefixWord, tailWord_2630131, baseEnd_2630131] using wordTrace_append hprefix tailTrace_2630131
  have hstable : (prefixWord ++ tailWord_2630131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630131).length < 2 ^ (prefixWord ++ tailWord_2630131).sum := by decide
  have hdescent : baseEnd_2630131 < baseStart_2630131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630133 : List Nat := [1, 3, 5, 1, 2, 1, 9]
def baseStart_2630133 : Nat := 118140960795 + 2630133 * 2 ^ 59
def prefixEnd_2630133 : Nat := 4983230072969 + 3 ^ 40 * 2630133 * 2
def baseEnd_2630133 : Nat := 33346232450663292005969

theorem tailTrace_2630133 : CollatzResearch.WordTrace tailWord_2630133 prefixEnd_2630133 33346232450663292005969 := by
  unfold tailWord_2630133
  simp only [CollatzResearch.WordTrace]
  refine ⟨95928831380484806799591053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63952554253656537866394035 95928831380484806799591053)
  ·
    refine ⟨35973311767681802549846645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95928831380484806799591053 35973311767681802549846645)
    ·
      refine ⟨3372497978220168989048123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35973311767681802549846645 3372497978220168989048123)
      ·
        refine ⟨5058746967330253483572185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372497978220168989048123 5058746967330253483572185)
        ·
          refine ⟨3794060225497690112679139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5058746967330253483572185 3794060225497690112679139)
          ·
            refine ⟨5691090338246535169018709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794060225497690112679139 5691090338246535169018709)
            ·
              refine ⟨33346232450663292005969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5691090338246535169018709 33346232450663292005969)
              ·
                rfl

theorem cell22_2630133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 9].length) (baseStart_2630133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630133 prefixEnd_2630133 := by exact prefixLift 2630133
  have htrace : WordTrace (prefixWord ++ tailWord_2630133) baseStart_2630133 baseEnd_2630133 := by
    simpa [prefixWord, tailWord_2630133, baseEnd_2630133] using wordTrace_append hprefix tailTrace_2630133
  have hstable : (prefixWord ++ tailWord_2630133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630133).length < 2 ^ (prefixWord ++ tailWord_2630133).sum := by decide
  have hdescent : baseEnd_2630133 < baseStart_2630133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630167 : List Nat := [1, 1, 3, 6, 2, 1, 2, 6]
def baseStart_2630167 : Nat := 118140960795 + 2630167 * 2 ^ 59
def prefixEnd_2630167 : Nat := 4983230072969 + 3 ^ 40 * 2630167 * 2
def baseEnd_2630167 : Nat := 100039990562527125423451

theorem tailTrace_2630167 : CollatzResearch.WordTrace tailWord_2630167 prefixEnd_2630167 100039990562527125423451 := by
  unfold tailWord_2630167
  simp only [CollatzResearch.WordTrace]
  refine ⟨95930071462361630606328755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63953380974907753737552503 95930071462361630606328755)
  ·
    refine ⟨143895107193542445909493133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95930071462361630606328755 143895107193542445909493133)
    ·
      refine ⟨53960665197578417216059925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143895107193542445909493133 53960665197578417216059925)
      ·
        refine ⟨2529406181136488307002809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53960665197578417216059925 2529406181136488307002809)
        ·
          refine ⟨1897054635852366230252107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2529406181136488307002809 1897054635852366230252107)
          ·
            refine ⟨2845581953778549345378161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897054635852366230252107 2845581953778549345378161)
            ·
              refine ⟨2134186465333912009033621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845581953778549345378161 2134186465333912009033621)
              ·
                refine ⟨100039990562527125423451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2134186465333912009033621 100039990562527125423451)
                ·
                  rfl

theorem cell22_2630167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 6].length) (baseStart_2630167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630167 prefixEnd_2630167 := by exact prefixLift 2630167
  have htrace : WordTrace (prefixWord ++ tailWord_2630167) baseStart_2630167 baseEnd_2630167 := by
    simpa [prefixWord, tailWord_2630167, baseEnd_2630167] using wordTrace_append hprefix tailTrace_2630167
  have hstable : (prefixWord ++ tailWord_2630167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630167).length < 2 ^ (prefixWord ++ tailWord_2630167).sum := by decide
  have hdescent : baseEnd_2630167 < baseStart_2630167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630225 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_2630225 : Nat := 118140960795 + 2630225 * 2 ^ 59
def prefixEnd_2630225 : Nat := 4983230072969 + 3 ^ 40 * 2630225 * 2
def baseEnd_2630225 : Nat := 900379769648051310860881

theorem tailTrace_2630225 : CollatzResearch.WordTrace tailWord_2630225 prefixEnd_2630225 900379769648051310860881 := by
  unfold tailWord_2630225
  simp only [CollatzResearch.WordTrace]
  refine ⟨95932186896151506511940129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63954791264101004341293419 95932186896151506511940129)
  ·
    refine ⟨71949140172113629883955097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95932186896151506511940129 71949140172113629883955097)
    ·
      refine ⟨53961855129085222412966323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71949140172113629883955097 53961855129085222412966323)
      ·
        refine ⟨80942782693627833619449485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53961855129085222412966323 80942782693627833619449485)
        ·
          refine ⟨30353543510110437607293557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80942782693627833619449485 30353543510110437607293557)
          ·
            refine ⟨2845644704072853525683771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30353543510110437607293557 2845644704072853525683771)
            ·
              refine ⟨4268467056109280288525657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845644704072853525683771 4268467056109280288525657)
              ·
                refine ⟨3201350292081960216394243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268467056109280288525657 3201350292081960216394243)
                ·
                  refine ⟨4802025438122940324591365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201350292081960216394243 4802025438122940324591365)
                  ·
                    refine ⟨900379769648051310860881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802025438122940324591365 900379769648051310860881)
                    ·
                      rfl

theorem cell22_2630225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_2630225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630225 prefixEnd_2630225 := by exact prefixLift 2630225
  have htrace : WordTrace (prefixWord ++ tailWord_2630225) baseStart_2630225 baseEnd_2630225 := by
    simpa [prefixWord, tailWord_2630225, baseEnd_2630225] using wordTrace_append hprefix tailTrace_2630225
  have hstable : (prefixWord ++ tailWord_2630225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630225).length < 2 ^ (prefixWord ++ tailWord_2630225).sum := by decide
  have hdescent : baseEnd_2630225 < baseStart_2630225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630274 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2630274 : Nat := 118140960795 + 2630274 * 2 ^ 59
def prefixEnd_2630274 : Nat := 4983230072969 + 3 ^ 40 * 2630274 * 2
def baseEnd_2630274 : Nat := 300132181116477172128577

theorem tailTrace_2630274 : CollatzResearch.WordTrace tailWord_2630274 prefixEnd_2630274 300132181116477172128577 := by
  unfold tailWord_2630274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23983493518243496970118469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63955982715315991920315917 23983493518243496970118469)
  ·
    refine ⟨4496905034670655681897213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23983493518243496970118469 4496905034670655681897213)
    ·
      refine ⟨1686339388001495880711455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4496905034670655681897213 1686339388001495880711455)
      ·
        refine ⟨2529509082002243821067183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686339388001495880711455 2529509082002243821067183)
        ·
          refine ⟨3794263623003365731600775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529509082002243821067183 3794263623003365731600775)
          ·
            refine ⟨5691395434505048597401163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794263623003365731600775 5691395434505048597401163)
            ·
              refine ⟨8537093151757572896101745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691395434505048597401163 8537093151757572896101745)
              ·
                refine ⟨6402819863818179672076309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8537093151757572896101745 6402819863818179672076309)
                ·
                  refine ⟨300132181116477172128577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6402819863818179672076309 300132181116477172128577)
                  ·
                    rfl

theorem cell22_2630274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2630274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630274 prefixEnd_2630274 := by exact prefixLift 2630274
  have htrace : WordTrace (prefixWord ++ tailWord_2630274) baseStart_2630274 baseEnd_2630274 := by
    simpa [prefixWord, tailWord_2630274, baseEnd_2630274] using wordTrace_append hprefix tailTrace_2630274
  have hstable : (prefixWord ++ tailWord_2630274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630274).length < 2 ^ (prefixWord ++ tailWord_2630274).sum := by decide
  have hdescent : baseEnd_2630274 < baseStart_2630274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630281 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_2630281 : Nat := 118140960795 + 2630281 * 2 ^ 59
def prefixEnd_2630281 : Nat := 4983230072969 + 3 ^ 40 * 2630281 * 2
def baseEnd_2630281 : Nat := 900398939592485831460709

theorem tailTrace_2630281 : CollatzResearch.WordTrace tailWord_2630281 prefixEnd_2630281 900398939592485831460709 := by
  unfold tailWord_2630281
  simp only [CollatzResearch.WordTrace]
  refine ⟨95934229383948628075978697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63956152922632418717319131 95934229383948628075978697)
  ·
    refine ⟨71950672037961471056984023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95934229383948628075978697 71950672037961471056984023)
    ·
      refine ⟨107926008056942206585476035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71950672037961471056984023 107926008056942206585476035)
      ·
        refine ⟨161889012085413309878214053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107926008056942206585476035 161889012085413309878214053)
        ·
          refine ⟨30354189766014995602165135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161889012085413309878214053 30354189766014995602165135)
          ·
            refine ⟨45531284649022493403247703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30354189766014995602165135 45531284649022493403247703)
            ·
              refine ⟨68296926973533740104871555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45531284649022493403247703 68296926973533740104871555)
              ·
                refine ⟨102445390460300610157307333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68296926973533740104871555 102445390460300610157307333)
                ·
                  refine ⟨19208510711306364404495125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102445390460300610157307333 19208510711306364404495125)
                  ·
                    refine ⟨900398939592485831460709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19208510711306364404495125 900398939592485831460709)
                    ·
                      rfl

theorem cell22_2630281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_2630281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630281 prefixEnd_2630281 := by exact prefixLift 2630281
  have htrace : WordTrace (prefixWord ++ tailWord_2630281) baseStart_2630281 baseEnd_2630281 := by
    simpa [prefixWord, tailWord_2630281, baseEnd_2630281] using wordTrace_append hprefix tailTrace_2630281
  have hstable : (prefixWord ++ tailWord_2630281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630281).length < 2 ^ (prefixWord ++ tailWord_2630281).sum := by decide
  have hdescent : baseEnd_2630281 < baseStart_2630281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630317 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2630317 : Nat := 118140960795 + 2630317 * 2 ^ 59
def prefixEnd_2630317 : Nat := 4983230072969 + 3 ^ 40 * 2630317 * 2
def baseEnd_2630317 : Nat := 900411263128193737560599

theorem tailTrace_2630317 : CollatzResearch.WordTrace tailWord_2630317 prefixEnd_2630317 900411263128193737560599 := by
  unfold tailWord_2630317
  simp only [CollatzResearch.WordTrace]
  refine ⟨95935542411818206224289205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63957028274545470816192803 95935542411818206224289205)
  ·
    refine ⟨8993957101107956833527113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95935542411818206224289205 8993957101107956833527113)
    ·
      refine ⟨6745467825830967625145335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8993957101107956833527113 6745467825830967625145335)
      ·
        refine ⟨10118201738746451437718003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745467825830967625145335 10118201738746451437718003)
        ·
          refine ⟨15177302608119677156577005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10118201738746451437718003 15177302608119677156577005)
          ·
            refine ⟨5691488478044878933716377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15177302608119677156577005 5691488478044878933716377)
            ·
              refine ⟨4268616358533659200287283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691488478044878933716377 4268616358533659200287283)
              ·
                refine ⟨6402924537800488800430925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268616358533659200287283 6402924537800488800430925)
                ·
                  refine ⟨2401096701675183300161597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6402924537800488800430925 2401096701675183300161597)
                  ·
                    refine ⟨900411263128193737560599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401096701675183300161597 900411263128193737560599)
                    ·
                      rfl

theorem cell22_2630317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2630317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630317 prefixEnd_2630317 := by exact prefixLift 2630317
  have htrace : WordTrace (prefixWord ++ tailWord_2630317) baseStart_2630317 baseEnd_2630317 := by
    simpa [prefixWord, tailWord_2630317, baseEnd_2630317] using wordTrace_append hprefix tailTrace_2630317
  have hstable : (prefixWord ++ tailWord_2630317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630317).length < 2 ^ (prefixWord ++ tailWord_2630317).sum := by decide
  have hdescent : baseEnd_2630317 < baseStart_2630317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630330 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_2630330 : Nat := 118140960795 + 2630330 * 2 ^ 59
def prefixEnd_2630330 : Nat := 4983230072969 + 3 ^ 40 * 2630330 * 2
def baseEnd_2630330 : Nat := 300138571097955345661853

theorem tailTrace_2630330 : CollatzResearch.WordTrace tailWord_2630330 prefixEnd_2630330 300138571097955345661853 := by
  unfold tailWord_2630330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23984004140192777361128111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63957344373847406296341629 23984004140192777361128111)
  ·
    refine ⟨35976006210289166041692167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23984004140192777361128111 35976006210289166041692167)
    ·
      refine ⟨53964009315433749062538251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35976006210289166041692167 53964009315433749062538251)
      ·
        refine ⟨80946013973150623593807377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53964009315433749062538251 80946013973150623593807377)
        ·
          refine ⟨60709510479862967695355533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80946013973150623593807377 60709510479862967695355533)
          ·
            refine ⟨22766066429948612885758325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60709510479862967695355533 22766066429948612885758325)
            ·
              refine ⟨2134318727807682458039843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22766066429948612885758325 2134318727807682458039843)
              ·
                refine ⟨3201478091711523687059765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134318727807682458039843 3201478091711523687059765)
                ·
                  refine ⟨300138571097955345661853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201478091711523687059765 300138571097955345661853)
                  ·
                    rfl

theorem cell22_2630330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_2630330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630330 prefixEnd_2630330 := by exact prefixLift 2630330
  have htrace : WordTrace (prefixWord ++ tailWord_2630330) baseStart_2630330 baseEnd_2630330 := by
    simpa [prefixWord, tailWord_2630330, baseEnd_2630330] using wordTrace_append hprefix tailTrace_2630330
  have hstable : (prefixWord ++ tailWord_2630330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630330).length < 2 ^ (prefixWord ++ tailWord_2630330).sum := by decide
  have hdescent : baseEnd_2630330 < baseStart_2630330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630360 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_2630360 : Nat := 118140960795 + 2630360 * 2 ^ 59
def prefixEnd_2630360 : Nat := 4983230072969 + 3 ^ 40 * 2630360 * 2
def baseEnd_2630360 : Nat := 900425982906955958735467

theorem tailTrace_2630360 : CollatzResearch.WordTrace tailWord_2630360 prefixEnd_2630360 900425982906955958735467 := by
  unfold tailWord_2630360
  simp only [CollatzResearch.WordTrace]
  refine ⟨47968555375331212284052267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63958073833774949712069689 47968555375331212284052267)
  ·
    refine ⟨71952833062996818426078401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47968555375331212284052267 71952833062996818426078401)
    ·
      refine ⟨53964624797247613819558801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71952833062996818426078401 53964624797247613819558801)
      ·
        refine ⟨40473468597935710364669101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53964624797247613819558801 40473468597935710364669101)
        ·
          refine ⟨15177550724225891386750913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40473468597935710364669101 15177550724225891386750913)
          ·
            refine ⟨11383163043169418540063185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15177550724225891386750913 11383163043169418540063185)
            ·
              refine ⟨8537372282377063905047389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11383163043169418540063185 8537372282377063905047389)
              ·
                refine ⟨3201514605891398964392771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8537372282377063905047389 3201514605891398964392771)
                ·
                  refine ⟨4802271908837098446589157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201514605891398964392771 4802271908837098446589157)
                  ·
                    refine ⟨900425982906955958735467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802271908837098446589157 900425982906955958735467)
                    ·
                      rfl

theorem cell22_2630360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_2630360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630360 prefixEnd_2630360 := by exact prefixLift 2630360
  have htrace : WordTrace (prefixWord ++ tailWord_2630360) baseStart_2630360 baseEnd_2630360 := by
    simpa [prefixWord, tailWord_2630360, baseEnd_2630360] using wordTrace_append hprefix tailTrace_2630360
  have hstable : (prefixWord ++ tailWord_2630360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630360).length < 2 ^ (prefixWord ++ tailWord_2630360).sum := by decide
  have hdescent : baseEnd_2630360 < baseStart_2630360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630390 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2630390 : Nat := 118140960795 + 2630390 * 2 ^ 59
def prefixEnd_2630390 : Nat := 4983230072969 + 3 ^ 40 * 2630390 * 2
def baseEnd_2630390 : Nat := 900436252520045880485375

theorem tailTrace_2630390 : CollatzResearch.WordTrace tailWord_2630390 prefixEnd_2630390 900436252520045880485375 := by
  unfold tailWord_2630390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996137808784608730731039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63958803293702493127797749 5996137808784608730731039)
  ·
    refine ⟨8994206713176913096096559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996137808784608730731039 8994206713176913096096559)
    ·
      refine ⟨13491310069765369644144839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8994206713176913096096559 13491310069765369644144839)
      ·
        refine ⟨20236965104648054466217259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13491310069765369644144839 20236965104648054466217259)
        ·
          refine ⟨30355447656972081699325889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20236965104648054466217259 30355447656972081699325889)
          ·
            refine ⟨22766585742729061274494417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30355447656972081699325889 22766585742729061274494417)
            ·
              refine ⟨17074939307046795955870813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22766585742729061274494417 17074939307046795955870813)
              ·
                refine ⟨6403102240142548483451555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17074939307046795955870813 6403102240142548483451555)
                ·
                  refine ⟨9604653360213822725177333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403102240142548483451555 9604653360213822725177333)
                  ·
                    refine ⟨900436252520045880485375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9604653360213822725177333 900436252520045880485375)
                    ·
                      rfl

theorem cell22_2630390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2630390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630390 prefixEnd_2630390 := by exact prefixLift 2630390
  have htrace : WordTrace (prefixWord ++ tailWord_2630390) baseStart_2630390 baseEnd_2630390 := by
    simpa [prefixWord, tailWord_2630390, baseEnd_2630390] using wordTrace_append hprefix tailTrace_2630390
  have hstable : (prefixWord ++ tailWord_2630390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630390).length < 2 ^ (prefixWord ++ tailWord_2630390).sum := by decide
  have hdescent : baseEnd_2630390 < baseStart_2630390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630420 : List Nat := [2, 4, 4, 12]
def baseStart_2630420 : Nat := 118140960795 + 2630420 * 2 ^ 59
def prefixEnd_2630420 : Nat := 4983230072969 + 3 ^ 40 * 2630420 * 2
def baseEnd_2630420 : Nat := 1235180414448745956427

theorem tailTrace_2630420 : CollatzResearch.WordTrace tailWord_2630420 prefixEnd_2630420 1235180414448745956427 := by
  unfold tailWord_2630420
  simp only [CollatzResearch.WordTrace]
  refine ⟨47969649565222527407644357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63959532753630036543525809 47969649565222527407644357)
  ·
    refine ⟨8994309293479223888933317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47969649565222527407644357 8994309293479223888933317)
    ·
      refine ⟨1686432992527354479174997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8994309293479223888933317 1686432992527354479174997)
      ·
        refine ⟨1235180414448745956427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1686432992527354479174997 1235180414448745956427)
        ·
          rfl

theorem cell22_2630420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 12].length) (baseStart_2630420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630420 prefixEnd_2630420 := by exact prefixLift 2630420
  have htrace : WordTrace (prefixWord ++ tailWord_2630420) baseStart_2630420 baseEnd_2630420 := by
    simpa [prefixWord, tailWord_2630420, baseEnd_2630420] using wordTrace_append hprefix tailTrace_2630420
  have hstable : (prefixWord ++ tailWord_2630420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630420).length < 2 ^ (prefixWord ++ tailWord_2630420).sum := by decide
  have hdescent : baseEnd_2630420 < baseStart_2630420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630433 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2630433 : Nat := 118140960795 + 2630433 * 2 ^ 59
def prefixEnd_2630433 : Nat := 4983230072969 + 3 ^ 40 * 2630433 * 2
def baseEnd_2630433 : Nat := 900450972298808101660243

theorem tailTrace_2630433 : CollatzResearch.WordTrace tailWord_2630433 prefixEnd_2630433 900450972298808101660243 := by
  unfold tailWord_2630433
  simp only [CollatzResearch.WordTrace]
  refine ⟨95939773279397958035511953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63959848852931972023674635 95939773279397958035511953)
  ·
    refine ⟨71954829959548468526633965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95939773279397958035511953 71954829959548468526633965)
    ·
      refine ⟨26983061234830675697487737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71954829959548468526633965 26983061234830675697487737)
      ·
        refine ⟨20237295926123006773115803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26983061234830675697487737 20237295926123006773115803)
        ·
          refine ⟨30355943889184510159673705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20237295926123006773115803 30355943889184510159673705)
          ·
            refine ⟨22766957916888382619755279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30355943889184510159673705 22766957916888382619755279)
            ·
              refine ⟨34150436875332573929632919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22766957916888382619755279 34150436875332573929632919)
              ·
                refine ⟨51225655312998860894449379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34150436875332573929632919 51225655312998860894449379)
                ·
                  refine ⟨76838482969498291341674069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51225655312998860894449379 76838482969498291341674069)
                  ·
                    refine ⟨900450972298808101660243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76838482969498291341674069 900450972298808101660243)
                    ·
                      rfl

theorem cell22_2630433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2630433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630433 prefixEnd_2630433 := by exact prefixLift 2630433
  have htrace : WordTrace (prefixWord ++ tailWord_2630433) baseStart_2630433 baseEnd_2630433 := by
    simpa [prefixWord, tailWord_2630433, baseEnd_2630433] using wordTrace_append hprefix tailTrace_2630433
  have hstable : (prefixWord ++ tailWord_2630433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630433).length < 2 ^ (prefixWord ++ tailWord_2630433).sum := by decide
  have hdescent : baseEnd_2630433 < baseStart_2630433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630435 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 3, 3]
def baseStart_2630435 : Nat := 118140960795 + 2630435 * 2 ^ 59
def prefixEnd_2630435 : Nat := 4983230072969 + 3 ^ 40 * 2630435 * 2
def baseEnd_2630435 : Nat := 900451656939680763110237

theorem tailTrace_2630435 : CollatzResearch.WordTrace tailWord_2630435 prefixEnd_2630435 900451656939680763110237 := by
  unfold tailWord_2630435
  simp only [CollatzResearch.WordTrace]
  refine ⟨95939846225390712377084759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63959897483593808251389839 95939846225390712377084759)
  ·
    refine ⟨143909769338086068565627139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95939846225390712377084759 143909769338086068565627139)
    ·
      refine ⟨215864654007129102848440709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143909769338086068565627139 215864654007129102848440709)
      ·
        refine ⟨40474622626336706784082633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215864654007129102848440709 40474622626336706784082633)
        ·
          refine ⟨30355966969752530088061975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40474622626336706784082633 30355966969752530088061975)
          ·
            refine ⟨45533950454628795132092963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30355966969752530088061975 45533950454628795132092963)
            ·
              refine ⟨68300925681943192698139445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45533950454628795132092963 68300925681943192698139445)
              ·
                refine ⟨6403211782682174315450573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68300925681943192698139445 6403211782682174315450573)
                ·
                  refine ⟨2401204418505815368293965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6403211782682174315450573 2401204418505815368293965)
                  ·
                    refine ⟨900451656939680763110237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401204418505815368293965 900451656939680763110237)
                    ·
                      rfl

theorem cell22_2630435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3].length) (baseStart_2630435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630435 prefixEnd_2630435 := by exact prefixLift 2630435
  have htrace : WordTrace (prefixWord ++ tailWord_2630435) baseStart_2630435 baseEnd_2630435 := by
    simpa [prefixWord, tailWord_2630435, baseEnd_2630435] using wordTrace_append hprefix tailTrace_2630435
  have hstable : (prefixWord ++ tailWord_2630435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630435).length < 2 ^ (prefixWord ++ tailWord_2630435).sum := by decide
  have hdescent : baseEnd_2630435 < baseStart_2630435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630454 : List Nat := [5, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2630454 : Nat := 118140960795 + 2630454 * 2 ^ 59
def prefixEnd_2630454 : Nat := 4983230072969 + 3 ^ 40 * 2630454 * 2
def baseEnd_2630454 : Nat := 100050906780885671876131

theorem tailTrace_2630454 : CollatzResearch.WordTrace tailWord_2630454 prefixEnd_2630454 100050906780885671876131 := by
  unfold tailWord_2630454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996283700770117413876651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63960359474881252414684277 5996283700770117413876651)
  ·
    refine ⟨8994425551155176120814977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996283700770117413876651 8994425551155176120814977)
    ·
      refine ⟨6745819163366382090611233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8994425551155176120814977 6745819163366382090611233)
      ·
        refine ⟨5059364372524786567958425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6745819163366382090611233 5059364372524786567958425)
        ·
          refine ⟨3794523279393589925968819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5059364372524786567958425 3794523279393589925968819)
          ·
            refine ⟨5691784919090384888953229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794523279393589925968819 5691784919090384888953229)
            ·
              refine ⟨2134419344658894333357461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5691784919090384888953229 2134419344658894333357461)
              ·
                refine ⟨100050906780885671876131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2134419344658894333357461 100050906780885671876131)
                ·
                  rfl

theorem cell22_2630454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2630454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630454 prefixEnd_2630454 := by exact prefixLift 2630454
  have htrace : WordTrace (prefixWord ++ tailWord_2630454) baseStart_2630454 baseEnd_2630454 := by
    simpa [prefixWord, tailWord_2630454, baseEnd_2630454] using wordTrace_append hprefix tailTrace_2630454
  have hstable : (prefixWord ++ tailWord_2630454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630454).length < 2 ^ (prefixWord ++ tailWord_2630454).sum := by decide
  have hdescent : baseEnd_2630454 < baseStart_2630454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630525 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2630525 : Nat := 118140960795 + 2630525 * 2 ^ 59
def prefixEnd_2630525 : Nat := 4983230072969 + 3 ^ 40 * 2630525 * 2
def baseEnd_2630525 : Nat := 900482465778950528359961

theorem tailTrace_2630525 : CollatzResearch.WordTrace tailWord_2630525 prefixEnd_2630525 900482465778950528359961 := by
  unfold tailWord_2630525
  simp only [CollatzResearch.WordTrace]
  refine ⟨95943128795064657747861029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63962085863376438498574019 95943128795064657747861029)
  ·
    refine ⟨17989336649074623327723943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95943128795064657747861029 17989336649074623327723943)
    ·
      refine ⟨26984004973611934991585915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17989336649074623327723943 26984004973611934991585915)
      ·
        refine ⟨40476007460417902487378873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26984004973611934991585915 40476007460417902487378873)
        ·
          refine ⟨30357005595313426865534155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40476007460417902487378873 30357005595313426865534155)
          ·
            refine ⟨45535508392970140298301233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30357005595313426865534155 45535508392970140298301233)
            ·
              refine ⟨34151631294727605223725925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45535508392970140298301233 34151631294727605223725925)
              ·
                refine ⟨6403430867761425979448611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34151631294727605223725925 6403430867761425979448611)
                ·
                  refine ⟨9605146301642138969172917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403430867761425979448611 9605146301642138969172917)
                  ·
                    refine ⟨900482465778950528359961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9605146301642138969172917 900482465778950528359961)
                    ·
                      rfl

theorem cell22_2630525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2630525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630525 prefixEnd_2630525 := by exact prefixLift 2630525
  have htrace : WordTrace (prefixWord ++ tailWord_2630525) baseStart_2630525 baseEnd_2630525 := by
    simpa [prefixWord, tailWord_2630525, baseEnd_2630525] using wordTrace_append hprefix tailTrace_2630525
  have hstable : (prefixWord ++ tailWord_2630525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630525).length < 2 ^ (prefixWord ++ tailWord_2630525).sum := by decide
  have hdescent : baseEnd_2630525 < baseStart_2630525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630527 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 4]
def baseStart_2630527 : Nat := 118140960795 + 2630527 * 2 ^ 59
def prefixEnd_2630527 : Nat := 4983230072969 + 3 ^ 40 * 2630527 * 2
def baseEnd_2630527 : Nat := 300161050139941063269985

theorem tailTrace_2630527 : CollatzResearch.WordTrace tailWord_2630527 prefixEnd_2630527 300161050139941063269985 := by
  unfold tailWord_2630527
  simp only [CollatzResearch.WordTrace]
  refine ⟨95943201741057412089433835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63962134494038274726289223 95943201741057412089433835)
  ·
    refine ⟨143914802611586118134150753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95943201741057412089433835 143914802611586118134150753)
    ·
      refine ⟨107936101958689588600613065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143914802611586118134150753 107936101958689588600613065)
      ·
        refine ⟨80952076469017191450459799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107936101958689588600613065 80952076469017191450459799)
        ·
          refine ⟨121428114703525787175689699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80952076469017191450459799 121428114703525787175689699)
          ·
            refine ⟨182142172055288680763534549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121428114703525787175689699 182142172055288680763534549)
            ·
              refine ⟨4268957157545828455395341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182142172055288680763534549 4268957157545828455395341)
              ·
                refine ⟨1600858934079685670773253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4268957157545828455395341 1600858934079685670773253)
                ·
                  refine ⟨300161050139941063269985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600858934079685670773253 300161050139941063269985)
                  ·
                    rfl

theorem cell22_2630527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 4].length) (baseStart_2630527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630527 prefixEnd_2630527 := by exact prefixLift 2630527
  have htrace : WordTrace (prefixWord ++ tailWord_2630527) baseStart_2630527 baseEnd_2630527 := by
    simpa [prefixWord, tailWord_2630527, baseEnd_2630527] using wordTrace_append hprefix tailTrace_2630527
  have hstable : (prefixWord ++ tailWord_2630527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630527).length < 2 ^ (prefixWord ++ tailWord_2630527).sum := by decide
  have hdescent : baseEnd_2630527 < baseStart_2630527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630540 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_2630540 : Nat := 118140960795 + 2630540 * 2 ^ 59
def prefixEnd_2630540 : Nat := 4983230072969 + 3 ^ 40 * 2630540 * 2
def baseEnd_2630540 : Nat := 900487600585495489234915

theorem tailTrace_2630540 : CollatzResearch.WordTrace tailWord_2630540 prefixEnd_2630540 900487600585495489234915 := by
  unfold tailWord_2630540
  simp only [CollatzResearch.WordTrace]
  refine ⟨47971837945005157654828537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63962450593340210206438049 47971837945005157654828537)
  ·
    refine ⟨35978878458753868241121403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47971837945005157654828537 35978878458753868241121403)
    ·
      refine ⟨53968317688130802361682105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35978878458753868241121403 53968317688130802361682105)
      ·
        refine ⟨40476238266098101771261579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53968317688130802361682105 40476238266098101771261579)
        ·
          refine ⟨60714357399147152656892369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40476238266098101771261579 60714357399147152656892369)
          ·
            refine ⟨45535768049360364492669277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60714357399147152656892369 45535768049360364492669277)
            ·
              refine ⟨17075913018510136684750979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45535768049360364492669277 17075913018510136684750979)
              ·
                refine ⟨25613869527765205027126469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17075913018510136684750979 25613869527765205027126469)
                ·
                  refine ⟨4802600536455975942586213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25613869527765205027126469 4802600536455975942586213)
                  ·
                    refine ⟨900487600585495489234915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802600536455975942586213 900487600585495489234915)
                    ·
                      rfl

theorem cell22_2630540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_2630540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630540 prefixEnd_2630540 := by exact prefixLift 2630540
  have htrace : WordTrace (prefixWord ++ tailWord_2630540) baseStart_2630540 baseEnd_2630540 := by
    simpa [prefixWord, tailWord_2630540, baseEnd_2630540] using wordTrace_append hprefix tailTrace_2630540
  have hstable : (prefixWord ++ tailWord_2630540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630540).length < 2 ^ (prefixWord ++ tailWord_2630540).sum := by decide
  have hdescent : baseEnd_2630540 < baseStart_2630540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630559 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 2, 3]
def baseStart_2630559 : Nat := 118140960795 + 2630559 * 2 ^ 59
def prefixEnd_2630559 : Nat := 4983230072969 + 3 ^ 40 * 2630559 * 2
def baseEnd_2630559 : Nat := 900494104673785773009857

theorem tailTrace_2630559 : CollatzResearch.WordTrace tailWord_2630559 prefixEnd_2630559 900494104673785773009857 := by
  unfold tailWord_2630559
  simp only [CollatzResearch.WordTrace]
  refine ⟨95944368876941481554598731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63962912584627654369732487 95944368876941481554598731)
  ·
    refine ⟨143916553315412222331898097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95944368876941481554598731 143916553315412222331898097)
    ·
      refine ⟨107937414986559166748923573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143916553315412222331898097 107937414986559166748923573)
      ·
        refine ⟨10119132654989921882711585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107937414986559166748923573 10119132654989921882711585)
        ·
          refine ⟨7589349491242441412033689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10119132654989921882711585 7589349491242441412033689)
          ·
            refine ⟨5692012118431831059025267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7589349491242441412033689 5692012118431831059025267)
            ·
              refine ⟨8538018177647746588537901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5692012118431831059025267 8538018177647746588537901)
              ·
                refine ⟨3201756816617904970701713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8538018177647746588537901 3201756816617904970701713)
                ·
                  refine ⟨2401317612463428728026285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201756816617904970701713 2401317612463428728026285)
                  ·
                    refine ⟨900494104673785773009857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401317612463428728026285 900494104673785773009857)
                    ·
                      rfl

theorem cell22_2630559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_2630559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630559 prefixEnd_2630559 := by exact prefixLift 2630559
  have htrace : WordTrace (prefixWord ++ tailWord_2630559) baseStart_2630559 baseEnd_2630559 := by
    simpa [prefixWord, tailWord_2630559, baseEnd_2630559] using wordTrace_append hprefix tailTrace_2630559
  have hstable : (prefixWord ++ tailWord_2630559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630559).length < 2 ^ (prefixWord ++ tailWord_2630559).sum := by decide
  have hdescent : baseEnd_2630559 < baseStart_2630559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630617 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 5]
def baseStart_2630617 : Nat := 118140960795 + 2630617 * 2 ^ 59
def prefixEnd_2630617 : Nat := 4983230072969 + 3 ^ 40 * 2630617 * 2
def baseEnd_2630617 : Nat := 300171319753030985019893

theorem tailTrace_2630617 : CollatzResearch.WordTrace tailWord_2630617 prefixEnd_2630617 300171319753030985019893 := by
  unfold tailWord_2630617
  simp only [CollatzResearch.WordTrace]
  refine ⟨95946484310731357460210105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63964322873820904973473403 95946484310731357460210105)
  ·
    refine ⟨71959863233048518095157579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95946484310731357460210105 71959863233048518095157579)
    ·
      refine ⟨107939794849572777142736369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71959863233048518095157579 107939794849572777142736369)
      ·
        refine ⟨80954846137179582857052277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107939794849572777142736369 80954846137179582857052277)
        ·
          refine ⟨7589516825360585892848651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80954846137179582857052277 7589516825360585892848651)
          ·
            refine ⟨11384275238040878839272977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589516825360585892848651 11384275238040878839272977)
            ·
              refine ⟨8538206428530659129454733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384275238040878839272977 8538206428530659129454733)
              ·
                refine ⟨3201827410698997173545525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8538206428530659129454733 3201827410698997173545525)
                ·
                  refine ⟨300171319753030985019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201827410698997173545525 300171319753030985019893)
                  ·
                    rfl

theorem cell22_2630617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_2630617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630617 prefixEnd_2630617 := by exact prefixLift 2630617
  have htrace : WordTrace (prefixWord ++ tailWord_2630617) baseStart_2630617 baseEnd_2630617 := by
    simpa [prefixWord, tailWord_2630617, baseEnd_2630617] using wordTrace_append hprefix tailTrace_2630617
  have hstable : (prefixWord ++ tailWord_2630617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630617).length < 2 ^ (prefixWord ++ tailWord_2630617).sum := by decide
  have hdescent : baseEnd_2630617 < baseStart_2630617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630638 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2630638 : Nat := 118140960795 + 2630638 * 2 ^ 59
def prefixEnd_2630638 : Nat := 4983230072969 + 3 ^ 40 * 2630638 * 2
def baseEnd_2630638 : Nat := 900521147988255900284615

theorem tailTrace_2630638 : CollatzResearch.WordTrace tailWord_2630638 prefixEnd_2630638 900521147988255900284615 := by
  unfold tailWord_2630638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993406280456909755840571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63964833495770185364483045 11993406280456909755840571)
  ·
    refine ⟨17990109420685364633760857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993406280456909755840571 17990109420685364633760857)
    ·
      refine ⟨13492582065514023475320643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17990109420685364633760857 13492582065514023475320643)
      ·
        refine ⟨20238873098271035212980965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13492582065514023475320643 20238873098271035212980965)
        ·
          refine ⟨3794788705925819102433931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20238873098271035212980965 3794788705925819102433931)
          ·
            refine ⟨5692183058888728653650897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794788705925819102433931 5692183058888728653650897)
            ·
              refine ⟨4269137294166546490238173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692183058888728653650897 4269137294166546490238173)
              ·
                refine ⟨1600926485312454933839315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4269137294166546490238173 1600926485312454933839315)
                ·
                  refine ⟨2401389727968682400758973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600926485312454933839315 2401389727968682400758973)
                  ·
                    refine ⟨900521147988255900284615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401389727968682400758973 900521147988255900284615)
                    ·
                      rfl

theorem cell22_2630638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2630638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630638 prefixEnd_2630638 := by exact prefixLift 2630638
  have htrace : WordTrace (prefixWord ++ tailWord_2630638) baseStart_2630638 baseEnd_2630638 := by
    simpa [prefixWord, tailWord_2630638, baseEnd_2630638] using wordTrace_append hprefix tailTrace_2630638
  have hstable : (prefixWord ++ tailWord_2630638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630638).length < 2 ^ (prefixWord ++ tailWord_2630638).sum := by decide
  have hdescent : baseEnd_2630638 < baseStart_2630638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630644 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2630644 : Nat := 118140960795 + 2630644 * 2 ^ 59
def prefixEnd_2630644 : Nat := 4983230072969 + 3 ^ 40 * 2630644 * 2
def baseEnd_2630644 : Nat := 900523201910873884634597

theorem tailTrace_2630644 : CollatzResearch.WordTrace tailWord_2630644 prefixEnd_2630644 900523201910873884634597 := by
  unfold tailWord_2630644
  simp only [CollatzResearch.WordTrace]
  refine ⟨47973734540816770535721493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63964979387755694047628657 47973734540816770535721493)
  ·
    refine ⟨2248768806600786118861945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47973734540816770535721493 2248768806600786118861945)
    ·
      refine ⟨1686576604950589589146459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2248768806600786118861945 1686576604950589589146459)
      ·
        refine ⟨2529864907425884383719689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686576604950589589146459 2529864907425884383719689)
        ·
          refine ⟨1897398680569413287789767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2529864907425884383719689 1897398680569413287789767)
          ·
            refine ⟨2846098020854119931684651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897398680569413287789767 2846098020854119931684651)
            ·
              refine ⟨4269147031281179897526977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846098020854119931684651 4269147031281179897526977)
              ·
                refine ⟨3201860273460884923145233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269147031281179897526977 3201860273460884923145233)
                ·
                  refine ⟨2401395205095663692358925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201860273460884923145233 2401395205095663692358925)
                  ·
                    refine ⟨900523201910873884634597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401395205095663692358925 900523201910873884634597)
                    ·
                      rfl

theorem cell22_2630644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2630644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630644 prefixEnd_2630644 := by exact prefixLift 2630644
  have htrace : WordTrace (prefixWord ++ tailWord_2630644) baseStart_2630644 baseEnd_2630644 := by
    simpa [prefixWord, tailWord_2630644, baseEnd_2630644] using wordTrace_append hprefix tailTrace_2630644
  have hstable : (prefixWord ++ tailWord_2630644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630644).length < 2 ^ (prefixWord ++ tailWord_2630644).sum := by decide
  have hdescent : baseEnd_2630644 < baseStart_2630644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630756 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_2630756 : Nat := 118140960795 + 2630756 * 2 ^ 59
def prefixEnd_2630756 : Nat := 4983230072969 + 3 ^ 40 * 2630756 * 2
def baseEnd_2630756 : Nat := 900561541799742925834253

theorem tailTrace_2630756 : CollatzResearch.WordTrace tailWord_2630756 prefixEnd_2630756 900561541799742925834253 := by
  unfold tailWord_2630756
  simp only [CollatzResearch.WordTrace]
  refine ⟨47975777028613892099760061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63967702704818522799680081 47975777028613892099760061)
  ·
    refine ⟨17990916385730209537410023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47975777028613892099760061 17990916385730209537410023)
    ·
      refine ⟨26986374578595314306115035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17990916385730209537410023 26986374578595314306115035)
      ·
        refine ⟨40479561867892971459172553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26986374578595314306115035 40479561867892971459172553)
        ·
          refine ⟨30359671400919728594379415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40479561867892971459172553 30359671400919728594379415)
          ·
            refine ⟨45539507101379592891569123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30359671400919728594379415 45539507101379592891569123)
            ·
              refine ⟨68309260652069389337353685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45539507101379592891569123 68309260652069389337353685)
              ·
                refine ⟨1600998296532876312594227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68309260652069389337353685 1600998296532876312594227)
                ·
                  refine ⟨2401497444799314468891341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600998296532876312594227 2401497444799314468891341)
                  ·
                    refine ⟨900561541799742925834253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401497444799314468891341 900561541799742925834253)
                    ·
                      rfl

theorem cell22_2630756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_2630756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630756 prefixEnd_2630756 := by exact prefixLift 2630756
  have htrace : WordTrace (prefixWord ++ tailWord_2630756) baseStart_2630756 baseEnd_2630756 := by
    simpa [prefixWord, tailWord_2630756, baseEnd_2630756] using wordTrace_append hprefix tailTrace_2630756
  have hstable : (prefixWord ++ tailWord_2630756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630756).length < 2 ^ (prefixWord ++ tailWord_2630756).sum := by decide
  have hdescent : baseEnd_2630756 < baseStart_2630756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630767 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_2630767 : Nat := 118140960795 + 2630767 * 2 ^ 59
def prefixEnd_2630767 : Nat := 4983230072969 + 3 ^ 40 * 2630767 * 2
def baseEnd_2630767 : Nat := 900565307324542563809219

theorem tailTrace_2630767 : CollatzResearch.WordTrace tailWord_2630767 prefixEnd_2630767 900565307324542563809219 := by
  unfold tailWord_2630767
  simp only [CollatzResearch.WordTrace]
  refine ⟨95951955260187933078170555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63967970173458622052113703 95951955260187933078170555)
  ·
    refine ⟨143927932890281899617255833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95951955260187933078170555 143927932890281899617255833)
    ·
      refine ⟨107945949667711424712941875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143927932890281899617255833 107945949667711424712941875)
      ·
        refine ⟨161918924501567137069412813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107945949667711424712941875 161918924501567137069412813)
        ·
          refine ⟨60719596688087676401029805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161918924501567137069412813 60719596688087676401029805)
          ·
            refine ⟨22769848758032878650386177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60719596688087676401029805 22769848758032878650386177)
            ·
              refine ⟨17077386568524658987789633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22769848758032878650386177 17077386568524658987789633)
              ·
                refine ⟨12808039926393494240842225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17077386568524658987789633 12808039926393494240842225)
                ·
                  refine ⟨9606029944795120680631669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12808039926393494240842225 9606029944795120680631669)
                  ·
                    refine ⟨900565307324542563809219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9606029944795120680631669 900565307324542563809219)
                    ·
                      rfl

theorem cell22_2630767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_2630767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630767 prefixEnd_2630767 := by exact prefixLift 2630767
  have htrace : WordTrace (prefixWord ++ tailWord_2630767) baseStart_2630767 baseEnd_2630767 := by
    simpa [prefixWord, tailWord_2630767, baseEnd_2630767] using wordTrace_append hprefix tailTrace_2630767
  have hstable : (prefixWord ++ tailWord_2630767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630767).length < 2 ^ (prefixWord ++ tailWord_2630767).sum := by decide
  have hdescent : baseEnd_2630767 < baseStart_2630767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630842 : List Nat := [3, 1, 1, 1, 2, 2, 1, 11]
def baseStart_2630842 : Nat := 118140960795 + 2630842 * 2 ^ 59
def prefixEnd_2630842 : Nat := 4983230072969 + 3 ^ 40 * 2630842 * 2
def baseEnd_2630842 : Nat := 100065664595251929798221

theorem tailTrace_2630842 : CollatzResearch.WordTrace tailWord_2630842 prefixEnd_2630842 100065664595251929798221 := by
  unfold tailWord_2630842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988672683729055221787695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63969793823277480591433853 23988672683729055221787695)
  ·
    refine ⟨35983009025593582832681543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23988672683729055221787695 35983009025593582832681543)
    ·
      refine ⟨53974513538390374249022315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35983009025593582832681543 53974513538390374249022315)
      ·
        refine ⟨80961770307585561373533473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53974513538390374249022315 80961770307585561373533473)
        ·
          refine ⟨60721327730689171030150105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80961770307585561373533473 60721327730689171030150105)
          ·
            refine ⟨45540995798016878272612579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60721327730689171030150105 45540995798016878272612579)
            ·
              refine ⟨68311493697025317408918869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45540995798016878272612579 68311493697025317408918869)
              ·
                refine ⟨100065664595251929798221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 68311493697025317408918869 100065664595251929798221)
                ·
                  rfl

theorem cell22_2630842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_2630842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630842 prefixEnd_2630842 := by exact prefixLift 2630842
  have htrace : WordTrace (prefixWord ++ tailWord_2630842) baseStart_2630842 baseEnd_2630842 := by
    simpa [prefixWord, tailWord_2630842, baseEnd_2630842] using wordTrace_append hprefix tailTrace_2630842
  have hstable : (prefixWord ++ tailWord_2630842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630842).length < 2 ^ (prefixWord ++ tailWord_2630842).sum := by decide
  have hdescent : baseEnd_2630842 < baseStart_2630842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630844 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2630844 : Nat := 118140960795 + 2630844 * 2 ^ 59
def prefixEnd_2630844 : Nat := 4983230072969 + 3 ^ 40 * 2630844 * 2
def baseEnd_2630844 : Nat := 900591665998140029633983

theorem tailTrace_2630844 : CollatzResearch.WordTrace tailWord_2630844 prefixEnd_2630844 900591665998140029633983 := by
  unfold tailWord_2630844
  simp only [CollatzResearch.WordTrace]
  refine ⟨47977381840454487614361793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63969842453939316819149057 47977381840454487614361793)
  ·
    refine ⟨35983036380340865710771345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47977381840454487614361793 35983036380340865710771345)
    ·
      refine ⟨26987277285255649283078509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35983036380340865710771345 26987277285255649283078509)
      ·
        refine ⟨10120228981970868481154441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26987277285255649283078509 10120228981970868481154441)
        ·
          refine ⟨7590171736478151360865831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10120228981970868481154441 7590171736478151360865831)
          ·
            refine ⟨11385257604717227041298747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7590171736478151360865831 11385257604717227041298747)
            ·
              refine ⟨17077886407075840561948121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11385257604717227041298747 17077886407075840561948121)
              ·
                refine ⟨12808414805306880421461091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17077886407075840561948121 12808414805306880421461091)
                ·
                  refine ⟨19212622207960320632191637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12808414805306880421461091 19212622207960320632191637)
                  ·
                    refine ⟨900591665998140029633983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19212622207960320632191637 900591665998140029633983)
                    ·
                      rfl

theorem cell22_2630844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2630844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630844 prefixEnd_2630844 := by exact prefixLift 2630844
  have htrace : WordTrace (prefixWord ++ tailWord_2630844) baseStart_2630844 baseEnd_2630844 := by
    simpa [prefixWord, tailWord_2630844, baseEnd_2630844] using wordTrace_append hprefix tailTrace_2630844
  have hstable : (prefixWord ++ tailWord_2630844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630844).length < 2 ^ (prefixWord ++ tailWord_2630844).sum := by decide
  have hdescent : baseEnd_2630844 < baseStart_2630844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630846 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2630846 : Nat := 118140960795 + 2630846 * 2 ^ 59
def prefixEnd_2630846 : Nat := 4983230072969 + 3 ^ 40 * 2630846 * 2
def baseEnd_2630846 : Nat := 900592350639012691083977

theorem tailTrace_2630846 : CollatzResearch.WordTrace tailWord_2630846 prefixEnd_2630846 900592350639012691083977 := by
  unfold tailWord_2630846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11994354578362716196287049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63969891084601153046864261 11994354578362716196287049)
  ·
    refine ⟨8995765933772037147215287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11994354578362716196287049 8995765933772037147215287)
    ·
      refine ⟨13493648900658055720822931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8995765933772037147215287 13493648900658055720822931)
      ·
        refine ⟨20240473350987083581234397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493648900658055720822931 20240473350987083581234397)
        ·
          refine ⟨7590177506620156342962899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20240473350987083581234397 7590177506620156342962899)
          ·
            refine ⟨11385266259930234514444349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7590177506620156342962899 11385266259930234514444349)
            ·
              refine ⟨4269474847473837942916631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11385266259930234514444349 4269474847473837942916631)
              ·
                refine ⟨6404212271210756914374947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269474847473837942916631 6404212271210756914374947)
                ·
                  refine ⟨9606318406816135371562421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6404212271210756914374947 9606318406816135371562421)
                  ·
                    refine ⟨900592350639012691083977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9606318406816135371562421 900592350639012691083977)
                    ·
                      rfl

theorem cell22_2630846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2630846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630846 prefixEnd_2630846 := by exact prefixLift 2630846
  have htrace : WordTrace (prefixWord ++ tailWord_2630846) baseStart_2630846 baseEnd_2630846 := by
    simpa [prefixWord, tailWord_2630846, baseEnd_2630846] using wordTrace_append hprefix tailTrace_2630846
  have hstable : (prefixWord ++ tailWord_2630846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630846).length < 2 ^ (prefixWord ++ tailWord_2630846).sum := by decide
  have hdescent : baseEnd_2630846 < baseStart_2630846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630891 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 3, 3]
def baseStart_2630891 : Nat := 118140960795 + 2630891 * 2 ^ 59
def prefixEnd_2630891 : Nat := 4983230072969 + 3 ^ 40 * 2630891 * 2
def baseEnd_2630891 : Nat := 900607755058647573708839

theorem tailTrace_2630891 : CollatzResearch.WordTrace tailWord_2630891 prefixEnd_2630891 900607755058647573708839 := by
  unfold tailWord_2630891
  simp only [CollatzResearch.WordTrace]
  refine ⟨95956477911738702255684527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63970985274492468170456351 95956477911738702255684527)
  ·
    refine ⟨143934716867608053383526791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95956477911738702255684527 143934716867608053383526791)
    ·
      refine ⟨215902075301412080075290187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143934716867608053383526791 215902075301412080075290187)
      ·
        refine ⟨323853112952118120112935281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215902075301412080075290187 323853112952118120112935281)
        ·
          refine ⟨242889834714088590084701461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323853112952118120112935281 242889834714088590084701461)
          ·
            refine ⟨11385461002222902660220381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 242889834714088590084701461 11385461002222902660220381)
            ·
              refine ⟨4269547875833588497582643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11385461002222902660220381 4269547875833588497582643)
              ·
                refine ⟨6404321813750382746373965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269547875833588497582643 6404321813750382746373965)
                ·
                  refine ⟨2401620680156393529890237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6404321813750382746373965 2401620680156393529890237)
                  ·
                    refine ⟨900607755058647573708839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401620680156393529890237 900607755058647573708839)
                    ·
                      rfl

theorem cell22_2630891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3].length) (baseStart_2630891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630891 prefixEnd_2630891 := by exact prefixLift 2630891
  have htrace : WordTrace (prefixWord ++ tailWord_2630891) baseStart_2630891 baseEnd_2630891 := by
    simpa [prefixWord, tailWord_2630891, baseEnd_2630891] using wordTrace_append hprefix tailTrace_2630891
  have hstable : (prefixWord ++ tailWord_2630891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630891).length < 2 ^ (prefixWord ++ tailWord_2630891).sum := by decide
  have hdescent : baseEnd_2630891 < baseStart_2630891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630983 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 4]
def baseStart_2630983 : Nat := 118140960795 + 2630983 * 2 ^ 59
def prefixEnd_2630983 : Nat := 4983230072969 + 3 ^ 40 * 2630983 * 2
def baseEnd_2630983 : Nat := 300213082846263333469519

theorem tailTrace_2630983 : CollatzResearch.WordTrace tailWord_2630983 prefixEnd_2630983 300213082846263333469519 := by
  unfold tailWord_2630983
  simp only [CollatzResearch.WordTrace]
  refine ⟨95959833427405401968033603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63973222284936934645355735 95959833427405401968033603)
  ·
    refine ⟨143939750141108102952050405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95959833427405401968033603 143939750141108102952050405)
    ·
      refine ⟨26988703151457769303509451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143939750141108102952050405 26988703151457769303509451)
      ·
        refine ⟨40483054727186653955264177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26988703151457769303509451 40483054727186653955264177)
        ·
          refine ⟨30362291045389990466448133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40483054727186653955264177 30362291045389990466448133)
          ·
            refine ⟨5692929571010623212459025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30362291045389990466448133 5692929571010623212459025)
            ·
              refine ⟨4269697178257967409344269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692929571010623212459025 4269697178257967409344269)
              ·
                refine ⟨1601136441846737778504101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4269697178257967409344269 1601136441846737778504101)
                ·
                  refine ⟨300213082846263333469519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601136441846737778504101 300213082846263333469519)
                  ·
                    rfl

theorem cell22_2630983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 4].length) (baseStart_2630983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630983 prefixEnd_2630983 := by exact prefixLift 2630983
  have htrace : WordTrace (prefixWord ++ tailWord_2630983) baseStart_2630983 baseEnd_2630983 := by
    simpa [prefixWord, tailWord_2630983, baseEnd_2630983] using wordTrace_append hprefix tailTrace_2630983
  have hstable : (prefixWord ++ tailWord_2630983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630983).length < 2 ^ (prefixWord ++ tailWord_2630983).sum := by decide
  have hdescent : baseEnd_2630983 < baseStart_2630983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630996 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2630996 : Nat := 118140960795 + 2630996 * 2 ^ 59
def prefixEnd_2630996 : Nat := 4983230072969 + 3 ^ 40 * 2630996 * 2
def baseEnd_2630996 : Nat := 900643698704462299833517

theorem tailTrace_2630996 : CollatzResearch.WordTrace tailWord_2630996 prefixEnd_2630996 900643698704462299833517 := by
  unfold tailWord_2630996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47980153788179152594128421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63973538384238870125504561 47980153788179152594128421)
  ·
    refine ⟨8996278835283591111399079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47980153788179152594128421 8996278835283591111399079)
    ·
      refine ⟨13494418252925386667098619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8996278835283591111399079 13494418252925386667098619)
      ·
        refine ⟨20241627379388080000647929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13494418252925386667098619 20241627379388080000647929)
        ·
          refine ⟨15181220534541060000485947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20241627379388080000647929 15181220534541060000485947)
          ·
            refine ⟨22771830801811590000728921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15181220534541060000485947 22771830801811590000728921)
            ·
              refine ⟨17078873101358692500546691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22771830801811590000728921 17078873101358692500546691)
              ·
                refine ⟨25618309652038038750820037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17078873101358692500546691 25618309652038038750820037)
                ·
                  refine ⟨4803433059757132265778757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25618309652038038750820037 4803433059757132265778757)
                  ·
                    refine ⟨900643698704462299833517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4803433059757132265778757 900643698704462299833517)
                    ·
                      rfl

theorem cell22_2630996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2630996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2630996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2630996 prefixEnd_2630996 := by exact prefixLift 2630996
  have htrace : WordTrace (prefixWord ++ tailWord_2630996) baseStart_2630996 baseEnd_2630996 := by
    simpa [prefixWord, tailWord_2630996, baseEnd_2630996] using wordTrace_append hprefix tailTrace_2630996
  have hstable : (prefixWord ++ tailWord_2630996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630996).length < 2 ^ (prefixWord ++ tailWord_2630996).sum := by decide
  have hdescent : baseEnd_2630996 < baseStart_2630996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631015 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2631015 : Nat := 118140960795 + 2631015 * 2 ^ 59
def prefixEnd_2631015 : Nat := 4983230072969 + 3 ^ 40 * 2631015 * 2
def baseEnd_2631015 : Nat := 900650202792752583608459

theorem tailTrace_2631015 : CollatzResearch.WordTrace tailWord_2631015 prefixEnd_2631015 900650202792752583608459 := by
  unfold tailWord_2631015
  simp only [CollatzResearch.WordTrace]
  refine ⟨95961000563289471433198499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63974000375526314288798999 95961000563289471433198499)
  ·
    refine ⟨143941500844934207149797749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95961000563289471433198499 143941500844934207149797749)
    ·
      refine ⟨13494515704212581920293539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143941500844934207149797749 13494515704212581920293539)
      ·
        refine ⟨20241773556318872880440309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13494515704212581920293539 20241773556318872880440309)
        ·
          refine ⟨1897666270904894332541279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20241773556318872880440309 1897666270904894332541279)
          ·
            refine ⟨2846499406357341498811919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897666270904894332541279 2846499406357341498811919)
            ·
              refine ⟨4269749109536012248217879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846499406357341498811919 4269749109536012248217879)
              ·
                refine ⟨6404623664304018372326819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269749109536012248217879 6404623664304018372326819)
                ·
                  refine ⟨9606935496456027558490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6404623664304018372326819 9606935496456027558490229)
                  ·
                    refine ⟨900650202792752583608459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9606935496456027558490229 900650202792752583608459)
                    ·
                      rfl

theorem cell22_2631015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2631015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631015 prefixEnd_2631015 := by exact prefixLift 2631015
  have htrace : WordTrace (prefixWord ++ tailWord_2631015) baseStart_2631015 baseEnd_2631015 := by
    simpa [prefixWord, tailWord_2631015, baseEnd_2631015] using wordTrace_append hprefix tailTrace_2631015
  have hstable : (prefixWord ++ tailWord_2631015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631015).length < 2 ^ (prefixWord ++ tailWord_2631015).sum := by decide
  have hdescent : baseEnd_2631015 < baseStart_2631015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631060 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2631060 : Nat := 118140960795 + 2631060 * 2 ^ 59
def prefixEnd_2631060 : Nat := 4983230072969 + 3 ^ 40 * 2631060 * 2
def baseEnd_2631060 : Nat := 900665607212387466233321

theorem tailTrace_2631060 : CollatzResearch.WordTrace tailWord_2631060 prefixEnd_2631060 900665607212387466233321 := by
  unfold tailWord_2631060
  simp only [CollatzResearch.WordTrace]
  refine ⟨47981320924063222059293317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63975094565417629412391089 47981320924063222059293317)
  ·
    refine ⟨8996497673261854136117497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47981320924063222059293317 8996497673261854136117497)
    ·
      refine ⟨6747373254946390602088123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8996497673261854136117497 6747373254946390602088123)
      ·
        refine ⟨10121059882419585903132185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6747373254946390602088123 10121059882419585903132185)
        ·
          refine ⟨7590794911814689427349139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10121059882419585903132185 7590794911814689427349139)
          ·
            refine ⟨11386192367722034141023709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7590794911814689427349139 11386192367722034141023709)
            ·
              refine ⟨4269822137895762802883891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11386192367722034141023709 4269822137895762802883891)
              ·
                refine ⟨6404733206843644204325837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269822137895762802883891 6404733206843644204325837)
                ·
                  refine ⟨2401774952566366576622189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6404733206843644204325837 2401774952566366576622189)
                  ·
                    refine ⟨900665607212387466233321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401774952566366576622189 900665607212387466233321)
                    ·
                      rfl

theorem cell22_2631060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2631060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631060 prefixEnd_2631060 := by exact prefixLift 2631060
  have htrace : WordTrace (prefixWord ++ tailWord_2631060) baseStart_2631060 baseEnd_2631060 := by
    simpa [prefixWord, tailWord_2631060, baseEnd_2631060] using wordTrace_append hprefix tailTrace_2631060
  have hstable : (prefixWord ++ tailWord_2631060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631060).length < 2 ^ (prefixWord ++ tailWord_2631060).sum := by decide
  have hdescent : baseEnd_2631060 < baseStart_2631060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631133 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2631133 : Nat := 118140960795 + 2631133 * 2 ^ 59
def prefixEnd_2631133 : Nat := 4983230072969 + 3 ^ 40 * 2631133 * 2
def baseEnd_2631133 : Nat := 900690596604239609158097

theorem tailTrace_2631133 : CollatzResearch.WordTrace tailWord_2631133 prefixEnd_2631133 900690596604239609158097 := by
  unfold tailWord_2631133
  simp only [CollatzResearch.WordTrace]
  refine ⟨95965304376861977585994053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63976869584574651723996035 95965304376861977585994053)
  ·
    refine ⟨17993494570661620797373885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95965304376861977585994053 17993494570661620797373885)
    ·
      refine ⟨6747560463998107799015207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17993494570661620797373885 6747560463998107799015207)
      ·
        refine ⟨10121340695997161698522811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6747560463998107799015207 10121340695997161698522811)
        ·
          refine ⟨15182011043995742547784217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10121340695997161698522811 15182011043995742547784217)
          ·
            refine ⟨11386508282996806910838163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15182011043995742547784217 11386508282996806910838163)
            ·
              refine ⟨17079762424495210366257245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11386508282996806910838163 17079762424495210366257245)
              ·
                refine ⟨6404910909185703887346467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17079762424495210366257245 6404910909185703887346467)
                ·
                  refine ⟨9607366363778555831019701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6404910909185703887346467 9607366363778555831019701)
                  ·
                    refine ⟨900690596604239609158097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9607366363778555831019701 900690596604239609158097)
                    ·
                      rfl

theorem cell22_2631133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2631133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631133 prefixEnd_2631133 := by exact prefixLift 2631133
  have htrace : WordTrace (prefixWord ++ tailWord_2631133) baseStart_2631133 baseEnd_2631133 := by
    simpa [prefixWord, tailWord_2631133, baseEnd_2631133] using wordTrace_append hprefix tailTrace_2631133
  have hstable : (prefixWord ++ tailWord_2631133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631133).length < 2 ^ (prefixWord ++ tailWord_2631133).sum := by decide
  have hdescent : baseEnd_2631133 < baseStart_2631133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631176 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2631176 : Nat := 118140960795 + 2631176 * 2 ^ 59
def prefixEnd_2631176 : Nat := 4983230072969 + 3 ^ 40 * 2631176 * 2
def baseEnd_2631176 : Nat := 900705316383001830332965

theorem tailTrace_2631176 : CollatzResearch.WordTrace tailWord_2631176 prefixEnd_2631176 900705316383001830332965 := by
  unfold tailWord_2631176
  simp only [CollatzResearch.WordTrace]
  refine ⟨47983436357853097964904691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63977915143804130619872921 47983436357853097964904691)
  ·
    refine ⟨71975154536779646947357037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47983436357853097964904691 71975154536779646947357037)
    ·
      refine ⟨26990682951292367605258889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71975154536779646947357037 26990682951292367605258889)
      ·
        refine ⟨20243012213469275703944167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26990682951292367605258889 20243012213469275703944167)
        ·
          refine ⟨30364518320203913555916251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20243012213469275703944167 30364518320203913555916251)
          ·
            refine ⟨45546777480305870333874377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30364518320203913555916251 45546777480305870333874377)
            ·
              refine ⟨34160083110229402750405783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45546777480305870333874377 34160083110229402750405783)
              ·
                refine ⟨51240124665344104125608675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34160083110229402750405783 51240124665344104125608675)
                ·
                  refine ⟨76860186998016156188413013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51240124665344104125608675 76860186998016156188413013)
                  ·
                    refine ⟨900705316383001830332965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76860186998016156188413013 900705316383001830332965)
                    ·
                      rfl

theorem cell22_2631176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2631176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631176 prefixEnd_2631176 := by exact prefixLift 2631176
  have htrace : WordTrace (prefixWord ++ tailWord_2631176) baseStart_2631176 baseEnd_2631176 := by
    simpa [prefixWord, tailWord_2631176, baseEnd_2631176] using wordTrace_append hprefix tailTrace_2631176
  have hstable : (prefixWord ++ tailWord_2631176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631176).length < 2 ^ (prefixWord ++ tailWord_2631176).sum := by decide
  have hdescent : baseEnd_2631176 < baseStart_2631176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631229 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_2631229 : Nat := 118140960795 + 2631229 * 2 ^ 59
def prefixEnd_2631229 : Nat := 4983230072969 + 3 ^ 40 * 2631229 * 2
def baseEnd_2631229 : Nat := 900723459366127358757803

theorem tailTrace_2631229 : CollatzResearch.WordTrace tailWord_2631229 prefixEnd_2631229 900723459366127358757803 := by
  unfold tailWord_2631229
  simp only [CollatzResearch.WordTrace]
  refine ⟨95968805784514185981488741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63979203856342790654325827 95968805784514185981488741)
  ·
    refine ⟨17994151084596409871529139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95968805784514185981488741 17994151084596409871529139)
    ·
      refine ⟨26991226626894614807293709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17994151084596409871529139 26991226626894614807293709)
      ·
        refine ⟨10121709985085480552735141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26991226626894614807293709 10121709985085480552735141)
        ·
          refine ⟨1897820622203527603637839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10121709985085480552735141 1897820622203527603637839)
          ·
            refine ⟨2846730933305291405456759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897820622203527603637839 2846730933305291405456759)
            ·
              refine ⟨4270096399957937108185139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846730933305291405456759 4270096399957937108185139)
              ·
                refine ⟨6405144599936905662277709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270096399957937108185139 6405144599936905662277709)
                ·
                  refine ⟨2401929224976339623354141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6405144599936905662277709 2401929224976339623354141)
                  ·
                    refine ⟨900723459366127358757803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401929224976339623354141 900723459366127358757803)
                    ·
                      rfl

theorem cell22_2631229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_2631229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631229 prefixEnd_2631229 := by exact prefixLift 2631229
  have htrace : WordTrace (prefixWord ++ tailWord_2631229) baseStart_2631229 baseEnd_2631229 := by
    simpa [prefixWord, tailWord_2631229, baseEnd_2631229] using wordTrace_append hprefix tailTrace_2631229
  have hstable : (prefixWord ++ tailWord_2631229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631229).length < 2 ^ (prefixWord ++ tailWord_2631229).sum := by decide
  have hdescent : baseEnd_2631229 < baseStart_2631229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631255 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 1, 4]
def baseStart_2631255 : Nat := 118140960795 + 2631255 * 2 ^ 59
def prefixEnd_2631255 : Nat := 4983230072969 + 3 ^ 40 * 2631255 * 2
def baseEnd_2631255 : Nat := 900732359697471957607723

theorem tailTrace_2631255 : CollatzResearch.WordTrace tailWord_2631255 prefixEnd_2631255 900732359697471957607723 := by
  unfold tailWord_2631255
  simp only [CollatzResearch.WordTrace]
  refine ⟨95969754082419992421935219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63979836054946661614623479 95969754082419992421935219)
  ·
    refine ⟨143954631123629988632902829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95969754082419992421935219 143954631123629988632902829)
    ·
      refine ⟨53982986671361245737338561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143954631123629988632902829 53982986671361245737338561)
      ·
        refine ⟨40487240003520934303003921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53982986671361245737338561 40487240003520934303003921)
        ·
          refine ⟨30365430002640700727252941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40487240003520934303003921 30365430002640700727252941)
          ·
            refine ⟨11387036250990262772719853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30365430002640700727252941 11387036250990262772719853)
            ·
              refine ⟨4270138594121348539769945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11387036250990262772719853 4270138594121348539769945)
              ·
                refine ⟨3202603945591011404827459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270138594121348539769945 3202603945591011404827459)
                ·
                  refine ⟨4803905918386517107241189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202603945591011404827459 4803905918386517107241189)
                  ·
                    refine ⟨900732359697471957607723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4803905918386517107241189 900732359697471957607723)
                    ·
                      rfl

theorem cell22_2631255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_2631255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2631255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2631255 prefixEnd_2631255 := by exact prefixLift 2631255
  have htrace : WordTrace (prefixWord ++ tailWord_2631255) baseStart_2631255 baseEnd_2631255 := by
    simpa [prefixWord, tailWord_2631255, baseEnd_2631255] using wordTrace_append hprefix tailTrace_2631255
  have hstable : (prefixWord ++ tailWord_2631255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631255).length < 2 ^ (prefixWord ++ tailWord_2631255).sum := by decide
  have hdescent : baseEnd_2631255 < baseStart_2631255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
