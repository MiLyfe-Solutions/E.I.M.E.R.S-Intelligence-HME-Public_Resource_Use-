import V185TrunkScan22Chunk456

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4073184 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_4073184 : Nat := 118140960795 + 4073184 * 2 ^ 59
def prefixEnd_4073184 : Nat := 4983230072969 + 3 ^ 40 * 4073184 * 2
def baseEnd_4073184 : Nat := 1394334124135397921711849

theorem tailTrace_4073184 : CollatzResearch.WordTrace tailWord_4073184 prefixEnd_4073184 1394334124135397921711849 := by
  unfold tailWord_4073184
  simp only [CollatzResearch.WordTrace]
  refine ⟨74280612637778743644613303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99040816850371658192817737 74280612637778743644613303)
  ·
    refine ⟨111420918956668115466919955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74280612637778743644613303 111420918956668115466919955)
    ·
      refine ⟨167131378435002173200379933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111420918956668115466919955 167131378435002173200379933)
      ·
        refine ⟨62674266913125814950142475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167131378435002173200379933 62674266913125814950142475)
        ·
          refine ⟨94011400369688722425213713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62674266913125814950142475 94011400369688722425213713)
          ·
            refine ⟨70508550277266541818910285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94011400369688722425213713 70508550277266541818910285)
            ·
              refine ⟨26440706353974953182091357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70508550277266541818910285 26440706353974953182091357)
              ·
                refine ⟨9915264882740607443284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26440706353974953182091357 9915264882740607443284259)
                ·
                  refine ⟨14872897324110911164926389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9915264882740607443284259 14872897324110911164926389)
                  ·
                    refine ⟨1394334124135397921711849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14872897324110911164926389 1394334124135397921711849)
                    ·
                      rfl

theorem cell22_4073184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_4073184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073184 prefixEnd_4073184 := by exact prefixLift 4073184
  have htrace : WordTrace (prefixWord ++ tailWord_4073184) baseStart_4073184 baseEnd_4073184 := by
    simpa [prefixWord, tailWord_4073184, baseEnd_4073184] using wordTrace_append hprefix tailTrace_4073184
  have hstable : (prefixWord ++ tailWord_4073184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073184).length < 2 ^ (prefixWord ++ tailWord_4073184).sum := by decide
  have hdescent : baseEnd_4073184 < baseStart_4073184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073199 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_4073199 : Nat := 118140960795 + 4073199 * 2 ^ 59
def prefixEnd_4073199 : Nat := 4983230072969 + 3 ^ 40 * 4073199 * 2
def baseEnd_4073199 : Nat := 1394339258941942882586803

theorem tailTrace_4073199 : CollatzResearch.WordTrace tailWord_4073199 prefixEnd_4073199 1394339258941942882586803 := by
  unfold tailWord_4073199
  simp only [CollatzResearch.WordTrace]
  refine ⟨148561772370503144851022651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99041181580335429900681767 148561772370503144851022651)
  ·
    refine ⟨222842658555754717276533977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148561772370503144851022651 222842658555754717276533977)
    ·
      refine ⟨167131993916816037957400483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222842658555754717276533977 167131993916816037957400483)
      ·
        refine ⟨250697990875224056936100725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167131993916816037957400483 250697990875224056936100725)
        ·
          refine ⟨23502936644552255337759443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250697990875224056936100725 23502936644552255337759443)
          ·
            refine ⟨35254404966828383006639165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23502936644552255337759443 35254404966828383006639165)
            ·
              refine ⟨13220401862560643627489687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35254404966828383006639165 13220401862560643627489687)
              ·
                refine ⟨19830602793840965441234531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220401862560643627489687 19830602793840965441234531)
                ·
                  refine ⟨29745904190761448161851797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19830602793840965441234531 29745904190761448161851797)
                  ·
                    refine ⟨1394339258941942882586803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29745904190761448161851797 1394339258941942882586803)
                    ·
                      rfl

theorem cell22_4073199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_4073199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073199 prefixEnd_4073199 := by exact prefixLift 4073199
  have htrace : WordTrace (prefixWord ++ tailWord_4073199) baseStart_4073199 baseEnd_4073199 := by
    simpa [prefixWord, tailWord_4073199, baseEnd_4073199] using wordTrace_append hprefix tailTrace_4073199
  have hstable : (prefixWord ++ tailWord_4073199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073199).length < 2 ^ (prefixWord ++ tailWord_4073199).sum := by decide
  have hdescent : baseEnd_4073199 < baseStart_4073199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073218 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4073218 : Nat := 118140960795 + 4073218 * 2 ^ 59
def prefixEnd_4073218 : Nat := 4983230072969 + 3 ^ 40 * 4073218 * 2
def baseEnd_4073218 : Nat := 1394345763030233166361745

theorem tailTrace_4073218 : CollatzResearch.WordTrace tailWord_4073218 prefixEnd_4073218 1394345763030233166361745 := by
  unfold tailWord_4073218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140616339358577773991077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99041643571622874063976205 37140616339358577773991077)
  ·
    refine ⟨6963865563629733332623327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37140616339358577773991077 6963865563629733332623327)
    ·
      refine ⟨10445798345444599998934991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6963865563629733332623327 10445798345444599998934991)
      ·
        refine ⟨15668697518166899998402487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10445798345444599998934991 15668697518166899998402487)
        ·
          refine ⟨23503046277250349997603731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15668697518166899998402487 23503046277250349997603731)
          ·
            refine ⟨35254569415875524996405597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23503046277250349997603731 35254569415875524996405597)
            ·
              refine ⟨13220463530953321873652099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35254569415875524996405597 13220463530953321873652099)
              ·
                refine ⟨19830695296429982810478149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220463530953321873652099 19830695296429982810478149)
                ·
                  refine ⟨3718255368080621776964653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19830695296429982810478149 3718255368080621776964653)
                  ·
                    refine ⟨1394345763030233166361745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718255368080621776964653 1394345763030233166361745)
                    ·
                      rfl

theorem cell22_4073218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4073218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073218 prefixEnd_4073218 := by exact prefixLift 4073218
  have htrace : WordTrace (prefixWord ++ tailWord_4073218) baseStart_4073218 baseEnd_4073218 := by
    simpa [prefixWord, tailWord_4073218, baseEnd_4073218] using wordTrace_append hprefix tailTrace_4073218
  have hstable : (prefixWord ++ tailWord_4073218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073218).length < 2 ^ (prefixWord ++ tailWord_4073218).sum := by decide
  have hdescent : baseEnd_4073218 < baseStart_4073218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073306 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_4073306 : Nat := 118140960795 + 4073306 * 2 ^ 59
def prefixEnd_4073306 : Nat := 4983230072969 + 3 ^ 40 * 4073306 * 2
def baseEnd_4073306 : Nat := 1394375887228630270161475

theorem tailTrace_4073306 : CollatzResearch.WordTrace tailWord_4073306 prefixEnd_4073306 1394375887228630270161475 := by
  unfold tailWord_4073306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37141418745278875531291943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99043783320743668083445181 37141418745278875531291943)
  ·
    refine ⟨55712128117918313296937915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37141418745278875531291943 55712128117918313296937915)
    ·
      refine ⟨83568192176877469945406873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55712128117918313296937915 83568192176877469945406873)
      ·
        refine ⟨62676144132658102459055155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83568192176877469945406873 62676144132658102459055155)
        ·
          refine ⟨94014216198987153688582733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62676144132658102459055155 94014216198987153688582733)
          ·
            refine ⟨35255331074620182633218525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94014216198987153688582733 35255331074620182633218525)
            ·
              refine ⟨13220749152982568487456947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35255331074620182633218525 13220749152982568487456947)
              ·
                refine ⟨19831123729473852731185421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13220749152982568487456947 19831123729473852731185421)
                ·
                  refine ⟨7436671398552694774194533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19831123729473852731185421 7436671398552694774194533)
                  ·
                    refine ⟨1394375887228630270161475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436671398552694774194533 1394375887228630270161475)
                    ·
                      rfl

theorem cell22_4073306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_4073306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073306 prefixEnd_4073306 := by exact prefixLift 4073306
  have htrace : WordTrace (prefixWord ++ tailWord_4073306) baseStart_4073306 baseEnd_4073306 := by
    simpa [prefixWord, tailWord_4073306, baseEnd_4073306] using wordTrace_append hprefix tailTrace_4073306
  have hstable : (prefixWord ++ tailWord_4073306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073306).length < 2 ^ (prefixWord ++ tailWord_4073306).sum := by decide
  have hdescent : baseEnd_4073306 < baseStart_4073306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073336 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_4073336 : Nat := 118140960795 + 4073336 * 2 ^ 59
def prefixEnd_4073336 : Nat := 4983230072969 + 3 ^ 40 * 4073336 * 2
def baseEnd_4073336 : Nat := 1394386156841720191911383

theorem tailTrace_4073336 : CollatzResearch.WordTrace tailWord_4073336 prefixEnd_4073336 1394386156841720191911383 := by
  unfold tailWord_4073336
  simp only [CollatzResearch.WordTrace]
  refine ⟨74283384585503408624379931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99044512780671211499173241 74283384585503408624379931)
  ·
    refine ⟨111425076878255112936569897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74283384585503408624379931 111425076878255112936569897)
    ·
      refine ⟨83568807658691334702427423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111425076878255112936569897 83568807658691334702427423)
      ·
        refine ⟨125353211488037002053641135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83568807658691334702427423 125353211488037002053641135)
        ·
          refine ⟨188029817232055503080461703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125353211488037002053641135 188029817232055503080461703)
          ·
            refine ⟨282044725848083254620692555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188029817232055503080461703 282044725848083254620692555)
            ·
              refine ⟨423067088772124881931038833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282044725848083254620692555 423067088772124881931038833)
              ·
                refine ⟨317300316579093661448279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423067088772124881931038833 317300316579093661448279125)
                ·
                  refine ⟨3718363084911253845097021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 317300316579093661448279125 3718363084911253845097021)
                  ·
                    refine ⟨1394386156841720191911383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718363084911253845097021 1394386156841720191911383)
                    ·
                      rfl

theorem cell22_4073336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_4073336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073336 prefixEnd_4073336 := by exact prefixLift 4073336
  have htrace : WordTrace (prefixWord ++ tailWord_4073336) baseStart_4073336 baseEnd_4073336 := by
    simpa [prefixWord, tailWord_4073336, baseEnd_4073336] using wordTrace_append hprefix tailTrace_4073336
  have hstable : (prefixWord ++ tailWord_4073336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073336).length < 2 ^ (prefixWord ++ tailWord_4073336).sum := by decide
  have hdescent : baseEnd_4073336 < baseStart_4073336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073353 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_4073353 : Nat := 118140960795 + 4073353 * 2 ^ 59
def prefixEnd_4073353 : Nat := 4983230072969 + 3 ^ 40 * 4073353 * 2
def baseEnd_4073353 : Nat := 1394391976289137814236331

theorem tailTrace_4073353 : CollatzResearch.WordTrace tailWord_4073353 prefixEnd_4073353 1394391976289137814236331 := by
  unfold tailWord_4073353
  simp only [CollatzResearch.WordTrace]
  refine ⟨148567389211945229152128713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99044926141296819434752475 148567389211945229152128713)
  ·
    refine ⟨111425541908958921864096535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148567389211945229152128713 111425541908958921864096535)
    ·
      refine ⟨167138312863438382796144803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111425541908958921864096535 167138312863438382796144803)
      ·
        refine ⟨250707469295157574194217205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167138312863438382796144803 250707469295157574194217205)
        ·
          refine ⟨23503825246421022580707863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250707469295157574194217205 23503825246421022580707863)
          ·
            refine ⟨35255737869631533871061795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23503825246421022580707863 35255737869631533871061795)
            ·
              refine ⟨52883606804447300806592693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35255737869631533871061795 52883606804447300806592693)
              ·
                refine ⟨4957838137916934450618065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52883606804447300806592693 4957838137916934450618065)
                ·
                  refine ⟨3718378603437700837963549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957838137916934450618065 3718378603437700837963549)
                  ·
                    refine ⟨1394391976289137814236331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718378603437700837963549 1394391976289137814236331)
                    ·
                      rfl

theorem cell22_4073353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_4073353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073353 prefixEnd_4073353 := by exact prefixLift 4073353
  have htrace : WordTrace (prefixWord ++ tailWord_4073353) baseStart_4073353 baseEnd_4073353 := by
    simpa [prefixWord, tailWord_4073353, baseEnd_4073353] using wordTrace_append hprefix tailTrace_4073353
  have hstable : (prefixWord ++ tailWord_4073353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073353).length < 2 ^ (prefixWord ++ tailWord_4073353).sum := by decide
  have hdescent : baseEnd_4073353 < baseStart_4073353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073404 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_4073404 : Nat := 118140960795 + 4073404 * 2 ^ 59
def prefixEnd_4073404 : Nat := 4983230072969 + 3 ^ 40 * 4073404 * 2
def baseEnd_4073404 : Nat := 1394409434631390681211175

theorem tailTrace_4073404 : CollatzResearch.WordTrace tailWord_4073404 prefixEnd_4073404 1394409434631390681211175 := by
  unfold tailWord_4073404
  simp only [CollatzResearch.WordTrace]
  refine ⟨74284624667380232431117633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99046166223173643241490177 74284624667380232431117633)
  ·
    refine ⟨55713468500535174323338225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74284624667380232431117633 55713468500535174323338225)
    ·
      refine ⟨41785101375401380742503669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55713468500535174323338225 41785101375401380742503669)
      ·
        refine ⟨3917353253943879444609719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41785101375401380742503669 3917353253943879444609719)
        ·
          refine ⟨5876029880915819166914579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917353253943879444609719 5876029880915819166914579)
          ·
            refine ⟨8814044821373728750371869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876029880915819166914579 8814044821373728750371869)
            ·
              refine ⟨3305266808015148281389451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8814044821373728750371869 3305266808015148281389451)
              ·
                refine ⟨4957900212022722422084177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305266808015148281389451 4957900212022722422084177)
                ·
                  refine ⟨3718425159017041816563133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957900212022722422084177 3718425159017041816563133)
                  ·
                    refine ⟨1394409434631390681211175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718425159017041816563133 1394409434631390681211175)
                    ·
                      rfl

theorem cell22_4073404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_4073404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073404 prefixEnd_4073404 := by exact prefixLift 4073404
  have htrace : WordTrace (prefixWord ++ tailWord_4073404) baseStart_4073404 baseEnd_4073404 := by
    simpa [prefixWord, tailWord_4073404, baseEnd_4073404] using wordTrace_append hprefix tailTrace_4073404
  have hstable : (prefixWord ++ tailWord_4073404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073404).length < 2 ^ (prefixWord ++ tailWord_4073404).sum := by decide
  have hdescent : baseEnd_4073404 < baseStart_4073404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073471 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_4073471 : Nat := 118140960795 + 4073471 * 2 ^ 59
def prefixEnd_4073471 : Nat := 4983230072969 + 3 ^ 40 * 4073471 * 2
def baseEnd_4073471 : Nat := 1394432370100624839785969

theorem tailTrace_4073471 : CollatzResearch.WordTrace tailWord_4073471 prefixEnd_4073471 1394432370100624839785969 := by
  unfold tailWord_4073471
  simp only [CollatzResearch.WordTrace]
  refine ⟨148571693025517735304924267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99047795350345156869949511 148571693025517735304924267)
  ·
    refine ⟨222857539538276602957386401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148571693025517735304924267 222857539538276602957386401)
    ·
      refine ⟨167143154653707452218039801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222857539538276602957386401 167143154653707452218039801)
      ·
        refine ⟨125357365990280589163529851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167143154653707452218039801 125357365990280589163529851)
        ·
          refine ⟨188036048985420883745294777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125357365990280589163529851 188036048985420883745294777)
          ·
            refine ⟨141027036739065662808971083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188036048985420883745294777 141027036739065662808971083)
            ·
              refine ⟨211540555108598494213456625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141027036739065662808971083 211540555108598494213456625)
              ·
                refine ⟨158655416331448870660092469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211540555108598494213456625 158655416331448870660092469)
                ·
                  refine ⟨14873945281073331624383669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158655416331448870660092469 14873945281073331624383669)
                  ·
                    refine ⟨1394432370100624839785969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14873945281073331624383669 1394432370100624839785969)
                    ·
                      rfl

theorem cell22_4073471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_4073471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073471 prefixEnd_4073471 := by exact prefixLift 4073471
  have htrace : WordTrace (prefixWord ++ tailWord_4073471) baseStart_4073471 baseEnd_4073471 := by
    simpa [prefixWord, tailWord_4073471, baseEnd_4073471] using wordTrace_append hprefix tailTrace_4073471
  have hstable : (prefixWord ++ tailWord_4073471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073471).length < 2 ^ (prefixWord ++ tailWord_4073471).sum := by decide
  have hdescent : baseEnd_4073471 < baseStart_4073471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073503 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_4073503 : Nat := 118140960795 + 4073503 * 2 ^ 59
def prefixEnd_4073503 : Nat := 4983230072969 + 3 ^ 40 * 4073503 * 2
def baseEnd_4073503 : Nat := 1394443324354587422985871

theorem tailTrace_4073503 : CollatzResearch.WordTrace tailWord_4073503 prefixEnd_4073503 1394443324354587422985871 := by
  unfold tailWord_4073503
  simp only [CollatzResearch.WordTrace]
  refine ⟨148572860161401804770089163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99048573440934536513392775 148572860161401804770089163)
  ·
    refine ⟨222859290242102707155133745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148572860161401804770089163 222859290242102707155133745)
    ·
      refine ⟨167144467681577030366350309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222859290242102707155133745 167144467681577030366350309)
      ·
        refine ⟨31339587690295693193690683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167144467681577030366350309 31339587690295693193690683)
        ·
          refine ⟨47009381535443539790536025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31339587690295693193690683 47009381535443539790536025)
          ·
            refine ⟨35257036151582654842902019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47009381535443539790536025 35257036151582654842902019)
            ·
              refine ⟨52885554227373982264353029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35257036151582654842902019 52885554227373982264353029)
              ·
                refine ⟨9916041417632621674566193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52885554227373982264353029 9916041417632621674566193)
                ·
                  refine ⟨7437031063224466255924645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916041417632621674566193 7437031063224466255924645)
                  ·
                    refine ⟨1394443324354587422985871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437031063224466255924645 1394443324354587422985871)
                    ·
                      rfl

theorem cell22_4073503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_4073503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073503 prefixEnd_4073503 := by exact prefixLift 4073503
  have htrace : WordTrace (prefixWord ++ tailWord_4073503) baseStart_4073503 baseEnd_4073503 := by
    simpa [prefixWord, tailWord_4073503, baseEnd_4073503] using wordTrace_append hprefix tailTrace_4073503
  have hstable : (prefixWord ++ tailWord_4073503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073503).length < 2 ^ (prefixWord ++ tailWord_4073503).sum := by decide
  have hdescent : baseEnd_4073503 < baseStart_4073503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073537 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4073537 : Nat := 118140960795 + 4073537 * 2 ^ 59
def prefixEnd_4073537 : Nat := 4983230072969 + 3 ^ 40 * 4073537 * 2
def baseEnd_4073537 : Nat := 1394454963249422667635767

theorem tailTrace_4073537 : CollatzResearch.WordTrace tailWord_4073537 prefixEnd_4073537 1394454963249422667635767 := by
  unfold tailWord_4073537
  simp only [CollatzResearch.WordTrace]
  refine ⟨148574100243278628576826865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99049400162185752384551243 148574100243278628576826865)
  ·
    refine ⟨111430575182458971432620149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148574100243278628576826865 111430575182458971432620149)
    ·
      refine ⟨10446616423355528571808139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111430575182458971432620149 10446616423355528571808139)
      ·
        refine ⟨15669924635033292857712209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446616423355528571808139 15669924635033292857712209)
        ·
          refine ⟨11752443476274969643284157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669924635033292857712209 11752443476274969643284157)
          ·
            refine ⟨4407166303603113616231559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11752443476274969643284157 4407166303603113616231559)
            ·
              refine ⟨6610749455404670424347339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407166303603113616231559 6610749455404670424347339)
              ·
                refine ⟨9916124183107005636521009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610749455404670424347339 9916124183107005636521009)
                ·
                  refine ⟨7437093137330254227390757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916124183107005636521009 7437093137330254227390757)
                  ·
                    refine ⟨1394454963249422667635767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437093137330254227390757 1394454963249422667635767)
                    ·
                      rfl

theorem cell22_4073537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4073537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073537 prefixEnd_4073537 := by exact prefixLift 4073537
  have htrace : WordTrace (prefixWord ++ tailWord_4073537) baseStart_4073537 baseEnd_4073537 := by
    simpa [prefixWord, tailWord_4073537, baseEnd_4073537] using wordTrace_append hprefix tailTrace_4073537
  have hstable : (prefixWord ++ tailWord_4073537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073537).length < 2 ^ (prefixWord ++ tailWord_4073537).sum := by decide
  have hdescent : baseEnd_4073537 < baseStart_4073537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073601 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4073601 : Nat := 118140960795 + 4073601 * 2 ^ 59
def prefixEnd_4073601 : Nat := 4983230072969 + 3 ^ 40 * 4073601 * 2
def baseEnd_4073601 : Nat := 1394476871757347834035571

theorem tailTrace_4073601 : CollatzResearch.WordTrace tailWord_4073601 prefixEnd_4073601 1394476871757347834035571 := by
  unfold tailWord_4073601
  simp only [CollatzResearch.WordTrace]
  refine ⟨148576434515046767507156657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99050956343364511671437771 148576434515046767507156657)
  ·
    refine ⟨111432325886285075630367493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148576434515046767507156657 111432325886285075630367493)
    ·
      refine ⟨20893561103678451680693905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111432325886285075630367493 20893561103678451680693905)
      ·
        refine ⟨15670170827758838760520429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20893561103678451680693905 15670170827758838760520429)
        ·
          refine ⟨5876314060409564535195161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15670170827758838760520429 5876314060409564535195161)
          ·
            refine ⟨4407235545307173401396371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5876314060409564535195161 4407235545307173401396371)
            ·
              refine ⟨6610853317960760102094557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407235545307173401396371 6610853317960760102094557)
              ·
                refine ⟨2479069994235285038285459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6610853317960760102094557 2479069994235285038285459)
                ·
                  refine ⟨3718604991352927557428189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479069994235285038285459 3718604991352927557428189)
                  ·
                    refine ⟨1394476871757347834035571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718604991352927557428189 1394476871757347834035571)
                    ·
                      rfl

theorem cell22_4073601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4073601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073601 prefixEnd_4073601 := by exact prefixLift 4073601
  have htrace : WordTrace (prefixWord ++ tailWord_4073601) baseStart_4073601 baseEnd_4073601 := by
    simpa [prefixWord, tailWord_4073601, baseEnd_4073601] using wordTrace_append hprefix tailTrace_4073601
  have hstable : (prefixWord ++ tailWord_4073601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073601).length < 2 ^ (prefixWord ++ tailWord_4073601).sum := by decide
  have hdescent : baseEnd_4073601 < baseStart_4073601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073625 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 4]
def baseStart_4073625 : Nat := 118140960795 + 4073625 * 2 ^ 59
def prefixEnd_4073625 : Nat := 4983230072969 + 3 ^ 40 * 4073625 * 2
def baseEnd_4073625 : Nat := 464828362482606590478499

theorem tailTrace_4073625 : CollatzResearch.WordTrace tailWord_4073625 prefixEnd_4073625 464828362482606590478499 := by
  unfold tailWord_4073625
  simp only [CollatzResearch.WordTrace]
  refine ⟨148577309866959819606030329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99051539911306546404020219 148577309866959819606030329)
  ·
    refine ⟨111432982400219864704522747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148577309866959819606030329 111432982400219864704522747)
    ·
      refine ⟨167149473600329797056784121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111432982400219864704522747 167149473600329797056784121)
      ·
        refine ⟨125362105200247347792588091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167149473600329797056784121 125362105200247347792588091)
        ·
          refine ⟨188043157800371021688882137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125362105200247347792588091 188043157800371021688882137)
          ·
            refine ⟨141032368350278266266661603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188043157800371021688882137 141032368350278266266661603)
            ·
              refine ⟨211548552525417399399992405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141032368350278266266661603 211548552525417399399992405)
              ·
                refine ⟨2479084599907235149218661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 211548552525417399399992405 2479084599907235149218661)
                ·
                  refine ⟨464828362482606590478499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479084599907235149218661 464828362482606590478499)
                  ·
                    rfl

theorem cell22_4073625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_4073625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073625 prefixEnd_4073625 := by exact prefixLift 4073625
  have htrace : WordTrace (prefixWord ++ tailWord_4073625) baseStart_4073625 baseEnd_4073625 := by
    simpa [prefixWord, tailWord_4073625, baseEnd_4073625] using wordTrace_append hprefix tailTrace_4073625
  have hstable : (prefixWord ++ tailWord_4073625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073625).length < 2 ^ (prefixWord ++ tailWord_4073625).sum := by decide
  have hdescent : baseEnd_4073625 < baseStart_4073625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073655 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_4073655 : Nat := 118140960795 + 4073655 * 2 ^ 59
def prefixEnd_4073655 : Nat := 4983230072969 + 3 ^ 40 * 4073655 * 2
def baseEnd_4073655 : Nat := 1394495357060909693185405

theorem tailTrace_4073655 : CollatzResearch.WordTrace tailWord_4073655 prefixEnd_4073655 1394495357060909693185405 := by
  unfold tailWord_4073655
  simp only [CollatzResearch.WordTrace]
  refine ⟨148578404056851134729622419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99052269371234089819748279 148578404056851134729622419)
  ·
    refine ⟨222867606085276702094433629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148578404056851134729622419 222867606085276702094433629)
    ·
      refine ⟨83575352281978763285412611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222867606085276702094433629 83575352281978763285412611)
      ·
        refine ⟨125363028422968144928118917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83575352281978763285412611 125363028422968144928118917)
        ·
          refine ⟨23505567829306527174022297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125363028422968144928118917 23505567829306527174022297)
          ·
            refine ⟨17629175871979895380516723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23505567829306527174022297 17629175871979895380516723)
            ·
              refine ⟨26443763807969843070775085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17629175871979895380516723 26443763807969843070775085)
              ·
                refine ⟨9916411427988691151540657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26443763807969843070775085 9916411427988691151540657)
                ·
                  refine ⟨7437308570991518363655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916411427988691151540657 7437308570991518363655493)
                  ·
                    refine ⟨1394495357060909693185405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437308570991518363655493 1394495357060909693185405)
                    ·
                      rfl

theorem cell22_4073655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_4073655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073655 prefixEnd_4073655 := by exact prefixLift 4073655
  have htrace : WordTrace (prefixWord ++ tailWord_4073655) baseStart_4073655 baseEnd_4073655 := by
    simpa [prefixWord, tailWord_4073655, baseEnd_4073655] using wordTrace_append hprefix tailTrace_4073655
  have hstable : (prefixWord ++ tailWord_4073655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073655).length < 2 ^ (prefixWord ++ tailWord_4073655).sum := by decide
  have hdescent : baseEnd_4073655 < baseStart_4073655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073732 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_4073732 : Nat := 118140960795 + 4073732 * 2 ^ 59
def prefixEnd_4073732 : Nat := 4983230072969 + 3 ^ 40 * 4073732 * 2
def baseEnd_4073732 : Nat := 464840571911502386336723

theorem tailTrace_4073732 : CollatzResearch.WordTrace tailWord_4073732 prefixEnd_4073732 464840571911502386336723 := by
  unfold tailWord_4073732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74290606238786088440087725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99054141651714784586783633 74290606238786088440087725)
  ·
    refine ⟨27858977339544783165032897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74290606238786088440087725 27858977339544783165032897)
    ·
      refine ⟨20894233004658587373774673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27858977339544783165032897 20894233004658587373774673)
      ·
        refine ⟨15670674753493940530331005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20894233004658587373774673 15670674753493940530331005)
        ·
          refine ⟨5876503032560227698874127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15670674753493940530331005 5876503032560227698874127)
          ·
            refine ⟨8814754548840341548311191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876503032560227698874127 8814754548840341548311191)
            ·
              refine ⟨13222131823260512322466787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814754548840341548311191 13222131823260512322466787)
              ·
                refine ⟨19833197734890768483700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13222131823260512322466787 19833197734890768483700181)
                ·
                  refine ⟨464840571911502386336723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19833197734890768483700181 464840571911502386336723)
                  ·
                    rfl

theorem cell22_4073732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_4073732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073732 prefixEnd_4073732 := by exact prefixLift 4073732
  have htrace : WordTrace (prefixWord ++ tailWord_4073732) baseStart_4073732 baseEnd_4073732 := by
    simpa [prefixWord, tailWord_4073732, baseEnd_4073732] using wordTrace_append hprefix tailTrace_4073732
  have hstable : (prefixWord ++ tailWord_4073732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073732).length < 2 ^ (prefixWord ++ tailWord_4073732).sum := by decide
  have hdescent : baseEnd_4073732 < baseStart_4073732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073770 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4073770 : Nat := 118140960795 + 4073770 * 2 ^ 59
def prefixEnd_4073770 : Nat := 4983230072969 + 3 ^ 40 * 4073770 * 2
def baseEnd_4073770 : Nat := 1394534723911087726560053

theorem tailTrace_4073770 : CollatzResearch.WordTrace tailWord_4073770 prefixEnd_4073770 1394534723911087726560053 := by
  unfold tailWord_4073770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145649612858627342514691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99055065634289672913372509 37145649612858627342514691)
  ·
    refine ⟨55718474419287941013772037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37145649612858627342514691 55718474419287941013772037)
    ·
      refine ⟨10447213953616488940082257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55718474419287941013772037 10447213953616488940082257)
      ·
        refine ⟨7835410465212366705061693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10447213953616488940082257 7835410465212366705061693)
        ·
          refine ⟨2938278924454637514398135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7835410465212366705061693 2938278924454637514398135)
          ·
            refine ⟨4407418386681956271597203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938278924454637514398135 4407418386681956271597203)
            ·
              refine ⟨6611127580022934407395805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407418386681956271597203 6611127580022934407395805)
              ·
                refine ⟨2479172842508600402773427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6611127580022934407395805 2479172842508600402773427)
                ·
                  refine ⟨3718759263762900604160141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479172842508600402773427 3718759263762900604160141)
                  ·
                    refine ⟨1394534723911087726560053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718759263762900604160141 1394534723911087726560053)
                    ·
                      rfl

theorem cell22_4073770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4073770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073770 prefixEnd_4073770 := by exact prefixLift 4073770
  have htrace : WordTrace (prefixWord ++ tailWord_4073770) baseStart_4073770 baseEnd_4073770 := by
    simpa [prefixWord, tailWord_4073770, baseEnd_4073770] using wordTrace_append hprefix tailTrace_4073770
  have hstable : (prefixWord ++ tailWord_4073770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073770).length < 2 ^ (prefixWord ++ tailWord_4073770).sum := by decide
  have hdescent : baseEnd_4073770 < baseStart_4073770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073775 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_4073775 : Nat := 118140960795 + 4073775 * 2 ^ 59
def prefixEnd_4073775 : Nat := 4983230072969 + 3 ^ 40 * 4073775 * 2
def baseEnd_4073775 : Nat := 1394536435513269380185037

theorem tailTrace_4073775 : CollatzResearch.WordTrace tailWord_4073775 prefixEnd_4073775 1394536435513269380185037 := by
  unfold tailWord_4073775
  simp only [CollatzResearch.WordTrace]
  refine ⟨148582780816416395223990779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99055187210944263482660519 148582780816416395223990779)
  ·
    refine ⟨222874171224624592835986169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148582780816416395223990779 222874171224624592835986169)
    ·
      refine ⟨167155628418468444626989627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222874171224624592835986169 167155628418468444626989627)
      ·
        refine ⟨250733442627702666940484441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167155628418468444626989627 250733442627702666940484441)
        ·
          refine ⟨188050081970777000205363331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250733442627702666940484441 188050081970777000205363331)
          ·
            refine ⟨282075122956165500308044997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188050081970777000205363331 282075122956165500308044997)
            ·
              refine ⟨52889085554281031307758437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282075122956165500308044997 52889085554281031307758437)
              ·
                refine ⟨9916703541427693370204707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52889085554281031307758437 9916703541427693370204707)
                ·
                  refine ⟨14875055312141540055307061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9916703541427693370204707 14875055312141540055307061)
                  ·
                    refine ⟨1394536435513269380185037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14875055312141540055307061 1394536435513269380185037)
                    ·
                      rfl

theorem cell22_4073775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_4073775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073775 prefixEnd_4073775 := by exact prefixLift 4073775
  have htrace : WordTrace (prefixWord ++ tailWord_4073775) baseStart_4073775 baseEnd_4073775 := by
    simpa [prefixWord, tailWord_4073775, baseEnd_4073775] using wordTrace_append hprefix tailTrace_4073775
  have hstable : (prefixWord ++ tailWord_4073775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073775).length < 2 ^ (prefixWord ++ tailWord_4073775).sum := by decide
  have hdescent : baseEnd_4073775 < baseStart_4073775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073809 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_4073809 : Nat := 118140960795 + 4073809 * 2 ^ 59
def prefixEnd_4073809 : Nat := 4983230072969 + 3 ^ 40 * 4073809 * 2
def baseEnd_4073809 : Nat := 1394548074408104624834933

theorem tailTrace_4073809 : CollatzResearch.WordTrace tailWord_4073809 prefixEnd_4073809 1394548074408104624834933 := by
  unfold tailWord_4073809
  simp only [CollatzResearch.WordTrace]
  refine ⟨148584020898293219030728481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99056013932195479353818987 148584020898293219030728481)
  ·
    refine ⟨111438015673719914273046361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148584020898293219030728481 111438015673719914273046361)
    ·
      refine ⟨83578511755289935704784771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111438015673719914273046361 83578511755289935704784771)
      ·
        refine ⟨125367767632934903557177157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83578511755289935704784771 125367767632934903557177157)
        ·
          refine ⟨23506456431175294416970717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125367767632934903557177157 23506456431175294416970717)
          ·
            refine ⟨8814921161690735406364019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23506456431175294416970717 8814921161690735406364019)
            ·
              refine ⟨13222381742536103109546029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814921161690735406364019 13222381742536103109546029)
              ·
                refine ⟨4958393153451038666079761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13222381742536103109546029 4958393153451038666079761)
                ·
                  refine ⟨3718794865088278999559821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4958393153451038666079761 3718794865088278999559821)
                  ·
                    refine ⟨1394548074408104624834933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718794865088278999559821 1394548074408104624834933)
                    ·
                      rfl

theorem cell22_4073809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_4073809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073809 prefixEnd_4073809 := by exact prefixLift 4073809
  have htrace : WordTrace (prefixWord ++ tailWord_4073809) baseStart_4073809 baseEnd_4073809 := by
    simpa [prefixWord, tailWord_4073809, baseEnd_4073809] using wordTrace_append hprefix tailTrace_4073809
  have hstable : (prefixWord ++ tailWord_4073809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073809).length < 2 ^ (prefixWord ++ tailWord_4073809).sum := by decide
  have hdescent : baseEnd_4073809 < baseStart_4073809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073824 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_4073824 : Nat := 118140960795 + 4073824 * 2 ^ 59
def prefixEnd_4073824 : Nat := 4983230072969 + 3 ^ 40 * 4073824 * 2
def baseEnd_4073824 : Nat := 1394553209214649585709887

theorem tailTrace_4073824 : CollatzResearch.WordTrace tailWord_4073824 prefixEnd_4073824 1394553209214649585709887 := by
  unfold tailWord_4073824
  simp only [CollatzResearch.WordTrace]
  refine ⟨74292283996619438296262263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99056378662159251061683017 74292283996619438296262263)
  ·
    refine ⟨111438425994929157444393395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74292283996619438296262263 111438425994929157444393395)
    ·
      refine ⟨167157638992393736166590093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111438425994929157444393395 167157638992393736166590093)
      ·
        refine ⟨62684114622147651062471285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167157638992393736166590093 62684114622147651062471285)
        ·
          refine ⟨5876635745826342287106683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62684114622147651062471285 5876635745826342287106683)
          ·
            refine ⟨8814953618739513430660025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876635745826342287106683 8814953618739513430660025)
            ·
              refine ⟨6611215214054635072995019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814953618739513430660025 6611215214054635072995019)
              ·
                refine ⟨9916822821081952609492529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611215214054635072995019 9916822821081952609492529)
                ·
                  refine ⟨7437617115811464457119397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9916822821081952609492529 7437617115811464457119397)
                  ·
                    refine ⟨1394553209214649585709887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437617115811464457119397 1394553209214649585709887)
                    ·
                      rfl

theorem cell22_4073824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_4073824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073824 prefixEnd_4073824 := by exact prefixLift 4073824
  have htrace : WordTrace (prefixWord ++ tailWord_4073824) baseStart_4073824 baseEnd_4073824 := by
    simpa [prefixWord, tailWord_4073824, baseEnd_4073824] using wordTrace_append hprefix tailTrace_4073824
  have hstable : (prefixWord ++ tailWord_4073824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073824).length < 2 ^ (prefixWord ++ tailWord_4073824).sum := by decide
  have hdescent : baseEnd_4073824 < baseStart_4073824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073867 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 5]
def baseStart_4073867 : Nat := 118140960795 + 4073867 * 2 ^ 59
def prefixEnd_4073867 : Nat := 4983230072969 + 3 ^ 40 * 4073867 * 2
def baseEnd_4073867 : Nat := 464855976331137268961585

theorem tailTrace_4073867 : CollatzResearch.WordTrace tailWord_4073867 prefixEnd_4073867 464855976331137268961585 := by
  unfold tailWord_4073867
  simp only [CollatzResearch.WordTrace]
  refine ⟨148586136332083094936339855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99057424221388729957559903 148586136332083094936339855)
  ·
    refine ⟨222879204498124642404509783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148586136332083094936339855 222879204498124642404509783)
    ·
      refine ⟨334318806747186963606764675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222879204498124642404509783 334318806747186963606764675)
      ·
        refine ⟨501478210120780445410147013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334318806747186963606764675 501478210120780445410147013)
        ·
          refine ⟨94027164397646333514402565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501478210120780445410147013 94027164397646333514402565)
          ·
            refine ⟨17630093324558687533950481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94027164397646333514402565 17630093324558687533950481)
            ·
              refine ⟨13222569993419015650462861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17630093324558687533950481 13222569993419015650462861)
              ·
                refine ⟨4958463747532130868923573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13222569993419015650462861 4958463747532130868923573)
                ·
                  refine ⟨464855976331137268961585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4958463747532130868923573 464855976331137268961585)
                  ·
                    rfl

theorem cell22_4073867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 5].length) (baseStart_4073867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073867 prefixEnd_4073867 := by exact prefixLift 4073867
  have htrace : WordTrace (prefixWord ++ tailWord_4073867) baseStart_4073867 baseEnd_4073867 := by
    simpa [prefixWord, tailWord_4073867, baseEnd_4073867] using wordTrace_append hprefix tailTrace_4073867
  have hstable : (prefixWord ++ tailWord_4073867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073867).length < 2 ^ (prefixWord ++ tailWord_4073867).sum := by decide
  have hdescent : baseEnd_4073867 < baseStart_4073867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073959 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4073959 : Nat := 118140960795 + 4073959 * 2 ^ 59
def prefixEnd_4073959 : Nat := 4983230072969 + 3 ^ 40 * 4073959 * 2
def baseEnd_4073959 : Nat := 1394599422473554233584473

theorem tailTrace_4073959 : CollatzResearch.WordTrace tailWord_4073959 prefixEnd_4073959 1394599422473554233584473 := by
  unfold tailWord_4073959
  simp only [CollatzResearch.WordTrace]
  refine ⟨148589491847749794648688931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99059661231833196432459287 148589491847749794648688931)
  ·
    refine ⟨222884237771624691973033397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148589491847749794648688931 222884237771624691973033397)
    ·
      refine ⟨20895397291089814872471881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222884237771624691973033397 20895397291089814872471881)
      ·
        refine ⟨15671547968317361154353911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20895397291089814872471881 15671547968317361154353911)
        ·
          refine ⟨23507321952476041731530867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671547968317361154353911 23507321952476041731530867)
          ·
            refine ⟨35260982928714062597296301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507321952476041731530867 35260982928714062597296301)
            ·
              refine ⟨13222868598267773473986113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35260982928714062597296301 13222868598267773473986113)
              ·
                refine ⟨9917151448700830105489585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222868598267773473986113 9917151448700830105489585)
                ·
                  refine ⟨7437863586525622579117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9917151448700830105489585 7437863586525622579117189)
                  ·
                    refine ⟨1394599422473554233584473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7437863586525622579117189 1394599422473554233584473)
                    ·
                      rfl

theorem cell22_4073959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4073959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073959 prefixEnd_4073959 := by exact prefixLift 4073959
  have htrace : WordTrace (prefixWord ++ tailWord_4073959) baseStart_4073959 baseEnd_4073959 := by
    simpa [prefixWord, tailWord_4073959, baseEnd_4073959] using wordTrace_append hprefix tailTrace_4073959
  have hstable : (prefixWord ++ tailWord_4073959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073959).length < 2 ^ (prefixWord ++ tailWord_4073959).sum := by decide
  have hdescent : baseEnd_4073959 < baseStart_4073959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073974 : List Nat := [5, 1, 1, 1, 2, 1, 4, 7]
def baseStart_4073974 : Nat := 118140960795 + 4073974 * 2 ^ 59
def prefixEnd_4073974 : Nat := 4983230072969 + 3 ^ 40 * 4073974 * 2
def baseEnd_4073974 : Nat := 154956061920011021606603

theorem tailTrace_4073974 : CollatzResearch.WordTrace tailWord_4073974 prefixEnd_4073974 154956061920011021606603 := by
  unfold tailWord_4073974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9286877433918465763155311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99060025961796968140323317 9286877433918465763155311)
  ·
    refine ⟨13930316150877698644732967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9286877433918465763155311 13930316150877698644732967)
    ·
      refine ⟨20895474226316547967099451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13930316150877698644732967 20895474226316547967099451)
      ·
        refine ⟨31343211339474821950649177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20895474226316547967099451 31343211339474821950649177)
        ·
          refine ⟨23507408504606116462986883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31343211339474821950649177 23507408504606116462986883)
          ·
            refine ⟨35261112756909174694480325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507408504606116462986883 35261112756909174694480325)
            ·
              refine ⟨6611458641920470255215061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35261112756909174694480325 6611458641920470255215061)
              ·
                refine ⟨154956061920011021606603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6611458641920470255215061 154956061920011021606603)
                ·
                  rfl

theorem cell22_4073974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_4073974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073974 prefixEnd_4073974 := by exact prefixLift 4073974
  have htrace : WordTrace (prefixWord ++ tailWord_4073974) baseStart_4073974 baseEnd_4073974 := by
    simpa [prefixWord, tailWord_4073974, baseEnd_4073974] using wordTrace_append hprefix tailTrace_4073974
  have hstable : (prefixWord ++ tailWord_4073974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073974).length < 2 ^ (prefixWord ++ tailWord_4073974).sum := by decide
  have hdescent : baseEnd_4073974 < baseStart_4073974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073989 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_4073989 : Nat := 118140960795 + 4073989 * 2 ^ 59
def prefixEnd_4073989 : Nat := 4983230072969 + 3 ^ 40 * 4073989 * 2
def baseEnd_4073989 : Nat := 1394609692086644155334381

theorem tailTrace_4073989 : CollatzResearch.WordTrace tailWord_4073989 prefixEnd_4073989 1394609692086644155334381 := by
  unfold tailWord_4073989
  simp only [CollatzResearch.WordTrace]
  refine ⟨148590586037641109772281021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99060390691760739848187347 148590586037641109772281021)
  ·
    refine ⟨55721469764115416164605383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148590586037641109772281021 55721469764115416164605383)
    ·
      refine ⟨83582204646173124246908075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55721469764115416164605383 83582204646173124246908075)
      ·
        refine ⟨125373306969259686370362113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83582204646173124246908075 125373306969259686370362113)
        ·
          refine ⟨94029980226944764777771585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125373306969259686370362113 94029980226944764777771585)
          ·
            refine ⟨70522485170208573583328689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94029980226944764777771585 70522485170208573583328689)
            ·
              refine ⟨52891863877656430187496517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70522485170208573583328689 52891863877656430187496517)
              ·
                refine ⟨9917224477060580660155597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52891863877656430187496517 9917224477060580660155597)
                ·
                  refine ⟨3718959178897717747558349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9917224477060580660155597 3718959178897717747558349)
                  ·
                    refine ⟨1394609692086644155334381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718959178897717747558349 1394609692086644155334381)
                    ·
                      rfl

theorem cell22_4073989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_4073989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073989 prefixEnd_4073989 := by exact prefixLift 4073989
  have htrace : WordTrace (prefixWord ++ tailWord_4073989) baseStart_4073989 baseEnd_4073989 := by
    simpa [prefixWord, tailWord_4073989, baseEnd_4073989] using wordTrace_append hprefix tailTrace_4073989
  have hstable : (prefixWord ++ tailWord_4073989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073989).length < 2 ^ (prefixWord ++ tailWord_4073989).sum := by decide
  have hdescent : baseEnd_4073989 < baseStart_4073989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074019 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 5]
def baseStart_4074019 : Nat := 118140960795 + 4074019 * 2 ^ 59
def prefixEnd_4074019 : Nat := 4983230072969 + 3 ^ 40 * 4074019 * 2
def baseEnd_4074019 : Nat := 464873320566578025694763

theorem tailTrace_4074019 : CollatzResearch.WordTrace tailWord_4074019 prefixEnd_4074019 464873320566578025694763 := by
  unfold tailWord_4074019
  simp only [CollatzResearch.WordTrace]
  refine ⟨148591680227532424895873111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99061120151688283263915407 148591680227532424895873111)
  ·
    refine ⟨222887520341298637343809667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148591680227532424895873111 222887520341298637343809667)
    ·
      refine ⟨334331280511947956015714501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222887520341298637343809667 334331280511947956015714501)
      ·
        refine ⟨62687115095990241752946469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334331280511947956015714501 62687115095990241752946469)
        ·
          refine ⟨11753834080498170328677463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62687115095990241752946469 11753834080498170328677463)
          ·
            refine ⟨17630751120747255493016195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11753834080498170328677463 17630751120747255493016195)
            ·
              refine ⟨26446126681120883239524293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17630751120747255493016195 26446126681120883239524293)
              ·
                refine ⟨4958648752710165607410805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26446126681120883239524293 4958648752710165607410805)
                ·
                  refine ⟨464873320566578025694763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4958648752710165607410805 464873320566578025694763)
                  ·
                    rfl

theorem cell22_4074019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 5].length) (baseStart_4074019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074019 prefixEnd_4074019 := by exact prefixLift 4074019
  have htrace : WordTrace (prefixWord ++ tailWord_4074019) baseStart_4074019 baseEnd_4074019 := by
    simpa [prefixWord, tailWord_4074019, baseEnd_4074019] using wordTrace_append hprefix tailTrace_4074019
  have hstable : (prefixWord ++ tailWord_4074019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074019).length < 2 ^ (prefixWord ++ tailWord_4074019).sum := by decide
  have hdescent : baseEnd_4074019 < baseStart_4074019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074066 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_4074066 : Nat := 118140960795 + 4074066 * 2 ^ 59
def prefixEnd_4074066 : Nat := 4983230072969 + 3 ^ 40 * 4074066 * 2
def baseEnd_4074066 : Nat := 1394636050760241621159145

theorem tailTrace_4074066 : CollatzResearch.WordTrace tailWord_4074066 prefixEnd_4074066 1394636050760241621159145 := by
  unfold tailWord_4074066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37148348614590537980708513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99062262972241434615222701 37148348614590537980708513)
  ·
    refine ⟨27861261460942903485531385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37148348614590537980708513 27861261460942903485531385)
    ·
      refine ⟨20895946095707177614148539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27861261460942903485531385 20895946095707177614148539)
      ·
        refine ⟨31343919143560766421222809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20895946095707177614148539 31343919143560766421222809)
        ·
          refine ⟨23507939357670574815917107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31343919143560766421222809 23507939357670574815917107)
          ·
            refine ⟨35261909036505862223875661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23507939357670574815917107 35261909036505862223875661)
            ·
              refine ⟨13223215888689698333953373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35261909036505862223875661 13223215888689698333953373)
              ·
                refine ⟨4958705958258636875232515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13223215888689698333953373 4958705958258636875232515)
                ·
                  refine ⟨7438058937387955312848773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958705958258636875232515 7438058937387955312848773)
                  ·
                    refine ⟨1394636050760241621159145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438058937387955312848773 1394636050760241621159145)
                    ·
                      rfl

theorem cell22_4074066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_4074066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074066 prefixEnd_4074066 := by exact prefixLift 4074066
  have htrace : WordTrace (prefixWord ++ tailWord_4074066) baseStart_4074066 baseEnd_4074066 := by
    simpa [prefixWord, tailWord_4074066, baseEnd_4074066] using wordTrace_append hprefix tailTrace_4074066
  have hstable : (prefixWord ++ tailWord_4074066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074066).length < 2 ^ (prefixWord ++ tailWord_4074066).sum := by decide
  have hdescent : baseEnd_4074066 < baseStart_4074066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074081 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 4]
def baseStart_4074081 : Nat := 118140960795 + 4074081 * 2 ^ 59
def prefixEnd_4074081 : Nat := 4983230072969 + 3 ^ 40 * 4074081 * 2
def baseEnd_4074081 : Nat := 464880395188928860678033

theorem tailTrace_4074081 : CollatzResearch.WordTrace tailWord_4074081 prefixEnd_4074081 464880395188928860678033 := by
  unfold tailWord_4074081
  simp only [CollatzResearch.WordTrace]
  refine ⟨148593941553307809484630097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99062627702205206323086731 148593941553307809484630097)
  ·
    refine ⟨111445456164980857113472573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148593941553307809484630097 111445456164980857113472573)
    ·
      refine ⟨41792046061867821417552215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111445456164980857113472573 41792046061867821417552215)
      ·
        refine ⟨62688069092801732126328323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41792046061867821417552215 62688069092801732126328323)
        ·
          refine ⟨94032103639202598189492485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62688069092801732126328323 94032103639202598189492485)
          ·
            refine ⟨17631019432350487160529841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94032103639202598189492485 17631019432350487160529841)
            ·
              refine ⟨13223264574262865370397381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17631019432350487160529841 13223264574262865370397381)
              ·
                refine ⟨2479362107674287256949509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13223264574262865370397381 2479362107674287256949509)
                ·
                  refine ⟨464880395188928860678033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479362107674287256949509 464880395188928860678033)
                  ·
                    rfl

theorem cell22_4074081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_4074081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074081 prefixEnd_4074081 := by exact prefixLift 4074081
  have htrace : WordTrace (prefixWord ++ tailWord_4074081) baseStart_4074081 baseEnd_4074081 := by
    simpa [prefixWord, tailWord_4074081, baseEnd_4074081] using wordTrace_append hprefix tailTrace_4074081
  have hstable : (prefixWord ++ tailWord_4074081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074081).length < 2 ^ (prefixWord ++ tailWord_4074081).sum := by decide
  have hdescent : baseEnd_4074081 < baseStart_4074081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074169 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_4074169 : Nat := 118140960795 + 4074169 * 2 ^ 59
def prefixEnd_4074169 : Nat := 4983230072969 + 3 ^ 40 * 4074169 * 2
def baseEnd_4074169 : Nat := 1394671309765183685833829

theorem tailTrace_4074169 : CollatzResearch.WordTrace tailWord_4074169 prefixEnd_4074169 1394671309765183685833829 := by
  unfold tailWord_4074169
  simp only [CollatzResearch.WordTrace]
  refine ⟨148597151176989000513833561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99064767451326000342555707 148597151176989000513833561)
  ·
    refine ⟨111447863382741750385375171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148597151176989000513833561 111447863382741750385375171)
    ·
      refine ⟨167171795074112625578062757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111447863382741750385375171 167171795074112625578062757)
      ·
        refine ⟨31344711576396117295886767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167171795074112625578062757 31344711576396117295886767)
        ·
          refine ⟨47017067364594175943830151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31344711576396117295886767 47017067364594175943830151)
          ·
            refine ⟨70525601046891263915745227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47017067364594175943830151 70525601046891263915745227)
            ·
              refine ⟨105788401570336895873617841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70525601046891263915745227 105788401570336895873617841)
              ·
                refine ⟨79341301177752671905213381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105788401570336895873617841 79341301177752671905213381)
                ·
                  refine ⟨14876493970828625982227509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79341301177752671905213381 14876493970828625982227509)
                  ·
                    refine ⟨1394671309765183685833829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14876493970828625982227509 1394671309765183685833829)
                    ·
                      rfl

theorem cell22_4074169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_4074169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074169 prefixEnd_4074169 := by exact prefixLift 4074169
  have htrace : WordTrace (prefixWord ++ tailWord_4074169) baseStart_4074169 baseEnd_4074169 := by
    simpa [prefixWord, tailWord_4074169, baseEnd_4074169] using wordTrace_append hprefix tailTrace_4074169
  have hstable : (prefixWord ++ tailWord_4074169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074169).length < 2 ^ (prefixWord ++ tailWord_4074169).sum := by decide
  have hdescent : baseEnd_4074169 < baseStart_4074169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074188 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_4074188 : Nat := 118140960795 + 4074188 * 2 ^ 59
def prefixEnd_4074188 : Nat := 4983230072969 + 3 ^ 40 * 4074188 * 2
def baseEnd_4074188 : Nat := 464892604617824656536257

theorem tailTrace_4074188 : CollatzResearch.WordTrace tailWord_4074188 prefixEnd_4074188 464892604617824656536257 := by
  unfold tailWord_4074188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74298922081960083379387609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99065229442613444505850145 74298922081960083379387609)
  ·
    refine ⟨55724191561470062534540707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74298922081960083379387609 55724191561470062534540707)
    ·
      refine ⟨83586287342205093801811061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55724191561470062534540707 83586287342205093801811061)
      ·
        refine ⟨7836214438331727543919787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83586287342205093801811061 7836214438331727543919787)
        ·
          refine ⟨11754321657497591315879681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836214438331727543919787 11754321657497591315879681)
          ·
            refine ⟨8815741243123193486909761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754321657497591315879681 8815741243123193486909761)
            ·
              refine ⟨6611805932342395115182321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8815741243123193486909761 6611805932342395115182321)
              ·
                refine ⟨4958854449256796336386741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6611805932342395115182321 4958854449256796336386741)
                ·
                  refine ⟨464892604617824656536257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4958854449256796336386741 464892604617824656536257)
                  ·
                    rfl

theorem cell22_4074188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_4074188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074188 prefixEnd_4074188 := by exact prefixLift 4074188
  have htrace : WordTrace (prefixWord ++ tailWord_4074188) baseStart_4074188 baseEnd_4074188 := by
    simpa [prefixWord, tailWord_4074188, baseEnd_4074188] using wordTrace_append hprefix tailTrace_4074188
  have hstable : (prefixWord ++ tailWord_4074188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074188).length < 2 ^ (prefixWord ++ tailWord_4074188).sum := by decide
  have hdescent : baseEnd_4074188 < baseStart_4074188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074231 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 4, 3]
def baseStart_4074231 : Nat := 118140960795 + 4074231 * 2 ^ 59
def prefixEnd_4074231 : Nat := 4983230072969 + 3 ^ 40 * 4074231 * 2
def baseEnd_4074231 : Nat := 1394692533632236190783639

theorem tailTrace_4074231 : CollatzResearch.WordTrace tailWord_4074231 prefixEnd_4074231 1394692533632236190783639 := by
  unfold tailWord_4074231
  simp only [CollatzResearch.WordTrace]
  refine ⟨148599412502764385102590547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99066275001842923401727031 148599412502764385102590547)
  ·
    refine ⟨222899118754146577653885821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148599412502764385102590547 222899118754146577653885821)
    ·
      refine ⟨83587169532804966620207183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222899118754146577653885821 83587169532804966620207183)
      ·
        refine ⟨125380754299207449930310775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83587169532804966620207183 125380754299207449930310775)
        ·
          refine ⟨188071131448811174895466163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125380754299207449930310775 188071131448811174895466163)
          ·
            refine ⟨282106697173216762343199245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188071131448811174895466163 282106697173216762343199245)
            ·
              refine ⟨105790011439956285878699717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282106697173216762343199245 105790011439956285878699717)
              ·
                refine ⟨19835627144991803602256197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105790011439956285878699717 19835627144991803602256197)
                ·
                  refine ⟨3719180089685963175423037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19835627144991803602256197 3719180089685963175423037)
                  ·
                    refine ⟨1394692533632236190783639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719180089685963175423037 1394692533632236190783639)
                    ·
                      rfl

theorem cell22_4074231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_4074231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074231 prefixEnd_4074231 := by exact prefixLift 4074231
  have htrace : WordTrace (prefixWord ++ tailWord_4074231) baseStart_4074231 baseEnd_4074231 := by
    simpa [prefixWord, tailWord_4074231, baseEnd_4074231] using wordTrace_append hprefix tailTrace_4074231
  have hstable : (prefixWord ++ tailWord_4074231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074231).length < 2 ^ (prefixWord ++ tailWord_4074231).sum := by decide
  have hdescent : baseEnd_4074231 < baseStart_4074231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074248 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_4074248 : Nat := 118140960795 + 4074248 * 2 ^ 59
def prefixEnd_4074248 : Nat := 4983230072969 + 3 ^ 40 * 4074248 * 2
def baseEnd_4074248 : Nat := 1394698353079653813108587

theorem tailTrace_4074248 : CollatzResearch.WordTrace tailWord_4074248 prefixEnd_4074248 1394698353079653813108587 := by
  unfold tailWord_4074248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74300016271851398502979699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99066688362468531337306265 74300016271851398502979699)
  ·
    refine ⟨111450024407777097754469549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74300016271851398502979699 111450024407777097754469549)
    ·
      refine ⟨41793759152916411657926081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111450024407777097754469549 41793759152916411657926081)
      ·
        refine ⟨31345319364687308743444561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41793759152916411657926081 31345319364687308743444561)
        ·
          refine ⟨23508989523515481557583421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31345319364687308743444561 23508989523515481557583421)
          ·
            refine ⟨8815871071318305584093783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23508989523515481557583421 8815871071318305584093783)
            ·
              refine ⟨13223806606977458376140675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815871071318305584093783 13223806606977458376140675)
              ·
                refine ⟨19835709910466187564211013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13223806606977458376140675 19835709910466187564211013)
                ·
                  refine ⟨3719195608212410168289565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19835709910466187564211013 3719195608212410168289565)
                  ·
                    refine ⟨1394698353079653813108587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719195608212410168289565 1394698353079653813108587)
                    ·
                      rfl

theorem cell22_4074248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_4074248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074248 prefixEnd_4074248 := by exact prefixLift 4074248
  have htrace : WordTrace (prefixWord ++ tailWord_4074248) baseStart_4074248 baseEnd_4074248 := by
    simpa [prefixWord, tailWord_4074248, baseEnd_4074248] using wordTrace_append hprefix tailTrace_4074248
  have hstable : (prefixWord ++ tailWord_4074248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074248).length < 2 ^ (prefixWord ++ tailWord_4074248).sum := by decide
  have hdescent : baseEnd_4074248 < baseStart_4074248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074402 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_4074402 : Nat := 118140960795 + 4074402 * 2 ^ 59
def prefixEnd_4074402 : Nat := 4983230072969 + 3 ^ 40 * 4074402 * 2
def baseEnd_4074402 : Nat := 464917023475616248252705

theorem tailTrace_4074402 : CollatzResearch.WordTrace tailWord_4074402 prefixEnd_4074402 464917023475616248252705 := by
  unfold tailWord_4074402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37151412346286220326766365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99070432923429920871376973 37151412346286220326766365)
  ·
    refine ⟨13931779629857332622537387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37151412346286220326766365 13931779629857332622537387)
    ·
      refine ⟨20897669444785998933806081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13931779629857332622537387 20897669444785998933806081)
      ·
        refine ⟨15673252083589499200354561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20897669444785998933806081 15673252083589499200354561)
        ·
          refine ⟨11754939062692124400265921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15673252083589499200354561 11754939062692124400265921)
          ·
            refine ⟨8816204297019093300199441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754939062692124400265921 8816204297019093300199441)
            ·
              refine ⟨6612153222764319975149581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816204297019093300199441 6612153222764319975149581)
              ·
                refine ⟨2479557458536619990681093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6612153222764319975149581 2479557458536619990681093)
                ·
                  refine ⟨464917023475616248252705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479557458536619990681093 464917023475616248252705)
                  ·
                    rfl

theorem cell22_4074402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_4074402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074402 prefixEnd_4074402 := by exact prefixLift 4074402
  have htrace : WordTrace (prefixWord ++ tailWord_4074402) baseStart_4074402 baseEnd_4074402 := by
    simpa [prefixWord, tailWord_4074402, baseEnd_4074402] using wordTrace_append hprefix tailTrace_4074402
  have hstable : (prefixWord ++ tailWord_4074402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074402).length < 2 ^ (prefixWord ++ tailWord_4074402).sum := by decide
  have hdescent : baseEnd_4074402 < baseStart_4074402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074438 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4074438 : Nat := 118140960795 + 4074438 * 2 ^ 59
def prefixEnd_4074438 : Nat := 4983230072969 + 3 ^ 40 * 4074438 * 2
def baseEnd_4074438 : Nat := 1394763393962556650858005

theorem tailTrace_4074438 : CollatzResearch.WordTrace tailWord_4074438 prefixEnd_4074438 1394763393962556650858005 := by
  unfold tailWord_4074438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643967575406701857980499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99071308275342972970250645 4643967575406701857980499)
  ·
    refine ⟨6965951363110052786970749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4643967575406701857980499 6965951363110052786970749)
    ·
      refine ⟨2612231761166269795114031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6965951363110052786970749 2612231761166269795114031)
      ·
        refine ⟨3918347641749404692671047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612231761166269795114031 3918347641749404692671047)
        ·
          refine ⟨5877521462624107039006571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918347641749404692671047 5877521462624107039006571)
          ·
            refine ⟨8816282193936160558509857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877521462624107039006571 8816282193936160558509857)
            ·
              refine ⟨6612211645452120418882393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816282193936160558509857 6612211645452120418882393)
              ·
                refine ⟨4959158734089090314161795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612211645452120418882393 4959158734089090314161795)
                ·
                  refine ⟨7438738101133635471242693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959158734089090314161795 7438738101133635471242693)
                  ·
                    refine ⟨1394763393962556650858005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438738101133635471242693 1394763393962556650858005)
                    ·
                      rfl

theorem cell22_4074438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4074438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074438 prefixEnd_4074438 := by exact prefixLift 4074438
  have htrace : WordTrace (prefixWord ++ tailWord_4074438) baseStart_4074438 baseEnd_4074438 := by
    simpa [prefixWord, tailWord_4074438, baseEnd_4074438] using wordTrace_append hprefix tailTrace_4074438
  have hstable : (prefixWord ++ tailWord_4074438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074438).length < 2 ^ (prefixWord ++ tailWord_4074438).sum := by decide
  have hdescent : baseEnd_4074438 < baseStart_4074438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074441 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 11]
def baseStart_4074441 : Nat := 118140960795 + 4074441 * 2 ^ 59
def prefixEnd_4074441 : Nat := 4983230072969 + 3 ^ 40 * 4074441 * 2
def baseEnd_4074441 : Nat := 464921473641288547677665

theorem tailTrace_4074441 : CollatzResearch.WordTrace tailWord_4074441 prefixEnd_4074441 464921473641288547677665 := by
  unfold tailWord_4074441
  simp only [CollatzResearch.WordTrace]
  refine ⟨148607071832003590967735177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99071381221335727311823451 148607071832003590967735177)
  ·
    refine ⟨111455303874002693225801383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148607071832003590967735177 111455303874002693225801383)
    ·
      refine ⟨167182955811004039838702075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111455303874002693225801383 167182955811004039838702075)
      ·
        refine ⟨250774433716506059758053113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167182955811004039838702075 250774433716506059758053113)
        ·
          refine ⟨188080825287379544818539835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250774433716506059758053113 188080825287379544818539835)
          ·
            refine ⟨282121237931069317227809753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188080825287379544818539835 282121237931069317227809753)
            ·
              refine ⟨211590928448301987920857315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282121237931069317227809753 211590928448301987920857315)
              ·
                refine ⟨317386392672452981881285973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211590928448301987920857315 317386392672452981881285973)
                ·
                  refine ⟨464921473641288547677665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 317386392672452981881285973 464921473641288547677665)
                  ·
                    rfl

theorem cell22_4074441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_4074441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074441 prefixEnd_4074441 := by exact prefixLift 4074441
  have htrace : WordTrace (prefixWord ++ tailWord_4074441) baseStart_4074441 baseEnd_4074441 := by
    simpa [prefixWord, tailWord_4074441, baseEnd_4074441] using wordTrace_append hprefix tailTrace_4074441
  have hstable : (prefixWord ++ tailWord_4074441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074441).length < 2 ^ (prefixWord ++ tailWord_4074441).sum := by decide
  have hdescent : baseEnd_4074441 < baseStart_4074441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074458 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_4074458 : Nat := 118140960795 + 4074458 * 2 ^ 59
def prefixEnd_4074458 : Nat := 4983230072969 + 3 ^ 40 * 4074458 * 2
def baseEnd_4074458 : Nat := 464923413457094421785981

theorem tailTrace_4074458 : CollatzResearch.WordTrace tailWord_4074458 prefixEnd_4074458 464923413457094421785981 := by
  unfold tailWord_4074458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37151922968235500717776007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99071794581961335247402685 37151922968235500717776007)
  ·
    refine ⟨55727884452353251076664011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37151922968235500717776007 55727884452353251076664011)
    ·
      refine ⟨83591826678529876614996017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55727884452353251076664011 83591826678529876614996017)
      ·
        refine ⟨62693870008897407461247013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83591826678529876614996017 62693870008897407461247013)
        ·
          refine ⟨11755100626668263898983815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62693870008897407461247013 11755100626668263898983815)
          ·
            refine ⟨17632650940002395848475723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11755100626668263898983815 17632650940002395848475723)
            ·
              refine ⟨26448976410003593772713585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17632650940002395848475723 26448976410003593772713585)
              ·
                refine ⟨19836732307502695329535189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26448976410003593772713585 19836732307502695329535189)
                ·
                  refine ⟨464923413457094421785981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19836732307502695329535189 464923413457094421785981)
                  ·
                    rfl

theorem cell22_4074458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_4074458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074458 prefixEnd_4074458 := by exact prefixLift 4074458
  have htrace : WordTrace (prefixWord ++ tailWord_4074458) baseStart_4074458 baseEnd_4074458 := by
    simpa [prefixWord, tailWord_4074458, baseEnd_4074458] using wordTrace_append hprefix tailTrace_4074458
  have hstable : (prefixWord ++ tailWord_4074458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074458).length < 2 ^ (prefixWord ++ tailWord_4074458).sum := by decide
  have hdescent : baseEnd_4074458 < baseStart_4074458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074479 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 1, 3]
def baseStart_4074479 : Nat := 118140960795 + 4074479 * 2 ^ 59
def prefixEnd_4074479 : Nat := 4983230072969 + 3 ^ 40 * 4074479 * 2
def baseEnd_4074479 : Nat := 1394777429100446210582879

theorem tailTrace_4074479 : CollatzResearch.WordTrace tailWord_4074479 prefixEnd_4074479 1394777429100446210582879 := by
  unfold tailWord_4074479
  simp only [CollatzResearch.WordTrace]
  refine ⟨148608457805865923457618491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99072305203910615638412327 148608457805865923457618491)
  ·
    refine ⟨222912686708798885186427737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148608457805865923457618491 222912686708798885186427737)
    ·
      refine ⟨167184515031599163889820803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222912686708798885186427737 167184515031599163889820803)
      ·
        refine ⟨250776772547398745834731205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167184515031599163889820803 250776772547398745834731205)
        ·
          refine ⟨47020644852637264844012101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250776772547398745834731205 47020644852637264844012101)
          ·
            refine ⟨8816370909869487158252269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47020644852637264844012101 8816370909869487158252269)
            ·
              refine ⟨3306139091201057684344601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8816370909869487158252269 3306139091201057684344601)
              ·
                refine ⟨2479604318400793263258451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306139091201057684344601 2479604318400793263258451)
                ·
                  refine ⟨3719406477601189894887677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479604318400793263258451 3719406477601189894887677)
                  ·
                    refine ⟨1394777429100446210582879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719406477601189894887677 1394777429100446210582879)
                    ·
                      rfl

theorem cell22_4074479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_4074479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074479 prefixEnd_4074479 := by exact prefixLift 4074479
  have htrace : WordTrace (prefixWord ++ tailWord_4074479) baseStart_4074479 baseEnd_4074479 := by
    simpa [prefixWord, tailWord_4074479, baseEnd_4074479] using wordTrace_append hprefix tailTrace_4074479
  have hstable : (prefixWord ++ tailWord_4074479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074479).length < 2 ^ (prefixWord ++ tailWord_4074479).sum := by decide
  have hdescent : baseEnd_4074479 < baseStart_4074479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074488 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_4074488 : Nat := 118140960795 + 4074488 * 2 ^ 59
def prefixEnd_4074488 : Nat := 4983230072969 + 3 ^ 40 * 4074488 * 2
def baseEnd_4074488 : Nat := 1394780509984373187107851

theorem tailTrace_4074488 : CollatzResearch.WordTrace tailWord_4074488 prefixEnd_4074488 1394780509984373187107851 := by
  unfold tailWord_4074488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74304393031416658997348059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99072524041888878663130745 74304393031416658997348059)
  ·
    refine ⟨111456589547124988496022089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74304393031416658997348059 111456589547124988496022089)
    ·
      refine ⟨83592442160343741372016567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111456589547124988496022089 83592442160343741372016567)
      ·
        refine ⟨125388663240515612058024851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83592442160343741372016567 125388663240515612058024851)
        ·
          refine ⟨188082994860773418087037277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125388663240515612058024851 188082994860773418087037277)
          ·
            refine ⟨70531123072790031782638979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188082994860773418087037277 70531123072790031782638979)
            ·
              refine ⟨105796684609185047673958469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70531123072790031782638979 105796684609185047673958469)
              ·
                refine ⟨19836878364222196438867213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105796684609185047673958469 19836878364222196438867213)
                ·
                  refine ⟨7438829386583323664575205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19836878364222196438867213 7438829386583323664575205)
                  ·
                    refine ⟨1394780509984373187107851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438829386583323664575205 1394780509984373187107851)
                    ·
                      rfl

theorem cell22_4074488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_4074488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074488 prefixEnd_4074488 := by exact prefixLift 4074488
  have htrace : WordTrace (prefixWord ++ tailWord_4074488) baseStart_4074488 baseEnd_4074488 := by
    simpa [prefixWord, tailWord_4074488, baseEnd_4074488] using wordTrace_append hprefix tailTrace_4074488
  have hstable : (prefixWord ++ tailWord_4074488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074488).length < 2 ^ (prefixWord ++ tailWord_4074488).sum := by decide
  have hdescent : baseEnd_4074488 < baseStart_4074488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074492 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_4074492 : Nat := 118140960795 + 4074492 * 2 ^ 59
def prefixEnd_4074492 : Nat := 4983230072969 + 3 ^ 40 * 4074492 * 2
def baseEnd_4074492 : Nat := 464927293088706170002613

theorem tailTrace_4074492 : CollatzResearch.WordTrace tailWord_4074492 prefixEnd_4074492 464927293088706170002613 := by
  unfold tailWord_4074492
  simp only [CollatzResearch.WordTrace]
  refine ⟨74304465977409413338920865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99072621303212551118561153 74304465977409413338920865)
  ·
    refine ⟨55728349483057060004190649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74304465977409413338920865 55728349483057060004190649)
    ·
      refine ⟨41796262112292795003142987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55728349483057060004190649 41796262112292795003142987)
      ·
        refine ⟨62694393168439192504714481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41796262112292795003142987 62694393168439192504714481)
        ·
          refine ⟨47020794876329394378535861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62694393168439192504714481 47020794876329394378535861)
          ·
            refine ⟨4408199519655880722987737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47020794876329394378535861 4408199519655880722987737)
            ·
              refine ⟨3306149639741910542240803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408199519655880722987737 3306149639741910542240803)
              ·
                refine ⟨4959224459612865813361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306149639741910542240803 4959224459612865813361205)
                ·
                  refine ⟨464927293088706170002613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4959224459612865813361205 464927293088706170002613)
                  ·
                    rfl

theorem cell22_4074492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_4074492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074492 prefixEnd_4074492 := by exact prefixLift 4074492
  have htrace : WordTrace (prefixWord ++ tailWord_4074492) baseStart_4074492 baseEnd_4074492 := by
    simpa [prefixWord, tailWord_4074492, baseEnd_4074492] using wordTrace_append hprefix tailTrace_4074492
  have hstable : (prefixWord ++ tailWord_4074492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074492).length < 2 ^ (prefixWord ++ tailWord_4074492).sum := by decide
  have hdescent : baseEnd_4074492 < baseStart_4074492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074503 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 8]
def baseStart_4074503 : Nat := 118140960795 + 4074503 * 2 ^ 59
def prefixEnd_4074503 : Nat := 4983230072969 + 3 ^ 40 * 4074503 * 2
def baseEnd_4074503 : Nat := 464928548263639382660935

theorem tailTrace_4074503 : CollatzResearch.WordTrace tailWord_4074503 prefixEnd_4074503 464928548263639382660935 := by
  unfold tailWord_4074503
  simp only [CollatzResearch.WordTrace]
  refine ⟨148609333157778975556492163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99072888771852650370994775 148609333157778975556492163)
  ·
    refine ⟨222913999736668463334738245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148609333157778975556492163 222913999736668463334738245)
    ·
      refine ⟨41796374950625336875263421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222913999736668463334738245 41796374950625336875263421)
      ·
        refine ⟨15673640606484501328223783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41796374950625336875263421 15673640606484501328223783)
        ·
          refine ⟨23510460909726751992335675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15673640606484501328223783 23510460909726751992335675)
          ·
            refine ⟨35265691364590127988503513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23510460909726751992335675 35265691364590127988503513)
            ·
              refine ⟨26449268523442595991377635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35265691364590127988503513 26449268523442595991377635)
              ·
                refine ⟨39673902785163893987066453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26449268523442595991377635 39673902785163893987066453)
                ·
                  refine ⟨464928548263639382660935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39673902785163893987066453 464928548263639382660935)
                  ·
                    rfl

theorem cell22_4074503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_4074503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074503 prefixEnd_4074503 := by exact prefixLift 4074503
  have htrace : WordTrace (prefixWord ++ tailWord_4074503) baseStart_4074503 baseEnd_4074503 := by
    simpa [prefixWord, tailWord_4074503, baseEnd_4074503] using wordTrace_append hprefix tailTrace_4074503
  have hstable : (prefixWord ++ tailWord_4074503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074503).length < 2 ^ (prefixWord ++ tailWord_4074503).sum := by decide
  have hdescent : baseEnd_4074503 < baseStart_4074503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074522 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_4074522 : Nat := 118140960795 + 4074522 * 2 ^ 59
def prefixEnd_4074522 : Nat := 4983230072969 + 3 ^ 40 * 4074522 * 2
def baseEnd_4074522 : Nat := 1394792148879208431757747

theorem tailTrace_4074522 : CollatzResearch.WordTrace tailWord_4074522 prefixEnd_4074522 1394792148879208431757747 := by
  unfold tailWord_4074522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37152506536177535450358455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99073350763140094534289213 37152506536177535450358455)
  ·
    refine ⟨55728759804266303175537683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37152506536177535450358455 55728759804266303175537683)
    ·
      refine ⟨83593139706399454763306525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55728759804266303175537683 83593139706399454763306525)
      ·
        refine ⟨31347427389899795536239947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83593139706399454763306525 31347427389899795536239947)
        ·
          refine ⟨47021141084849693304359921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31347427389899795536239947 47021141084849693304359921)
          ·
            refine ⟨35265855813637269978269941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47021141084849693304359921 35265855813637269978269941)
            ·
              refine ⟨3306173982528494060462807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35265855813637269978269941 3306173982528494060462807)
              ·
                refine ⟨4959260973792741090694211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306173982528494060462807 4959260973792741090694211)
                ·
                  refine ⟨7438891460689111636041317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959260973792741090694211 7438891460689111636041317)
                  ·
                    refine ⟨1394792148879208431757747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438891460689111636041317 1394792148879208431757747)
                    ·
                      rfl

theorem cell22_4074522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_4074522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074522 prefixEnd_4074522 := by exact prefixLift 4074522
  have htrace : WordTrace (prefixWord ++ tailWord_4074522) baseStart_4074522 baseEnd_4074522 := by
    simpa [prefixWord, tailWord_4074522, baseEnd_4074522] using wordTrace_append hprefix tailTrace_4074522
  have hstable : (prefixWord ++ tailWord_4074522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074522).length < 2 ^ (prefixWord ++ tailWord_4074522).sum := by decide
  have hdescent : baseEnd_4074522 < baseStart_4074522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074552 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_4074552 : Nat := 118140960795 + 4074552 * 2 ^ 59
def prefixEnd_4074552 : Nat := 4983230072969 + 3 ^ 40 * 4074552 * 2
def baseEnd_4074552 : Nat := 1394802418492298353507655

theorem tailTrace_4074552 : CollatzResearch.WordTrace tailWord_4074552 prefixEnd_4074552 1394802418492298353507655 := by
  unfold tailWord_4074552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74305560167300728462512955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99074080223067637950017273 74305560167300728462512955)
  ·
    refine ⟨111458340250951092693769433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74305560167300728462512955 111458340250951092693769433)
    ·
      refine ⟨83593755188213319520327075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111458340250951092693769433 83593755188213319520327075)
      ·
        refine ⟨125390632782319979280490613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83593755188213319520327075 125390632782319979280490613)
        ·
          refine ⟨11755371823342498057545995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125390632782319979280490613 11755371823342498057545995)
          ·
            refine ⟨17633057735013747086318993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11755371823342498057545995 17633057735013747086318993)
            ·
              refine ⟨13224793301260310314739245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17633057735013747086318993 13224793301260310314739245)
              ·
                refine ⟨4959297487972616368027217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13224793301260310314739245 4959297487972616368027217)
                ·
                  refine ⟨3719473115979462276020413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959297487972616368027217 3719473115979462276020413)
                  ·
                    refine ⟨1394802418492298353507655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719473115979462276020413 1394802418492298353507655)
                    ·
                      rfl

theorem cell22_4074552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_4074552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074552 prefixEnd_4074552 := by exact prefixLift 4074552
  have htrace : WordTrace (prefixWord ++ tailWord_4074552) baseStart_4074552 baseEnd_4074552 := by
    simpa [prefixWord, tailWord_4074552, baseEnd_4074552] using wordTrace_append hprefix tailTrace_4074552
  have hstable : (prefixWord ++ tailWord_4074552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074552).length < 2 ^ (prefixWord ++ tailWord_4074552).sum := by decide
  have hdescent : baseEnd_4074552 < baseStart_4074552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074567 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 2, 4]
def baseStart_4074567 : Nat := 118140960795 + 4074567 * 2 ^ 59
def prefixEnd_4074567 : Nat := 4983230072969 + 3 ^ 40 * 4074567 * 2
def baseEnd_4074567 : Nat := 1394807553298843314382609

theorem tailTrace_4074567 : CollatzResearch.WordTrace tailWord_4074567 prefixEnd_4074567 1394807553298843314382609 := by
  unfold tailWord_4074567
  simp only [CollatzResearch.WordTrace]
  refine ⟨148611667429547114486821955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99074444953031409657881303 148611667429547114486821955)
  ·
    refine ⟨222917501144320671730232933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148611667429547114486821955 222917501144320671730232933)
    ·
      refine ⟨41797031464560125949418675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222917501144320671730232933 41797031464560125949418675)
      ·
        refine ⟨62695547196840188924128013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41797031464560125949418675 62695547196840188924128013)
        ·
          refine ⟨23510830198815070846548005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62695547196840188924128013 23510830198815070846548005)
          ·
            refine ⟨4408280662277825783727751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23510830198815070846548005 4408280662277825783727751)
            ·
              refine ⟨6612420993416738675591627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408280662277825783727751 6612420993416738675591627)
              ·
                refine ⟨9918631490125108013387441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612420993416738675591627 9918631490125108013387441)
                ·
                  refine ⟨7438973617593831010040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9918631490125108013387441 7438973617593831010040581)
                  ·
                    refine ⟨1394807553298843314382609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7438973617593831010040581 1394807553298843314382609)
                    ·
                      rfl

theorem cell22_4074567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_4074567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074567 prefixEnd_4074567 := by exact prefixLift 4074567
  have htrace : WordTrace (prefixWord ++ tailWord_4074567) baseStart_4074567 baseEnd_4074567 := by
    simpa [prefixWord, tailWord_4074567, baseEnd_4074567] using wordTrace_append hprefix tailTrace_4074567
  have hstable : (prefixWord ++ tailWord_4074567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074567).length < 2 ^ (prefixWord ++ tailWord_4074567).sum := by decide
  have hdescent : baseEnd_4074567 < baseStart_4074567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074597 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_4074597 : Nat := 118140960795 + 4074597 * 2 ^ 59
def prefixEnd_4074597 : Nat := 4983230072969 + 3 ^ 40 * 4074597 * 2
def baseEnd_4074597 : Nat := 1394817822911933236132517

theorem tailTrace_4074597 : CollatzResearch.WordTrace tailWord_4074597 prefixEnd_4074597 1394817822911933236132517 := by
  unfold tailWord_4074597
  simp only [CollatzResearch.WordTrace]
  refine ⟨148612761619438429610414045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99075174412958953073609363 148612761619438429610414045)
  ·
    refine ⟨55729785607289411103905267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148612761619438429610414045 55729785607289411103905267)
    ·
      refine ⟨83594678410934116655857901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55729785607289411103905267 83594678410934116655857901)
      ·
        refine ⟨31348004404100293745946713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83594678410934116655857901 31348004404100293745946713)
        ·
          refine ⟨23511003303075220309460035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31348004404100293745946713 23511003303075220309460035)
          ·
            refine ⟨35266504954612830464190053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23511003303075220309460035 35266504954612830464190053)
            ·
              refine ⟨6612469678989905712035635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35266504954612830464190053 6612469678989905712035635)
              ·
                refine ⟨9918704518484858568053453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612469678989905712035635 9918704518484858568053453)
                ·
                  refine ⟨3719514194431821963020045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9918704518484858568053453 3719514194431821963020045)
                  ·
                    refine ⟨1394817822911933236132517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719514194431821963020045 1394817822911933236132517)
                    ·
                      rfl

theorem cell22_4074597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_4074597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074597 prefixEnd_4074597 := by exact prefixLift 4074597
  have htrace : WordTrace (prefixWord ++ tailWord_4074597) baseStart_4074597 baseEnd_4074597 := by
    simpa [prefixWord, tailWord_4074597, baseEnd_4074597] using wordTrace_append hprefix tailTrace_4074597
  have hstable : (prefixWord ++ tailWord_4074597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074597).length < 2 ^ (prefixWord ++ tailWord_4074597).sum := by decide
  have hdescent : baseEnd_4074597 < baseStart_4074597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074623 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_4074623 : Nat := 118140960795 + 4074623 * 2 ^ 59
def prefixEnd_4074623 : Nat := 4983230072969 + 3 ^ 40 * 4074623 * 2
def baseEnd_4074623 : Nat := 1394826723243277834982437

theorem tailTrace_4074623 : CollatzResearch.WordTrace tailWord_4074623 prefixEnd_4074623 1394826723243277834982437 := by
  unfold tailWord_4074623
  simp only [CollatzResearch.WordTrace]
  refine ⟨148613709917344236050860523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99075806611562824033907015 148613709917344236050860523)
  ·
    refine ⟨222920564876016354076290785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148613709917344236050860523 222920564876016354076290785)
    ·
      refine ⟨167190423657012265557218089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222920564876016354076290785 167190423657012265557218089)
      ·
        refine ⟨125392817742759199167913567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167190423657012265557218089 125392817742759199167913567)
        ·
          refine ⟨188089226614138798751870351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125392817742759199167913567 188089226614138798751870351)
          ·
            refine ⟨282133839921208198127805527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188089226614138798751870351 282133839921208198127805527)
            ·
              refine ⟨423200759881812297191708291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282133839921208198127805527 423200759881812297191708291)
              ·
                refine ⟨634801139822718445787562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423200759881812297191708291 634801139822718445787562437)
                ·
                  refine ⟨119025213716759708585167957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 634801139822718445787562437 119025213716759708585167957)
                  ·
                    refine ⟨1394826723243277834982437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119025213716759708585167957 1394826723243277834982437)
                    ·
                      rfl

theorem cell22_4074623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_4074623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074623 prefixEnd_4074623 := by exact prefixLift 4074623
  have htrace : WordTrace (prefixWord ++ tailWord_4074623) baseStart_4074623 baseEnd_4074623 := by
    simpa [prefixWord, tailWord_4074623, baseEnd_4074623] using wordTrace_append hprefix tailTrace_4074623
  have hstable : (prefixWord ++ tailWord_4074623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074623).length < 2 ^ (prefixWord ++ tailWord_4074623).sum := by decide
  have hdescent : baseEnd_4074623 < baseStart_4074623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074674 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_4074674 : Nat := 118140960795 + 4074674 * 2 ^ 59
def prefixEnd_4074674 : Nat := 4983230072969 + 3 ^ 40 * 4074674 * 2
def baseEnd_4074674 : Nat := 1394844181585530701957281

theorem tailTrace_4074674 : CollatzResearch.WordTrace tailWord_4074674 prefixEnd_4074674 1394844181585530701957281 := by
  unfold tailWord_4074674
  simp only [CollatzResearch.WordTrace]
  refine ⟨37153892510039867940241769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99077046693439647840644717 37153892510039867940241769)
  ·
    refine ⟨27865419382529900955181327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37153892510039867940241769 27865419382529900955181327)
    ·
      refine ⟨41798129073794851432771991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27865419382529900955181327 41798129073794851432771991)
      ·
        refine ⟨62697193610692277149157987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41798129073794851432771991 62697193610692277149157987)
        ·
          refine ⟨94045790416038415723736981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62697193610692277149157987 94045790416038415723736981)
          ·
            refine ⟨4408396425751800737050171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94045790416038415723736981 4408396425751800737050171)
            ·
              refine ⟨6612594638627701105575257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408396425751800737050171 6612594638627701105575257)
              ·
                refine ⟨4959445978970775829181443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612594638627701105575257 4959445978970775829181443)
                ·
                  refine ⟨7439168968456163743772165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959445978970775829181443 7439168968456163743772165)
                  ·
                    refine ⟨1394844181585530701957281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7439168968456163743772165 1394844181585530701957281)
                    ·
                      rfl

theorem cell22_4074674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_4074674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074674 prefixEnd_4074674 := by exact prefixLift 4074674
  have htrace : WordTrace (prefixWord ++ tailWord_4074674) baseStart_4074674 baseEnd_4074674 := by
    simpa [prefixWord, tailWord_4074674, baseEnd_4074674] using wordTrace_append hprefix tailTrace_4074674
  have hstable : (prefixWord ++ tailWord_4074674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074674).length < 2 ^ (prefixWord ++ tailWord_4074674).sum := by decide
  have hdescent : baseEnd_4074674 < baseStart_4074674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074685 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4074685 : Nat := 118140960795 + 4074685 * 2 ^ 59
def prefixEnd_4074685 : Nat := 4983230072969 + 3 ^ 40 * 4074685 * 2
def baseEnd_4074685 : Nat := 1394847947110330339932247

theorem tailTrace_4074685 : CollatzResearch.WordTrace tailWord_4074685 prefixEnd_4074685 1394847947110330339932247 := by
  unfold tailWord_4074685
  simp only [CollatzResearch.WordTrace]
  refine ⟨148615971243119620639617509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99077314162079747093078339 148615971243119620639617509)
  ·
    refine ⟨27865494608084928869928283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148615971243119620639617509 27865494608084928869928283)
    ·
      refine ⟨41798241912127393304892425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27865494608084928869928283 41798241912127393304892425)
      ·
        refine ⟨31348681434095544978669319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41798241912127393304892425 31348681434095544978669319)
        ·
          refine ⟨47023022151143317468003979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31348681434095544978669319 47023022151143317468003979)
          ·
            refine ⟨70534533226714976202005969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47023022151143317468003979 70534533226714976202005969)
            ·
              refine ⟨52900899920036232151504477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70534533226714976202005969 52900899920036232151504477)
              ·
                refine ⟨19837837470013587056814179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52900899920036232151504477 19837837470013587056814179)
                ·
                  refine ⟨29756756205020380585221269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19837837470013587056814179 29756756205020380585221269)
                  ·
                    refine ⟨1394847947110330339932247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29756756205020380585221269 1394847947110330339932247)
                    ·
                      rfl

theorem cell22_4074685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4074685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074685 prefixEnd_4074685 := by exact prefixLift 4074685
  have htrace : WordTrace (prefixWord ++ tailWord_4074685) baseStart_4074685 baseEnd_4074685 := by
    simpa [prefixWord, tailWord_4074685, baseEnd_4074685] using wordTrace_append hprefix tailTrace_4074685
  have hstable : (prefixWord ++ tailWord_4074685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074685).length < 2 ^ (prefixWord ++ tailWord_4074685).sum := by decide
  have hdescent : baseEnd_4074685 < baseStart_4074685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074732 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_4074732 : Nat := 118140960795 + 4074732 * 2 ^ 59
def prefixEnd_4074732 : Nat := 4983230072969 + 3 ^ 40 * 4074732 * 2
def baseEnd_4074732 : Nat := 1394864036170837884007103

theorem tailTrace_4074732 : CollatzResearch.WordTrace tailWord_4074732 prefixEnd_4074732 1394864036170837884007103 := by
  unfold tailWord_4074732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74308842736974673833289225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99078456982632898444385633 74308842736974673833289225)
  ·
    refine ⟨55731632052731005374966919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74308842736974673833289225 55731632052731005374966919)
    ·
      refine ⟨83597448079096508062450379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55731632052731005374966919 83597448079096508062450379)
      ·
        refine ⟨125396172118644762093675569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83597448079096508062450379 125396172118644762093675569)
        ·
          refine ⟨94047129088983571570256677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125396172118644762093675569 94047129088983571570256677)
          ·
            refine ⟨17633836704184419669423127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94047129088983571570256677 17633836704184419669423127)
            ·
              refine ⟨26450755056276629504134691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17633836704184419669423127 26450755056276629504134691)
              ·
                refine ⟨39676132584414944256202037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26450755056276629504134691 39676132584414944256202037)
                ·
                  refine ⟨3719637429788901024018941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39676132584414944256202037 3719637429788901024018941)
                  ·
                    refine ⟨1394864036170837884007103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719637429788901024018941 1394864036170837884007103)
                    ·
                      rfl

theorem cell22_4074732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_4074732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074732 prefixEnd_4074732 := by exact prefixLift 4074732
  have htrace : WordTrace (prefixWord ++ tailWord_4074732) baseStart_4074732 baseEnd_4074732 := by
    simpa [prefixWord, tailWord_4074732, baseEnd_4074732] using wordTrace_append hprefix tailTrace_4074732
  have hstable : (prefixWord ++ tailWord_4074732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074732).length < 2 ^ (prefixWord ++ tailWord_4074732).sum := by decide
  have hdescent : baseEnd_4074732 < baseStart_4074732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074740 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4074740 : Nat := 118140960795 + 4074740 * 2 ^ 59
def prefixEnd_4074740 : Nat := 4983230072969 + 3 ^ 40 * 4074740 * 2
def baseEnd_4074740 : Nat := 464955591578109509935693

theorem tailTrace_4074740 : CollatzResearch.WordTrace tailWord_4074740 prefixEnd_4074740 464955591578109509935693 := by
  unfold tailWord_4074740
  simp only [CollatzResearch.WordTrace]
  refine ⟨74308988628960182516434837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99078651505280243355246449 74308988628960182516434837)
  ·
    refine ⟨3483233841982508555457883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74308988628960182516434837 3483233841982508555457883)
    ·
      refine ⟨5224850762973762833186825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483233841982508555457883 5224850762973762833186825)
      ·
        refine ⟨3918638072230322124890119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5224850762973762833186825 3918638072230322124890119)
        ·
          refine ⟨5877957108345483187335179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918638072230322124890119 5877957108345483187335179)
          ·
            refine ⟨8816935662518224781002769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877957108345483187335179 8816935662518224781002769)
            ·
              refine ⟨6612701746888668585752077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816935662518224781002769 6612701746888668585752077)
              ·
                refine ⟨2479763155083250719657029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6612701746888668585752077 2479763155083250719657029)
                ·
                  refine ⟨464955591578109509935693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479763155083250719657029 464955591578109509935693)
                  ·
                    rfl

theorem cell22_4074740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4074740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074740 prefixEnd_4074740 := by exact prefixLift 4074740
  have htrace : WordTrace (prefixWord ++ tailWord_4074740) baseStart_4074740 baseEnd_4074740 := by
    simpa [prefixWord, tailWord_4074740, baseEnd_4074740] using wordTrace_append hprefix tailTrace_4074740
  have hstable : (prefixWord ++ tailWord_4074740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074740).length < 2 ^ (prefixWord ++ tailWord_4074740).sum := by decide
  have hdescent : baseEnd_4074740 < baseStart_4074740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074745 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 7]
def baseStart_4074745 : Nat := 118140960795 + 4074745 * 2 ^ 59
def prefixEnd_4074745 : Nat := 4983230072969 + 3 ^ 40 * 4074745 * 2
def baseEnd_4074745 : Nat := 464956162112170061144021

theorem tailTrace_4074745 : CollatzResearch.WordTrace tailWord_4074745 prefixEnd_4074745 464956162112170061144021 := by
  unfold tailWord_4074745
  simp only [CollatzResearch.WordTrace]
  refine ⟨148618159622902250886801689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99078773081934833924534459 148618159622902250886801689)
  ·
    refine ⟨111463619717176688165101267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148618159622902250886801689 111463619717176688165101267)
    ·
      refine ⟨167195429575765032247651901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111463619717176688165101267 167195429575765032247651901)
      ·
        refine ⟨62698286090911887092869463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167195429575765032247651901 62698286090911887092869463)
        ·
          refine ⟨94047429136367830639304195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62698286090911887092869463 94047429136367830639304195)
          ·
            refine ⟨141071143704551745958956293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94047429136367830639304195 141071143704551745958956293)
            ·
              refine ⟨26450839444603452367304305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141071143704551745958956293 26450839444603452367304305)
              ·
                refine ⟨19838129583452589275478229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26450839444603452367304305 19838129583452589275478229)
                ·
                  refine ⟨464956162112170061144021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19838129583452589275478229 464956162112170061144021)
                  ·
                    rfl

theorem cell22_4074745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_4074745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074745 prefixEnd_4074745 := by exact prefixLift 4074745
  have htrace : WordTrace (prefixWord ++ tailWord_4074745) baseStart_4074745 baseEnd_4074745 := by
    simpa [prefixWord, tailWord_4074745, baseEnd_4074745] using wordTrace_append hprefix tailTrace_4074745
  have hstable : (prefixWord ++ tailWord_4074745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074745).length < 2 ^ (prefixWord ++ tailWord_4074745).sum := by decide
  have hdescent : baseEnd_4074745 < baseStart_4074745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074766 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_4074766 : Nat := 118140960795 + 4074766 * 2 ^ 59
def prefixEnd_4074766 : Nat := 4983230072969 + 3 ^ 40 * 4074766 * 2
def baseEnd_4074766 : Nat := 1394875675065673128656999

theorem tailTrace_4074766 : CollatzResearch.WordTrace tailWord_4074766 prefixEnd_4074766 1394875675065673128656999 := by
  unfold tailWord_4074766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577365694478271434164519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99079283703884114315544101 18577365694478271434164519)
  ·
    refine ⟨27866048541717407151246779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18577365694478271434164519 27866048541717407151246779)
    ·
      refine ⟨41799072812576110726870169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27866048541717407151246779 41799072812576110726870169)
      ·
        refine ⟨31349304609432083045152627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41799072812576110726870169 31349304609432083045152627)
        ·
          refine ⟨47023956914148124567728941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31349304609432083045152627 47023956914148124567728941)
          ·
            refine ⟨17633983842805546712898353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47023956914148124567728941 17633983842805546712898353)
            ·
              refine ⟨13225487882104160034673765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17633983842805546712898353 13225487882104160034673765)
              ·
                refine ⟨2479778977894530006501331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13225487882104160034673765 2479778977894530006501331)
                ·
                  refine ⟨3719668466841795009751997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479778977894530006501331 3719668466841795009751997)
                  ·
                    refine ⟨1394875675065673128656999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719668466841795009751997 1394875675065673128656999)
                    ·
                      rfl

theorem cell22_4074766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_4074766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074766 prefixEnd_4074766 := by exact prefixLift 4074766
  have htrace : WordTrace (prefixWord ++ tailWord_4074766) baseStart_4074766 baseEnd_4074766 := by
    simpa [prefixWord, tailWord_4074766, baseEnd_4074766] using wordTrace_append hprefix tailTrace_4074766
  have hstable : (prefixWord ++ tailWord_4074766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074766).length < 2 ^ (prefixWord ++ tailWord_4074766).sum := by decide
  have hdescent : baseEnd_4074766 < baseStart_4074766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074852 : List Nat := [2, 3, 1, 1, 3, 2, 2, 8]
def baseStart_4074852 : Nat := 118140960795 + 4074852 * 2 ^ 59
def prefixEnd_4074852 : Nat := 4983230072969 + 3 ^ 40 * 4074852 * 2
def baseEnd_4074852 : Nat := 154989457180355285667415

theorem tailTrace_4074852 : CollatzResearch.WordTrace tailWord_4074852 prefixEnd_4074852 154989457180355285667415 := by
  unfold tailWord_4074852
  simp only [CollatzResearch.WordTrace]
  refine ⟨74311031116757304080473405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99081374822343072107297873 74311031116757304080473405)
  ·
    refine ⟨27866636668783989030177527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74311031116757304080473405 27866636668783989030177527)
    ·
      refine ⟨41799955003175983545266291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27866636668783989030177527 41799955003175983545266291)
      ·
        refine ⟨62699932504763975317899437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41799955003175983545266291 62699932504763975317899437)
        ·
          refine ⟨23512474689286490744212289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62699932504763975317899437 23512474689286490744212289)
          ·
            refine ⟨17634356016964868058159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23512474689286490744212289 17634356016964868058159217)
            ·
              refine ⟨13225767012723651043619413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17634356016964868058159217 13225767012723651043619413)
              ·
                refine ⟨154989457180355285667415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13225767012723651043619413 154989457180355285667415)
                ·
                  rfl

theorem cell22_4074852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_4074852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074852 prefixEnd_4074852 := by exact prefixLift 4074852
  have htrace : WordTrace (prefixWord ++ tailWord_4074852) baseStart_4074852 baseEnd_4074852 := by
    simpa [prefixWord, tailWord_4074852, baseEnd_4074852] using wordTrace_append hprefix tailTrace_4074852
  have hstable : (prefixWord ++ tailWord_4074852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074852).length < 2 ^ (prefixWord ++ tailWord_4074852).sum := by decide
  have hdescent : baseEnd_4074852 < baseStart_4074852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074869 : List Nat := [1, 3, 4, 1, 4, 9]
def baseStart_4074869 : Nat := 118140960795 + 4074869 * 2 ^ 59
def prefixEnd_4074869 : Nat := 4983230072969 + 3 ^ 40 * 4074869 * 2
def baseEnd_4074869 : Nat := 17221122642847101152243

theorem tailTrace_4074869 : CollatzResearch.WordTrace tailWord_4074869 prefixEnd_4074869 17221122642847101152243 := by
  unfold tailWord_4074869
  simp only [CollatzResearch.WordTrace]
  refine ⟨148622682274453020064315661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99081788182968680042877107 148622682274453020064315661)
  ·
    refine ⟨55733505852919882524118373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148622682274453020064315661 55733505852919882524118373)
    ·
      refine ⟨10450032347422477973272195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55733505852919882524118373 10450032347422477973272195)
      ·
        refine ⟨15675048521133716959908293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450032347422477973272195 15675048521133716959908293)
        ·
          refine ⟨2939071597712571929982805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15675048521133716959908293 2939071597712571929982805)
          ·
            refine ⟨17221122642847101152243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2939071597712571929982805 17221122642847101152243)
            ·
              rfl

theorem cell22_4074869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 9].length) (baseStart_4074869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074869 prefixEnd_4074869 := by exact prefixLift 4074869
  have htrace : WordTrace (prefixWord ++ tailWord_4074869) baseStart_4074869 baseEnd_4074869 := by
    simpa [prefixWord, tailWord_4074869, baseEnd_4074869] using wordTrace_append hprefix tailTrace_4074869
  have hstable : (prefixWord ++ tailWord_4074869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074869).length < 2 ^ (prefixWord ++ tailWord_4074869).sum := by decide
  have hdescent : baseEnd_4074869 < baseStart_4074869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074912 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_4074912 : Nat := 118140960795 + 4074912 * 2 ^ 59
def prefixEnd_4074912 : Nat := 4983230072969 + 3 ^ 40 * 4074912 * 2
def baseEnd_4074912 : Nat := 1394925653849377414506551

theorem tailTrace_4074912 : CollatzResearch.WordTrace tailWord_4074912 prefixEnd_4074912 1394925653849377414506551 := by
  unfold tailWord_4074912
  simp only [CollatzResearch.WordTrace]
  refine ⟨74312125306648619204065495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99082833742198158938753993 74312125306648619204065495)
  ·
    refine ⟨111468187959972928806098243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74312125306648619204065495 111468187959972928806098243)
    ·
      refine ⟨167202281939959393209147365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111468187959972928806098243 167202281939959393209147365)
      ·
        refine ⟨31350427863742386226715131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167202281939959393209147365 31350427863742386226715131)
        ·
          refine ⟨47025641795613579340072697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31350427863742386226715131 47025641795613579340072697)
          ·
            refine ⟨35269231346710184505054523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47025641795613579340072697 35269231346710184505054523)
            ·
              refine ⟨52903847020065276757581785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35269231346710184505054523 52903847020065276757581785)
              ·
                refine ⟨39677885265048957568186339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52903847020065276757581785 39677885265048957568186339)
                ·
                  refine ⟨59516827897573436352279509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39677885265048957568186339 59516827897573436352279509)
                  ·
                    refine ⟨1394925653849377414506551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59516827897573436352279509 1394925653849377414506551)
                    ·
                      rfl

theorem cell22_4074912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_4074912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074912 prefixEnd_4074912 := by exact prefixLift 4074912
  have htrace : WordTrace (prefixWord ++ tailWord_4074912) baseStart_4074912 baseEnd_4074912 := by
    simpa [prefixWord, tailWord_4074912, baseEnd_4074912] using wordTrace_append hprefix tailTrace_4074912
  have hstable : (prefixWord ++ tailWord_4074912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074912).length < 2 ^ (prefixWord ++ tailWord_4074912).sum := by decide
  have hdescent : baseEnd_4074912 < baseStart_4074912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074948 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_4074948 : Nat := 118140960795 + 4074948 * 2 ^ 59
def prefixEnd_4074948 : Nat := 4983230072969 + 3 ^ 40 * 4074948 * 2
def baseEnd_4074948 : Nat := 464979325795028440202147

theorem tailTrace_4074948 : CollatzResearch.WordTrace tailWord_4074948 prefixEnd_4074948 464979325795028440202147 := by
  unfold tailWord_4074948
  simp only [CollatzResearch.WordTrace]
  refine ⟨74312781820583408278220749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99083709094111211037627665 74312781820583408278220749)
  ·
    refine ⟨27867293182718778104332781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74312781820583408278220749 27867293182718778104332781)
    ·
      refine ⟨10450234943519541789124793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27867293182718778104332781 10450234943519541789124793)
      ·
        refine ⟨7837676207639656341843595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10450234943519541789124793 7837676207639656341843595)
        ·
          refine ⟨11756514311459484512765393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837676207639656341843595 11756514311459484512765393)
          ·
            refine ⟨8817385733594613384574045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11756514311459484512765393 8817385733594613384574045)
            ·
              refine ⟨3306519650097980019215267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8817385733594613384574045 3306519650097980019215267)
              ·
                refine ⟨4959779475146970028822901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306519650097980019215267 4959779475146970028822901)
                ·
                  refine ⟨464979325795028440202147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4959779475146970028822901 464979325795028440202147)
                  ·
                    rfl

theorem cell22_4074948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_4074948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074948 prefixEnd_4074948 := by exact prefixLift 4074948
  have htrace : WordTrace (prefixWord ++ tailWord_4074948) baseStart_4074948 baseEnd_4074948 := by
    simpa [prefixWord, tailWord_4074948, baseEnd_4074948] using wordTrace_append hprefix tailTrace_4074948
  have hstable : (prefixWord ++ tailWord_4074948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074948).length < 2 ^ (prefixWord ++ tailWord_4074948).sum := by decide
  have hdescent : baseEnd_4074948 < baseStart_4074948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074993 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 4]
def baseStart_4074993 : Nat := 118140960795 + 4074993 * 2 ^ 59
def prefixEnd_4074993 : Nat := 4983230072969 + 3 ^ 40 * 4074993 * 2
def baseEnd_4074993 : Nat := 464984460601573401077101

theorem tailTrace_4074993 : CollatzResearch.WordTrace tailWord_4074993 prefixEnd_4074993 464984460601573401077101 := by
  unfold tailWord_4074993
  simp only [CollatzResearch.WordTrace]
  refine ⟨148627204926003789241829633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99084803284002526161219755 148627204926003789241829633)
  ·
    refine ⟨111470403694502841931372225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148627204926003789241829633 111470403694502841931372225)
    ·
      refine ⟨83602802770877131448529169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111470403694502841931372225 83602802770877131448529169)
      ·
        refine ⟨62702102078157848586396877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83602802770877131448529169 62702102078157848586396877)
        ·
          refine ⟨23513288279309193219898829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62702102078157848586396877 23513288279309193219898829)
          ·
            refine ⟨8817483104740947457462061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23513288279309193219898829 8817483104740947457462061)
            ·
              refine ⟨3306556164277855296548273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8817483104740947457462061 3306556164277855296548273)
              ·
                refine ⟨2479917123208391472411205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306556164277855296548273 2479917123208391472411205)
                ·
                  refine ⟨464984460601573401077101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479917123208391472411205 464984460601573401077101)
                  ·
                    rfl

theorem cell22_4074993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_4074993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4074993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4074993 prefixEnd_4074993 := by exact prefixLift 4074993
  have htrace : WordTrace (prefixWord ++ tailWord_4074993) baseStart_4074993 baseEnd_4074993 := by
    simpa [prefixWord, tailWord_4074993, baseEnd_4074993] using wordTrace_append hprefix tailTrace_4074993
  have hstable : (prefixWord ++ tailWord_4074993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074993).length < 2 ^ (prefixWord ++ tailWord_4074993).sum := by decide
  have hdescent : baseEnd_4074993 < baseStart_4074993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075038 : List Nat := [4, 3, 3, 1, 11]
def baseStart_4075038 : Nat := 118140960795 + 4075038 * 2 ^ 59
def prefixEnd_4075038 : Nat := 4983230072969 + 3 ^ 40 * 4075038 * 2
def baseEnd_4075038 : Nat := 5740612288989115579655

theorem tailTrace_4075038 : CollatzResearch.WordTrace tailWord_4075038 prefixEnd_4075038 5740612288989115579655 := by
  unfold tailWord_4075038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578605776355095240902221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99085897473893841284811845 18578605776355095240902221)
  ·
    refine ⟨6966977166133160715338333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18578605776355095240902221 6966977166133160715338333)
    ·
      refine ⟨2612616437299935268251875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6966977166133160715338333 2612616437299935268251875)
      ·
        refine ⟨3918924655949902902377813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612616437299935268251875 3918924655949902902377813)
        ·
          refine ⟨5740612288989115579655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3918924655949902902377813 5740612288989115579655)
          ·
            rfl

theorem cell22_4075038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 11].length) (baseStart_4075038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075038 prefixEnd_4075038 := by exact prefixLift 4075038
  have htrace : WordTrace (prefixWord ++ tailWord_4075038) baseStart_4075038 baseEnd_4075038 := by
    simpa [prefixWord, tailWord_4075038, baseEnd_4075038] using wordTrace_append hprefix tailTrace_4075038
  have hstable : (prefixWord ++ tailWord_4075038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075038).length < 2 ^ (prefixWord ++ tailWord_4075038).sum := by decide
  have hdescent : baseEnd_4075038 < baseStart_4075038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075064 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_4075064 : Nat := 118140960795 + 4075064 * 2 ^ 59
def prefixEnd_4075064 : Nat := 4983230072969 + 3 ^ 40 * 4075064 * 2
def baseEnd_4075064 : Nat := 1394977686555699684706085

theorem tailTrace_4075064 : CollatzResearch.WordTrace tailWord_4075064 prefixEnd_4075064 1394977686555699684706085 := by
  unfold tailWord_4075064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74314897254373284183832123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99086529672497712245109497 74314897254373284183832123)
  ·
    refine ⟨111472345881559926275748185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74314897254373284183832123 111472345881559926275748185)
    ·
      refine ⟨83604259411169944706811139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111472345881559926275748185 83604259411169944706811139)
      ·
        refine ⟨125406389116754917060216709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83604259411169944706811139 125406389116754917060216709)
        ·
          refine ⟨23513697959391546948790633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125406389116754917060216709 23513697959391546948790633)
          ·
            refine ⟨17635273469543660211592975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23513697959391546948790633 17635273469543660211592975)
            ·
              refine ⟨26452910204315490317389463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17635273469543660211592975 26452910204315490317389463)
              ·
                refine ⟨39679365306473235476084195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26452910204315490317389463 39679365306473235476084195)
                ·
                  refine ⟨59519047959709853214126293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39679365306473235476084195 59519047959709853214126293)
                  ·
                    refine ⟨1394977686555699684706085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59519047959709853214126293 1394977686555699684706085)
                    ·
                      rfl

theorem cell22_4075064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_4075064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075064 prefixEnd_4075064 := by exact prefixLift 4075064
  have htrace : WordTrace (prefixWord ++ tailWord_4075064) baseStart_4075064 baseEnd_4075064 := by
    simpa [prefixWord, tailWord_4075064, baseEnd_4075064] using wordTrace_append hprefix tailTrace_4075064
  have hstable : (prefixWord ++ tailWord_4075064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075064).length < 2 ^ (prefixWord ++ tailWord_4075064).sum := by decide
  have hdescent : baseEnd_4075064 < baseStart_4075064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075141 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_4075141 : Nat := 118140960795 + 4075141 * 2 ^ 59
def prefixEnd_4075141 : Nat := 4983230072969 + 3 ^ 40 * 4075141 * 2
def baseEnd_4075141 : Nat := 1395004045229297150530849

theorem tailTrace_4075141 : CollatzResearch.WordTrace tailWord_4075141 prefixEnd_4075141 1395004045229297150530849 := by
  unfold tailWord_4075141
  simp only [CollatzResearch.WordTrace]
  refine ⟨148632602929467610518217277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99088401952978407012144851 148632602929467610518217277)
  ·
    refine ⟨55737226098550353944331479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148632602929467610518217277 55737226098550353944331479)
    ·
      refine ⟨83605839147825530916497219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55737226098550353944331479 83605839147825530916497219)
      ·
        refine ⟨125408758721738296374745829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83605839147825530916497219 125408758721738296374745829)
        ·
          refine ⟨23514142260325930570264843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125408758721738296374745829 23514142260325930570264843)
          ·
            refine ⟨35271213390488895855397265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23514142260325930570264843 35271213390488895855397265)
            ·
              refine ⟨26453410042866671891547949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35271213390488895855397265 26453410042866671891547949)
              ·
                refine ⟨9920028766075001959330481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26453410042866671891547949 9920028766075001959330481)
                ·
                  refine ⟨7440021574556251469497861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9920028766075001959330481 7440021574556251469497861)
                  ·
                    refine ⟨1395004045229297150530849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7440021574556251469497861 1395004045229297150530849)
                    ·
                      rfl

theorem cell22_4075141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_4075141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075141 prefixEnd_4075141 := by exact prefixLift 4075141
  have htrace : WordTrace (prefixWord ++ tailWord_4075141) baseStart_4075141 baseEnd_4075141 := by
    simpa [prefixWord, tailWord_4075141, baseEnd_4075141] using wordTrace_append hprefix tailTrace_4075141
  have hstable : (prefixWord ++ tailWord_4075141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075141).length < 2 ^ (prefixWord ++ tailWord_4075141).sum := by decide
  have hdescent : baseEnd_4075141 < baseStart_4075141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075218 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_4075218 : Nat := 118140960795 + 4075218 * 2 ^ 59
def prefixEnd_4075218 : Nat := 4983230072969 + 3 ^ 40 * 4075218 * 2
def baseEnd_4075218 : Nat := 465010134634298205451871

theorem tailTrace_4075218 : CollatzResearch.WordTrace tailWord_4075218 prefixEnd_4075218 465010134634298205451871 := by
  unfold tailWord_4075218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37158852837547163167192577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99090274233459101779180205 37158852837547163167192577)
  ·
    refine ⟨27869139628160372375394433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37158852837547163167192577 27869139628160372375394433)
    ·
      refine ⟨20901854721120279281545825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27869139628160372375394433 20901854721120279281545825)
      ·
        refine ⟨15676391040840209461159369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20901854721120279281545825 15676391040840209461159369)
        ·
          refine ⟨11757293280630157095869527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15676391040840209461159369 11757293280630157095869527)
          ·
            refine ⟨17635939920945235643804291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757293280630157095869527 17635939920945235643804291)
            ·
              refine ⟨26453909881417853465706437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17635939920945235643804291 26453909881417853465706437)
              ·
                refine ⟨4960108102765847524819957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26453909881417853465706437 4960108102765847524819957)
                ·
                  refine ⟨465010134634298205451871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4960108102765847524819957 465010134634298205451871)
                  ·
                    rfl

theorem cell22_4075218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_4075218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075218 prefixEnd_4075218 := by exact prefixLift 4075218
  have htrace : WordTrace (prefixWord ++ tailWord_4075218) baseStart_4075218 baseEnd_4075218 := by
    simpa [prefixWord, tailWord_4075218, baseEnd_4075218] using wordTrace_append hprefix tailTrace_4075218
  have hstable : (prefixWord ++ tailWord_4075218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075218).length < 2 ^ (prefixWord ++ tailWord_4075218).sum := by decide
  have hdescent : baseEnd_4075218 < baseStart_4075218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075231 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_4075231 : Nat := 118140960795 + 4075231 * 2 ^ 59
def prefixEnd_4075231 : Nat := 4983230072969 + 3 ^ 40 * 4075231 * 2
def baseEnd_4075231 : Nat := 1395034854068566915780573

theorem tailTrace_4075231 : CollatzResearch.WordTrace tailWord_4075231 prefixEnd_4075231 1395034854068566915780573 := by
  unfold tailWord_4075231
  simp only [CollatzResearch.WordTrace]
  refine ⟨148635885499141555888993547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99090590332761037259329031 148635885499141555888993547)
  ·
    refine ⟨222953828248712333833490321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148635885499141555888993547 222953828248712333833490321)
    ·
      refine ⟨167215371186534250375117741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222953828248712333833490321 167215371186534250375117741)
      ·
        refine ⟨62705764194950343890669153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167215371186534250375117741 62705764194950343890669153)
        ·
          refine ⟨47029323146212757918001865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62705764194950343890669153 47029323146212757918001865)
          ·
            refine ⟨35271992359659568438501399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47029323146212757918001865 35271992359659568438501399)
            ·
              refine ⟨52907988539489352657752099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35271992359659568438501399 52907988539489352657752099)
              ·
                refine ⟨79361982809234028986628149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52907988539489352657752099 79361982809234028986628149)
                ·
                  refine ⟨7440185888365690217496389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79361982809234028986628149 7440185888365690217496389)
                  ·
                    refine ⟨1395034854068566915780573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7440185888365690217496389 1395034854068566915780573)
                    ·
                      rfl

theorem cell22_4075231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_4075231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075231 prefixEnd_4075231 := by exact prefixLift 4075231
  have htrace : WordTrace (prefixWord ++ tailWord_4075231) baseStart_4075231 baseEnd_4075231 := by
    simpa [prefixWord, tailWord_4075231, baseEnd_4075231] using wordTrace_append hprefix tailTrace_4075231
  have hstable : (prefixWord ++ tailWord_4075231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075231).length < 2 ^ (prefixWord ++ tailWord_4075231).sum := by decide
  have hdescent : baseEnd_4075231 < baseStart_4075231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075233 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_4075233 : Nat := 118140960795 + 4075233 * 2 ^ 59
def prefixEnd_4075233 : Nat := 4983230072969 + 3 ^ 40 * 4075233 * 2
def baseEnd_4075233 : Nat := 1395035538709439577230567

theorem tailTrace_4075233 : CollatzResearch.WordTrace tailWord_4075233 prefixEnd_4075233 1395035538709439577230567 := by
  unfold tailWord_4075233
  simp only [CollatzResearch.WordTrace]
  refine ⟨148635958445134310230566353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99090638963422873487044235 148635958445134310230566353)
  ·
    refine ⟨111476968833850732672924765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148635958445134310230566353 111476968833850732672924765)
    ·
      refine ⟨41803863312694024752346787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111476968833850732672924765 41803863312694024752346787)
      ·
        refine ⟨62705794969041037128520181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41803863312694024752346787 62705794969041037128520181)
        ·
          refine ⟨5878668278347597230798767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62705794969041037128520181 5878668278347597230798767)
          ·
            refine ⟨8818002417521395846198151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5878668278347597230798767 8818002417521395846198151)
            ·
              refine ⟨13227003626282093769297227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8818002417521395846198151 13227003626282093769297227)
              ·
                refine ⟨19840505439423140653945841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13227003626282093769297227 19840505439423140653945841)
                ·
                  refine ⟨14880379079567355490459381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19840505439423140653945841 14880379079567355490459381)
                  ·
                    refine ⟨1395035538709439577230567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14880379079567355490459381 1395035538709439577230567)
                    ·
                      rfl

theorem cell22_4075233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_4075233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075233 prefixEnd_4075233 := by exact prefixLift 4075233
  have htrace : WordTrace (prefixWord ++ tailWord_4075233) baseStart_4075233 baseEnd_4075233 := by
    simpa [prefixWord, tailWord_4075233, baseEnd_4075233] using wordTrace_append hprefix tailTrace_4075233
  have hstable : (prefixWord ++ tailWord_4075233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075233).length < 2 ^ (prefixWord ++ tailWord_4075233).sum := by decide
  have hdescent : baseEnd_4075233 < baseStart_4075233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075261 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4075261 : Nat := 118140960795 + 4075261 * 2 ^ 59
def prefixEnd_4075261 : Nat := 4983230072969 + 3 ^ 40 * 4075261 * 2
def baseEnd_4075261 : Nat := 1395045123681656837530481

theorem tailTrace_4075261 : CollatzResearch.WordTrace tailWord_4075261 prefixEnd_4075261 1395045123681656837530481 := by
  unfold tailWord_4075261
  simp only [CollatzResearch.WordTrace]
  refine ⟨148636979689032871012585637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99091319792688580675057091 148636979689032871012585637)
  ·
    refine ⟨27869433691693663314859807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148636979689032871012585637 27869433691693663314859807)
    ·
      refine ⟨41804150537540494972289711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27869433691693663314859807 41804150537540494972289711)
      ·
        refine ⟨62706225806310742458434567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41804150537540494972289711 62706225806310742458434567)
        ·
          refine ⟨94059338709466113687651851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62706225806310742458434567 94059338709466113687651851)
          ·
            refine ⟨141089008064199170531477777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94059338709466113687651851 141089008064199170531477777)
            ·
              refine ⟨105816756048149377898608333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141089008064199170531477777 105816756048149377898608333)
              ·
                refine ⟨39681283518056016711978125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105816756048149377898608333 39681283518056016711978125)
                ·
                  refine ⟨14880481319271006266991797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39681283518056016711978125 14880481319271006266991797)
                  ·
                    refine ⟨1395045123681656837530481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14880481319271006266991797 1395045123681656837530481)
                    ·
                      rfl

theorem cell22_4075261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4075261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075261 prefixEnd_4075261 := by exact prefixLift 4075261
  have htrace : WordTrace (prefixWord ++ tailWord_4075261) baseStart_4075261 baseEnd_4075261 := by
    simpa [prefixWord, tailWord_4075261, baseEnd_4075261] using wordTrace_append hprefix tailTrace_4075261
  have hstable : (prefixWord ++ tailWord_4075261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075261).length < 2 ^ (prefixWord ++ tailWord_4075261).sum := by decide
  have hdescent : baseEnd_4075261 < baseStart_4075261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075263 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 4]
def baseStart_4075263 : Nat := 118140960795 + 4075263 * 2 ^ 59
def prefixEnd_4075263 : Nat := 4983230072969 + 3 ^ 40 * 4075263 * 2
def baseEnd_4075263 : Nat := 465015269440843166326825

theorem tailTrace_4075263 : CollatzResearch.WordTrace tailWord_4075263 prefixEnd_4075263 465015269440843166326825 := by
  unfold tailWord_4075263
  simp only [CollatzResearch.WordTrace]
  refine ⟨148637052635025625354158443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99091368423350416902772295 148637052635025625354158443)
  ·
    refine ⟨222955578952538438031237665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148637052635025625354158443 222955578952538438031237665)
    ·
      refine ⟨167216684214403828523428249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222955578952538438031237665 167216684214403828523428249)
      ·
        refine ⟨125412513160802871392571187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167216684214403828523428249 125412513160802871392571187)
        ·
          refine ⟨188118769741204307088856781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125412513160802871392571187 188118769741204307088856781)
          ·
            refine ⟨70544538652951615158321293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188118769741204307088856781 70544538652951615158321293)
            ·
              refine ⟨26454201994856855684370485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70544538652951615158321293 26454201994856855684370485)
              ·
                refine ⟨2480081437017830220409733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26454201994856855684370485 2480081437017830220409733)
                ·
                  refine ⟨465015269440843166326825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480081437017830220409733 465015269440843166326825)
                  ·
                    rfl

theorem cell22_4075263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 4].length) (baseStart_4075263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075263 prefixEnd_4075263 := by exact prefixLift 4075263
  have htrace : WordTrace (prefixWord ++ tailWord_4075263) baseStart_4075263 baseEnd_4075263 := by
    simpa [prefixWord, tailWord_4075263, baseEnd_4075263] using wordTrace_append hprefix tailTrace_4075263
  have hstable : (prefixWord ++ tailWord_4075263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075263).length < 2 ^ (prefixWord ++ tailWord_4075263).sum := by decide
  have hdescent : baseEnd_4075263 < baseStart_4075263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075265 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_4075265 : Nat := 118140960795 + 4075265 * 2 ^ 59
def prefixEnd_4075265 : Nat := 4983230072969 + 3 ^ 40 * 4075265 * 2
def baseEnd_4075265 : Nat := 1395046492963402160430469

theorem tailTrace_4075265 : CollatzResearch.WordTrace tailWord_4075265 prefixEnd_4075265 1395046492963402160430469 := by
  unfold tailWord_4075265
  simp only [CollatzResearch.WordTrace]
  refine ⟨148637125581018379695731249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99091417054012253130487499 148637125581018379695731249)
  ·
    refine ⟨111477844185763784771798437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148637125581018379695731249 111477844185763784771798437)
    ·
      refine ⟨20902095784830709644712207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111477844185763784771798437 20902095784830709644712207)
      ·
        refine ⟨31353143677246064467068311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20902095784830709644712207 31353143677246064467068311)
        ·
          refine ⟨47029715515869096700602467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31353143677246064467068311 47029715515869096700602467)
          ·
            refine ⟨70544573273803645050903701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47029715515869096700602467 70544573273803645050903701)
            ·
              refine ⟨3306776872209545861761111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70544573273803645050903701 3306776872209545861761111)
              ·
                refine ⟨4960165308314318792641667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306776872209545861761111 4960165308314318792641667)
                ·
                  refine ⟨7440247962471478188962501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960165308314318792641667 7440247962471478188962501)
                  ·
                    refine ⟨1395046492963402160430469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7440247962471478188962501 1395046492963402160430469)
                    ·
                      rfl

theorem cell22_4075265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_4075265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075265 prefixEnd_4075265 := by exact prefixLift 4075265
  have htrace : WordTrace (prefixWord ++ tailWord_4075265) baseStart_4075265 baseEnd_4075265 := by
    simpa [prefixWord, tailWord_4075265, baseEnd_4075265] using wordTrace_append hprefix tailTrace_4075265
  have hstable : (prefixWord ++ tailWord_4075265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075265).length < 2 ^ (prefixWord ++ tailWord_4075265).sum := by decide
  have hdescent : baseEnd_4075265 < baseStart_4075265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075308 : List Nat := [2, 2, 1, 1, 1, 5, 4, 6]
def baseStart_4075308 : Nat := 118140960795 + 4075308 * 2 ^ 59
def prefixEnd_4075308 : Nat := 4983230072969 + 3 ^ 40 * 4075308 * 2
def baseEnd_4075308 : Nat := 155006801415796042400593

theorem tailTrace_4075308 : CollatzResearch.WordTrace tailWord_4075308 prefixEnd_4075308 155006801415796042400593 := by
  unfold tailWord_4075308
  simp only [CollatzResearch.WordTrace]
  refine ⟨74319346959931299019773289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99092462613241732026364385 74319346959931299019773289)
  ·
    refine ⟨55739510219948474264829967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74319346959931299019773289 55739510219948474264829967)
    ·
      refine ⟨83609265329922711397244951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55739510219948474264829967 83609265329922711397244951)
      ·
        refine ⟨125413897994884067095867427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83609265329922711397244951 125413897994884067095867427)
        ·
          refine ⟨188120846992326100643801141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125413897994884067095867427 188120846992326100643801141)
          ·
            refine ⟨17636329405530571935356357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188120846992326100643801141 17636329405530571935356357)
            ·
              refine ⟨3306811763536982237879317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17636329405530571935356357 3306811763536982237879317)
              ·
                refine ⟨155006801415796042400593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3306811763536982237879317 155006801415796042400593)
                ·
                  rfl

theorem cell22_4075308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_4075308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075308 prefixEnd_4075308 := by exact prefixLift 4075308
  have htrace : WordTrace (prefixWord ++ tailWord_4075308) baseStart_4075308 baseEnd_4075308 := by
    simpa [prefixWord, tailWord_4075308, baseEnd_4075308] using wordTrace_append hprefix tailTrace_4075308
  have hstable : (prefixWord ++ tailWord_4075308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075308).length < 2 ^ (prefixWord ++ tailWord_4075308).sum := by decide
  have hdescent : baseEnd_4075308 < baseStart_4075308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075353 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 5]
def baseStart_4075353 : Nat := 118140960795 + 4075353 * 2 ^ 59
def prefixEnd_4075353 : Nat := 4983230072969 + 3 ^ 40 * 4075353 * 2
def baseEnd_4075353 : Nat := 465025539053933088076733

theorem tailTrace_4075353 : CollatzResearch.WordTrace tailWord_4075353 prefixEnd_4075353 465025539053933088076733 := by
  unfold tailWord_4075353
  simp only [CollatzResearch.WordTrace]
  refine ⟨148640335204699570724934713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99093556803133047149956475 148640335204699570724934713)
  ·
    refine ⟨111480251403524678043701035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148640335204699570724934713 111480251403524678043701035)
    ·
      refine ⟨167220377105287017065551553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111480251403524678043701035 167220377105287017065551553)
      ·
        refine ⟨125415282828965262799163665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167220377105287017065551553 125415282828965262799163665)
        ·
          refine ⟨94061462121723947099372749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125415282828965262799163665 94061462121723947099372749)
          ·
            refine ⟨35273048295646480162264781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94061462121723947099372749 35273048295646480162264781)
            ·
              refine ⟨13227393110867430060849293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35273048295646480162264781 13227393110867430060849293)
              ·
                refine ⟨4960272416575286272818485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13227393110867430060849293 4960272416575286272818485)
                ·
                  refine ⟨465025539053933088076733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4960272416575286272818485 465025539053933088076733)
                  ·
                    rfl

theorem cell22_4075353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_4075353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075353 prefixEnd_4075353 := by exact prefixLift 4075353
  have htrace : WordTrace (prefixWord ++ tailWord_4075353) baseStart_4075353 baseEnd_4075353 := by
    simpa [prefixWord, tailWord_4075353, baseEnd_4075353] using wordTrace_append hprefix tailTrace_4075353
  have hstable : (prefixWord ++ tailWord_4075353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075353).length < 2 ^ (prefixWord ++ tailWord_4075353).sum := by decide
  have hdescent : baseEnd_4075353 < baseStart_4075353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075438 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_4075438 : Nat := 118140960795 + 4075438 * 2 ^ 59
def prefixEnd_4075438 : Nat := 4983230072969 + 3 ^ 40 * 4075438 * 2
def baseEnd_4075438 : Nat := 465035238132962458618313

theorem tailTrace_4075438 : CollatzResearch.WordTrace tailWord_4075438 prefixEnd_4075438 465035238132962458618313 := by
  unfold tailWord_4075438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18580429426173953780222371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99095623606261086827852645 18580429426173953780222371)
  ·
    refine ⟨27870644139260930670333557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18580429426173953780222371 27870644139260930670333557)
    ·
      refine ⟨2612872888055712250343771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27870644139260930670333557 2612872888055712250343771)
      ·
        refine ⟨3919309332083568375515657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612872888055712250343771 3919309332083568375515657)
        ·
          refine ⟨2939481999062676281636743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3919309332083568375515657 2939481999062676281636743)
          ·
            refine ⟨4409222998594014422455115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939481999062676281636743 4409222998594014422455115)
            ·
              refine ⟨6613834497891021633682673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409222998594014422455115 6613834497891021633682673)
              ·
                refine ⟨4960375873418266225262005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613834497891021633682673 4960375873418266225262005)
                ·
                  refine ⟨465035238132962458618313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4960375873418266225262005 465035238132962458618313)
                  ·
                    rfl

theorem cell22_4075438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_4075438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075438 prefixEnd_4075438 := by exact prefixLift 4075438
  have htrace : WordTrace (prefixWord ++ tailWord_4075438) baseStart_4075438 baseEnd_4075438 := by
    simpa [prefixWord, tailWord_4075438, baseEnd_4075438] using wordTrace_append hprefix tailTrace_4075438
  have hstable : (prefixWord ++ tailWord_4075438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075438).length < 2 ^ (prefixWord ++ tailWord_4075438).sum := by decide
  have hdescent : baseEnd_4075438 < baseStart_4075438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075464 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_4075464 : Nat := 118140960795 + 4075464 * 2 ^ 59
def prefixEnd_4075464 : Nat := 4983230072969 + 3 ^ 40 * 4075464 * 2
def baseEnd_4075464 : Nat := 1395114614730231974704859

theorem tailTrace_4075464 : CollatzResearch.WordTrace tailWord_4075464 prefixEnd_4075464 1395114614730231974704859 := by
  unfold tailWord_4075464
  simp only [CollatzResearch.WordTrace]
  refine ⟨74322191853648718341112723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99096255804864957788150297 74322191853648718341112723)
  ·
    refine ⟨111483287780473077511669085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74322191853648718341112723 111483287780473077511669085)
    ·
      refine ⟨41806232917677404066875907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111483287780473077511669085 41806232917677404066875907)
      ·
        refine ⟨62709349376516106100313861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41806232917677404066875907 62709349376516106100313861)
        ·
          refine ⟨11758003008096769893808849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62709349376516106100313861 11758003008096769893808849)
          ·
            refine ⟨8818502256072577420356637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11758003008096769893808849 8818502256072577420356637)
            ·
              refine ⟨3306938346027216532633739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8818502256072577420356637 3306938346027216532633739)
              ·
                refine ⟨4960407519040824798950609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306938346027216532633739 4960407519040824798950609)
                ·
                  refine ⟨3720305639280618599212957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960407519040824798950609 3720305639280618599212957)
                  ·
                    refine ⟨1395114614730231974704859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720305639280618599212957 1395114614730231974704859)
                    ·
                      rfl

theorem cell22_4075464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_4075464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075464 prefixEnd_4075464 := by exact prefixLift 4075464
  have htrace : WordTrace (prefixWord ++ tailWord_4075464) baseStart_4075464 baseEnd_4075464 := by
    simpa [prefixWord, tailWord_4075464, baseEnd_4075464] using wordTrace_append hprefix tailTrace_4075464
  have hstable : (prefixWord ++ tailWord_4075464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075464).length < 2 ^ (prefixWord ++ tailWord_4075464).sum := by decide
  have hdescent : baseEnd_4075464 < baseStart_4075464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075477 : List Nat := [1, 3, 2, 3, 2, 3, 2, 6]
def baseStart_4075477 : Nat := 118140960795 + 4075477 * 2 ^ 59
def prefixEnd_4075477 : Nat := 4983230072969 + 3 ^ 40 * 4075477 * 2
def baseEnd_4075477 : Nat := 155013229432878252681091

theorem tailTrace_4075477 : CollatzResearch.WordTrace tailWord_4075477 prefixEnd_4075477 155013229432878252681091 := by
  unfold tailWord_4075477
  simp only [CollatzResearch.WordTrace]
  refine ⟨148644857856250339902448685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99096571904166893268299123 148644857856250339902448685)
  ·
    refine ⟨55741821696093877463418257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148644857856250339902448685 55741821696093877463418257)
    ·
      refine ⟨41806366272070408097563693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55741821696093877463418257 41806366272070408097563693)
      ·
        refine ⟨15677387352026403036586385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41806366272070408097563693 15677387352026403036586385)
        ·
          refine ⟨11758040514019802277439789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15677387352026403036586385 11758040514019802277439789)
          ·
            refine ⟨4409265192757425854039921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11758040514019802277439789 4409265192757425854039921)
            ·
              refine ⟨3306948894568069390529941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409265192757425854039921 3306948894568069390529941)
              ·
                refine ⟨155013229432878252681091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3306948894568069390529941 155013229432878252681091)
                ·
                  rfl

theorem cell22_4075477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 6].length) (baseStart_4075477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075477 prefixEnd_4075477 := by exact prefixLift 4075477
  have htrace : WordTrace (prefixWord ++ tailWord_4075477) baseStart_4075477 baseEnd_4075477 := by
    simpa [prefixWord, tailWord_4075477, baseEnd_4075477] using wordTrace_append hprefix tailTrace_4075477
  have hstable : (prefixWord ++ tailWord_4075477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075477).length < 2 ^ (prefixWord ++ tailWord_4075477).sum := by decide
  have hdescent : baseEnd_4075477 < baseStart_4075477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075560 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4075560 : Nat := 118140960795 + 4075560 * 2 ^ 59
def prefixEnd_4075560 : Nat := 4983230072969 + 3 ^ 40 * 4075560 * 2
def baseEnd_4075560 : Nat := 1395147477492119724304565

theorem tailTrace_4075560 : CollatzResearch.WordTrace tailWord_4075560 prefixEnd_4075560 1395147477492119724304565 := by
  unfold tailWord_4075560
  simp only [CollatzResearch.WordTrace]
  refine ⟨74323942557474822538860067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99098590076633096718480089 74323942557474822538860067)
  ·
    refine ⟨111485913836212233808290101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74323942557474822538860067 111485913836212233808290101)
    ·
      refine ⟨10451804422144896919527197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111485913836212233808290101 10451804422144896919527197)
      ·
        refine ⟨3919426658304336344822699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10451804422144896919527197 3919426658304336344822699)
        ·
          refine ⟨5879139987456504517234049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919426658304336344822699 5879139987456504517234049)
          ·
            refine ⟨4409354990592378387925537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879139987456504517234049 4409354990592378387925537)
            ·
              refine ⟨3307016242944283790944153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409354990592378387925537 3307016242944283790944153)
              ·
                refine ⟨2480262182208212843208115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307016242944283790944153 2480262182208212843208115)
                ·
                  refine ⟨3720393273312319264812173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480262182208212843208115 3720393273312319264812173)
                  ·
                    refine ⟨1395147477492119724304565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720393273312319264812173 1395147477492119724304565)
                    ·
                      rfl

theorem cell22_4075560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4075560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075560 prefixEnd_4075560 := by exact prefixLift 4075560
  have htrace : WordTrace (prefixWord ++ tailWord_4075560) baseStart_4075560 baseEnd_4075560 := by
    simpa [prefixWord, tailWord_4075560, baseEnd_4075560] using wordTrace_append hprefix tailTrace_4075560
  have hstable : (prefixWord ++ tailWord_4075560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075560).length < 2 ^ (prefixWord ++ tailWord_4075560).sum := by decide
  have hdescent : baseEnd_4075560 < baseStart_4075560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075580 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4075580 : Nat := 118140960795 + 4075580 * 2 ^ 59
def prefixEnd_4075580 : Nat := 4983230072969 + 3 ^ 40 * 4075580 * 2
def baseEnd_4075580 : Nat := 1395154323900846338804503

theorem tailTrace_4075580 : CollatzResearch.WordTrace tailWord_4075580 prefixEnd_4075580 1395154323900846338804503 := by
  unfold tailWord_4075580
  simp only [CollatzResearch.WordTrace]
  refine ⟨74324307287438594246724097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99099076383251458995632129 74324307287438594246724097)
  ·
    refine ⟨55743230465578945685043073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74324307287438594246724097 55743230465578945685043073)
    ·
      refine ⟨41807422849184209263782305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55743230465578945685043073 41807422849184209263782305)
      ·
        refine ⟨31355567136888156947836729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41807422849184209263782305 31355567136888156947836729)
        ·
          refine ⟨23516675352666117710877547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31355567136888156947836729 23516675352666117710877547)
          ·
            refine ⟨35275013028999176566316321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23516675352666117710877547 35275013028999176566316321)
            ·
              refine ⟨26456259771749382424737241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35275013028999176566316321 26456259771749382424737241)
              ·
                refine ⟨19842194828812036818552931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26456259771749382424737241 19842194828812036818552931)
                ·
                  refine ⟨29763292243218055227829397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19842194828812036818552931 29763292243218055227829397)
                  ·
                    refine ⟨1395154323900846338804503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29763292243218055227829397 1395154323900846338804503)
                    ·
                      rfl

theorem cell22_4075580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4075580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075580 prefixEnd_4075580 := by exact prefixLift 4075580
  have htrace : WordTrace (prefixWord ++ tailWord_4075580) baseStart_4075580 baseEnd_4075580 := by
    simpa [prefixWord, tailWord_4075580, baseEnd_4075580] using wordTrace_append hprefix tailTrace_4075580
  have hstable : (prefixWord ++ tailWord_4075580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075580).length < 2 ^ (prefixWord ++ tailWord_4075580).sum := by decide
  have hdescent : baseEnd_4075580 < baseStart_4075580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075597 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4075597 : Nat := 118140960795 + 4075597 * 2 ^ 59
def prefixEnd_4075597 : Nat := 4983230072969 + 3 ^ 40 * 4075597 * 2
def baseEnd_4075597 : Nat := 1395160143348263961129451

theorem tailTrace_4075597 : CollatzResearch.WordTrace tailWord_4075597 prefixEnd_4075597 1395160143348263961129451 := by
  unfold tailWord_4075597
  simp only [CollatzResearch.WordTrace]
  refine ⟨148649234615815600396817045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99099489743877066931211363 148649234615815600396817045)
  ·
    refine ⟨6967932872616356268600799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148649234615815600396817045 6967932872616356268600799)
    ·
      refine ⟨10451899308924534402901199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967932872616356268600799 10451899308924534402901199)
      ·
        refine ⟨15677848963386801604351799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451899308924534402901199 15677848963386801604351799)
        ·
          refine ⟨23516773445080202406527699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677848963386801604351799 23516773445080202406527699)
          ·
            refine ⟨35275160167620303609791549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23516773445080202406527699 35275160167620303609791549)
            ·
              refine ⟨13228185062857613853671831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35275160167620303609791549 13228185062857613853671831)
              ·
                refine ⟨19842277594286420780507747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228185062857613853671831 19842277594286420780507747)
                ·
                  refine ⟨29763416391429631170761621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19842277594286420780507747 29763416391429631170761621)
                  ·
                    refine ⟨1395160143348263961129451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29763416391429631170761621 1395160143348263961129451)
                    ·
                      rfl

theorem cell22_4075597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4075597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075597 prefixEnd_4075597 := by exact prefixLift 4075597
  have htrace : WordTrace (prefixWord ++ tailWord_4075597) baseStart_4075597 baseEnd_4075597 := by
    simpa [prefixWord, tailWord_4075597, baseEnd_4075597] using wordTrace_append hprefix tailTrace_4075597
  have hstable : (prefixWord ++ tailWord_4075597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075597).length < 2 ^ (prefixWord ++ tailWord_4075597).sum := by decide
  have hdescent : baseEnd_4075597 < baseStart_4075597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075655 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4075655 : Nat := 118140960795 + 4075655 * 2 ^ 59
def prefixEnd_4075655 : Nat := 4983230072969 + 3 ^ 40 * 4075655 * 2
def baseEnd_4075655 : Nat := 1395179997933571143179273

theorem tailTrace_4075655 : CollatzResearch.WordTrace tailWord_4075655 prefixEnd_4075655 1395179997933571143179273 := by
  unfold tailWord_4075655
  simp only [CollatzResearch.WordTrace]
  refine ⟨148651350049605476302428419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99100900033070317534952279 148651350049605476302428419)
  ·
    refine ⟨222977025074408214453642629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148651350049605476302428419 222977025074408214453642629)
    ·
      refine ⟨41808192201451540210057993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222977025074408214453642629 41808192201451540210057993)
      ·
        refine ⟨31356144151088655157543495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41808192201451540210057993 31356144151088655157543495)
        ·
          refine ⟨47034216226632982736315243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31356144151088655157543495 47034216226632982736315243)
          ·
            refine ⟨70551324339949474104472865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47034216226632982736315243 70551324339949474104472865)
            ·
              refine ⟨52913493254962105578354649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70551324339949474104472865 52913493254962105578354649)
              ·
                refine ⟨39685119941221579183765987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52913493254962105578354649 39685119941221579183765987)
                ·
                  refine ⟨59527679911832368775648981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39685119941221579183765987 59527679911832368775648981)
                  ·
                    refine ⟨1395179997933571143179273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59527679911832368775648981 1395179997933571143179273)
                    ·
                      rfl

theorem cell22_4075655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4075655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075655 prefixEnd_4075655 := by exact prefixLift 4075655
  have htrace : WordTrace (prefixWord ++ tailWord_4075655) baseStart_4075655 baseEnd_4075655 := by
    simpa [prefixWord, tailWord_4075655, baseEnd_4075655] using wordTrace_append hprefix tailTrace_4075655
  have hstable : (prefixWord ++ tailWord_4075655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075655).length < 2 ^ (prefixWord ++ tailWord_4075655).sum := by decide
  have hdescent : baseEnd_4075655 < baseStart_4075655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075678 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4075678 : Nat := 118140960795 + 4075678 * 2 ^ 59
def prefixEnd_4075678 : Nat := 4983230072969 + 3 ^ 40 * 4075678 * 2
def baseEnd_4075678 : Nat := 1395187871303606749854203

theorem tailTrace_4075678 : CollatzResearch.WordTrace tailWord_4075678 prefixEnd_4075678 1395187871303606749854203 := by
  unfold tailWord_4075678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581523616065268903814461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99101459285681434153677125 18581523616065268903814461)
  ·
    refine ⟨6968071356024475838930423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18581523616065268903814461 6968071356024475838930423)
    ·
      refine ⟨10452107034036713758395635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6968071356024475838930423 10452107034036713758395635)
      ·
        refine ⟨15678160551055070637593453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10452107034036713758395635 15678160551055070637593453)
        ·
          refine ⟨5879310206645651489097545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15678160551055070637593453 5879310206645651489097545)
          ·
            refine ⟨4409482654984238616823159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879310206645651489097545 4409482654984238616823159)
            ·
              refine ⟨6614223982476357925234739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409482654984238616823159 6614223982476357925234739)
              ·
                refine ⟨9921335973714536887852109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6614223982476357925234739 9921335973714536887852109)
                ·
                  refine ⟨3720500990142951332944541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9921335973714536887852109 3720500990142951332944541)
                  ·
                    refine ⟨1395187871303606749854203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720500990142951332944541 1395187871303606749854203)
                    ·
                      rfl

theorem cell22_4075678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4075678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075678 prefixEnd_4075678 := by exact prefixLift 4075678
  have htrace : WordTrace (prefixWord ++ tailWord_4075678) baseStart_4075678 baseEnd_4075678 := by
    simpa [prefixWord, tailWord_4075678, baseEnd_4075678] using wordTrace_append hprefix tailTrace_4075678
  have hstable : (prefixWord ++ tailWord_4075678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075678).length < 2 ^ (prefixWord ++ tailWord_4075678).sum := by decide
  have hdescent : baseEnd_4075678 < baseStart_4075678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075715 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_4075715 : Nat := 118140960795 + 4075715 * 2 ^ 59
def prefixEnd_4075715 : Nat := 4983230072969 + 3 ^ 40 * 4075715 * 2
def baseEnd_4075715 : Nat := 1395200537159750986679089

theorem tailTrace_4075715 : CollatzResearch.WordTrace tailWord_4075715 prefixEnd_4075715 1395200537159750986679089 := by
  unfold tailWord_4075715
  simp only [CollatzResearch.WordTrace]
  refine ⟨148653538429388106549612599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99102358952925404366408399 148653538429388106549612599)
  ·
    refine ⟨222980307644082159824418899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148653538429388106549612599 222980307644082159824418899)
    ·
      refine ⟨334470461466123239736628349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222980307644082159824418899 334470461466123239736628349)
      ·
        refine ⟨125426423049796214901235631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334470461466123239736628349 125426423049796214901235631)
        ·
          refine ⟨188139634574694322351853447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125426423049796214901235631 188139634574694322351853447)
          ·
            refine ⟨282209451862041483527780171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188139634574694322351853447 282209451862041483527780171)
            ·
              refine ⟨423314177793062225291670257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282209451862041483527780171 423314177793062225291670257)
              ·
                refine ⟨317485633344796668968752693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423314177793062225291670257 317485633344796668968752693)
                ·
                  refine ⟨29764278126074687715820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317485633344796668968752693 29764278126074687715820565)
                  ·
                    refine ⟨1395200537159750986679089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29764278126074687715820565 1395200537159750986679089)
                    ·
                      rfl

theorem cell22_4075715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_4075715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075715 prefixEnd_4075715 := by exact prefixLift 4075715
  have htrace : WordTrace (prefixWord ++ tailWord_4075715) baseStart_4075715 baseEnd_4075715 := by
    simpa [prefixWord, tailWord_4075715, baseEnd_4075715] using wordTrace_append hprefix tailTrace_4075715
  have hstable : (prefixWord ++ tailWord_4075715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075715).length < 2 ^ (prefixWord ++ tailWord_4075715).sum := by decide
  have hdescent : baseEnd_4075715 < baseStart_4075715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075717 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_4075717 : Nat := 118140960795 + 4075717 * 2 ^ 59
def prefixEnd_4075717 : Nat := 4983230072969 + 3 ^ 40 * 4075717 * 2
def baseEnd_4075717 : Nat := 1395201221800623648129083

theorem tailTrace_4075717 : CollatzResearch.WordTrace tailWord_4075717 prefixEnd_4075717 1395201221800623648129083 := by
  unfold tailWord_4075717
  simp only [CollatzResearch.WordTrace]
  refine ⟨148653611375380860891185405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99102407583587240594123603 148653611375380860891185405)
  ·
    refine ⟨55745104265767822834194527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148653611375380860891185405 55745104265767822834194527)
    ·
      refine ⟨83617656398651734251291791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55745104265767822834194527 83617656398651734251291791)
      ·
        refine ⟨125426484597977601376937687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83617656398651734251291791 125426484597977601376937687)
        ·
          refine ⟨188139726896966402065406531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125426484597977601376937687 188139726896966402065406531)
          ·
            refine ⟨282209590345449603098109797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188139726896966402065406531 282209590345449603098109797)
            ·
              refine ⟨52914298189771800580895587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282209590345449603098109797 52914298189771800580895587)
              ·
                refine ⟨79371447284657700871343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52914298189771800580895587 79371447284657700871343381)
                ·
                  refine ⟨3720536591468329728344221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79371447284657700871343381 3720536591468329728344221)
                  ·
                    refine ⟨1395201221800623648129083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720536591468329728344221 1395201221800623648129083)
                    ·
                      rfl

theorem cell22_4075717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_4075717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075717 prefixEnd_4075717 := by exact prefixLift 4075717
  have htrace : WordTrace (prefixWord ++ tailWord_4075717) baseStart_4075717 baseEnd_4075717 := by
    simpa [prefixWord, tailWord_4075717, baseEnd_4075717] using wordTrace_append hprefix tailTrace_4075717
  have hstable : (prefixWord ++ tailWord_4075717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075717).length < 2 ^ (prefixWord ++ tailWord_4075717).sum := by decide
  have hdescent : baseEnd_4075717 < baseStart_4075717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075736 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_4075736 : Nat := 118140960795 + 4075736 * 2 ^ 59
def prefixEnd_4075736 : Nat := 4983230072969 + 3 ^ 40 * 4075736 * 2
def baseEnd_4075736 : Nat := 465069241962971310634675

theorem tailTrace_4075736 : CollatzResearch.WordTrace tailWord_4075736 prefixEnd_4075736 465069241962971310634675 := by
  unfold tailWord_4075736
  simp only [CollatzResearch.WordTrace]
  refine ⟨74327152181156013568063531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99102869574874684757418041 74327152181156013568063531)
  ·
    refine ⟨111490728271734020352095297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74327152181156013568063531 111490728271734020352095297)
    ·
      refine ⟨83618046203800515264071473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111490728271734020352095297 83618046203800515264071473)
      ·
        refine ⟨62713534652850386448053605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83618046203800515264071473 62713534652850386448053605)
        ·
          refine ⟨11758787747409447459010051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62713534652850386448053605 11758787747409447459010051)
          ·
            refine ⟨17638181621114171188515077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758787747409447459010051 17638181621114171188515077)
            ·
              refine ⟨3307159053958907097846577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17638181621114171188515077 3307159053958907097846577)
              ·
                refine ⟨2480369290469180323384933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307159053958907097846577 2480369290469180323384933)
                ·
                  refine ⟨465069241962971310634675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480369290469180323384933 465069241962971310634675)
                  ·
                    rfl

theorem cell22_4075736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_4075736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075736 prefixEnd_4075736 := by exact prefixLift 4075736
  have htrace : WordTrace (prefixWord ++ tailWord_4075736) baseStart_4075736 baseEnd_4075736 := by
    simpa [prefixWord, tailWord_4075736, baseEnd_4075736] using wordTrace_append hprefix tailTrace_4075736
  have hstable : (prefixWord ++ tailWord_4075736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075736).length < 2 ^ (prefixWord ++ tailWord_4075736).sum := by decide
  have hdescent : baseEnd_4075736 < baseStart_4075736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075751 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 2, 3]
def baseStart_4075751 : Nat := 118140960795 + 4075751 * 2 ^ 59
def prefixEnd_4075751 : Nat := 4983230072969 + 3 ^ 40 * 4075751 * 2
def baseEnd_4075751 : Nat := 1395212860695458892778979

theorem tailTrace_4075751 : CollatzResearch.WordTrace tailWord_4075751 prefixEnd_4075751 1395212860695458892778979 := by
  unfold tailWord_4075751
  simp only [CollatzResearch.WordTrace]
  refine ⟨148654851457257684697923107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99103234304838456465282071 148654851457257684697923107)
  ·
    refine ⟨222982277185886527046884661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148654851457257684697923107 222982277185886527046884661)
    ·
      refine ⟨20904588486176861910645437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222982277185886527046884661 20904588486176861910645437)
      ·
        refine ⟨7839220682316323216492039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20904588486176861910645437 7839220682316323216492039)
        ·
          refine ⟨11758831023474484824738059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839220682316323216492039 11758831023474484824738059)
          ·
            refine ⟨17638246535211727237107089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758831023474484824738059 17638246535211727237107089)
            ·
              refine ⟨13228684901408795427830317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17638246535211727237107089 13228684901408795427830317)
              ·
                refine ⟨4960756838028298285436369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13228684901408795427830317 4960756838028298285436369)
                ·
                  refine ⟨3720567628521223714077277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960756838028298285436369 3720567628521223714077277)
                  ·
                    refine ⟨1395212860695458892778979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720567628521223714077277 1395212860695458892778979)
                    ·
                      rfl

theorem cell22_4075751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_4075751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075751 prefixEnd_4075751 := by exact prefixLift 4075751
  have htrace : WordTrace (prefixWord ++ tailWord_4075751) baseStart_4075751 baseEnd_4075751 := by
    simpa [prefixWord, tailWord_4075751, baseEnd_4075751] using wordTrace_append hprefix tailTrace_4075751
  have hstable : (prefixWord ++ tailWord_4075751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075751).length < 2 ^ (prefixWord ++ tailWord_4075751).sum := by decide
  have hdescent : baseEnd_4075751 < baseStart_4075751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075815 : List Nat := [1, 1, 8, 1, 1, 2, 2, 6]
def baseStart_4075815 : Nat := 118140960795 + 4075815 * 2 ^ 59
def prefixEnd_4075815 : Nat := 4983230072969 + 3 ^ 40 * 4075815 * 2
def baseEnd_4075815 : Nat := 155026085467042673242087

theorem tailTrace_4075815 : CollatzResearch.WordTrace tailWord_4075815 prefixEnd_4075815 155026085467042673242087 := by
  unfold tailWord_4075815
  simp only [CollatzResearch.WordTrace]
  refine ⟨148657185729025823628252899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99104790486017215752168599 148657185729025823628252899)
  ·
    refine ⟨222985778593538735442379349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148657185729025823628252899 222985778593538735442379349)
    ·
      refine ⟨2613114592893032055965383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 222985778593538735442379349 2613114592893032055965383)
      ·
        refine ⟨3919671889339548083948075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613114592893032055965383 3919671889339548083948075)
        ·
          refine ⟨5879507834009322125922113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919671889339548083948075 5879507834009322125922113)
          ·
            refine ⟨4409630875506991594441585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879507834009322125922113 4409630875506991594441585)
            ·
              refine ⟨3307223156630243695831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409630875506991594441585 3307223156630243695831189)
              ·
                refine ⟨155026085467042673242087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3307223156630243695831189 155026085467042673242087)
                ·
                  rfl

theorem cell22_4075815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 6].length) (baseStart_4075815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075815 prefixEnd_4075815 := by exact prefixLift 4075815
  have htrace : WordTrace (prefixWord ++ tailWord_4075815) baseStart_4075815 baseEnd_4075815 := by
    simpa [prefixWord, tailWord_4075815, baseEnd_4075815] using wordTrace_append hprefix tailTrace_4075815
  have hstable : (prefixWord ++ tailWord_4075815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075815).length < 2 ^ (prefixWord ++ tailWord_4075815).sum := by decide
  have hdescent : baseEnd_4075815 < baseStart_4075815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075839 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 1, 4]
def baseStart_4075839 : Nat := 118140960795 + 4075839 * 2 ^ 59
def prefixEnd_4075839 : Nat := 4983230072969 + 3 ^ 40 * 4075839 * 2
def baseEnd_4075839 : Nat := 1395242984893855996578709

theorem tailTrace_4075839 : CollatzResearch.WordTrace tailWord_4075839 prefixEnd_4075839 1395242984893855996578709 := by
  unfold tailWord_4075839
  simp only [CollatzResearch.WordTrace]
  refine ⟨148658061080938875727126571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99105374053959250484751047 148658061080938875727126571)
  ·
    refine ⟨222987091621408313590689857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148658061080938875727126571 222987091621408313590689857)
    ·
      refine ⟨167240318716056235193017393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222987091621408313590689857 167240318716056235193017393)
      ·
        refine ⟨125430239037042176394763045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167240318716056235193017393 125430239037042176394763045)
        ·
          refine ⟨23518169819445408074018071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125430239037042176394763045 23518169819445408074018071)
          ·
            refine ⟨35277254729168112111027107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518169819445408074018071 35277254729168112111027107)
            ·
              refine ⟨52915882093752168166540661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35277254729168112111027107 52915882093752168166540661)
              ·
                refine ⟨4960863946289265765613187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52915882093752168166540661 4960863946289265765613187)
                ·
                  refine ⟨7441295919433898648419781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960863946289265765613187 7441295919433898648419781)
                  ·
                    refine ⟨1395242984893855996578709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7441295919433898648419781 1395242984893855996578709)
                    ·
                      rfl

theorem cell22_4075839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_4075839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075839 prefixEnd_4075839 := by exact prefixLift 4075839
  have htrace : WordTrace (prefixWord ++ tailWord_4075839) baseStart_4075839 baseEnd_4075839 := by
    simpa [prefixWord, tailWord_4075839, baseEnd_4075839] using wordTrace_append hprefix tailTrace_4075839
  have hstable : (prefixWord ++ tailWord_4075839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075839).length < 2 ^ (prefixWord ++ tailWord_4075839).sum := by decide
  have hdescent : baseEnd_4075839 < baseStart_4075839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075905 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 4]
def baseStart_4075905 : Nat := 118140960795 + 4075905 * 2 ^ 59
def prefixEnd_4075905 : Nat := 4983230072969 + 3 ^ 40 * 4075905 * 2
def baseEnd_4075905 : Nat := 465088526014217941476169

theorem tailTrace_4075905 : CollatzResearch.WordTrace tailWord_4075905 prefixEnd_4075905 465088526014217941476169 := by
  unfold tailWord_4075905
  simp only [CollatzResearch.WordTrace]
  refine ⟨148660468298699768999029169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99106978865799845999352779 148660468298699768999029169)
  ·
    refine ⟨111495351224024826749271877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148660468298699768999029169 111495351224024826749271877)
    ·
      refine ⟨20905378354504655015488477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111495351224024826749271877 20905378354504655015488477)
      ·
        refine ⟨7839516882939245630808179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20905378354504655015488477 7839516882939245630808179)
        ·
          refine ⟨11759275324408868446212269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839516882939245630808179 11759275324408868446212269)
          ·
            refine ⟨4409728246653325667329601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11759275324408868446212269 4409728246653325667329601)
            ·
              refine ⟨3307296184989994250497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409728246653325667329601 3307296184989994250497201)
              ·
                refine ⟨2480472138742495687872901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307296184989994250497201 2480472138742495687872901)
                ·
                  refine ⟨465088526014217941476169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480472138742495687872901 465088526014217941476169)
                  ·
                    rfl

theorem cell22_4075905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_4075905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075905 prefixEnd_4075905 := by exact prefixLift 4075905
  have htrace : WordTrace (prefixWord ++ tailWord_4075905) baseStart_4075905 baseEnd_4075905 := by
    simpa [prefixWord, tailWord_4075905, baseEnd_4075905] using wordTrace_append hprefix tailTrace_4075905
  have hstable : (prefixWord ++ tailWord_4075905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075905).length < 2 ^ (prefixWord ++ tailWord_4075905).sum := by decide
  have hdescent : baseEnd_4075905 < baseStart_4075905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075959 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4075959 : Nat := 118140960795 + 4075959 * 2 ^ 59
def prefixEnd_4075959 : Nat := 4983230072969 + 3 ^ 40 * 4075959 * 2
def baseEnd_4075959 : Nat := 1395284063346215683578341

theorem tailTrace_4075959 : CollatzResearch.WordTrace tailWord_4075959 prefixEnd_4075959 1395284063346215683578341 := by
  unfold tailWord_4075959
  simp only [CollatzResearch.WordTrace]
  refine ⟨148662437840504136221494931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99108291893669424147663287 148662437840504136221494931)
  ·
    refine ⟨222993656760756204332242397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148662437840504136221494931 222993656760756204332242397)
    ·
      refine ⟨83622621285283576624590899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222993656760756204332242397 83622621285283576624590899)
      ·
        refine ⟨125433931927925364936886349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83622621285283576624590899 125433931927925364936886349)
        ·
          refine ⟨47037724472972011851332381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125433931927925364936886349 47037724472972011851332381)
          ·
            refine ⟨17639146677364504444249643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47037724472972011851332381 17639146677364504444249643)
            ·
              refine ⟨26458720016046756666374465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17639146677364504444249643 26458720016046756666374465)
              ·
                refine ⟨19844040012035067499780849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26458720016046756666374465 19844040012035067499780849)
                ·
                  refine ⟨14883030009026300624835637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19844040012035067499780849 14883030009026300624835637)
                  ·
                    refine ⟨1395284063346215683578341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14883030009026300624835637 1395284063346215683578341)
                    ·
                      rfl

theorem cell22_4075959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4075959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075959 prefixEnd_4075959 := by exact prefixLift 4075959
  have htrace : WordTrace (prefixWord ++ tailWord_4075959) baseStart_4075959 baseEnd_4075959 := by
    simpa [prefixWord, tailWord_4075959, baseEnd_4075959] using wordTrace_append hprefix tailTrace_4075959
  have hstable : (prefixWord ++ tailWord_4075959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075959).length < 2 ^ (prefixWord ++ tailWord_4075959).sum := by decide
  have hdescent : baseEnd_4075959 < baseStart_4075959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075961 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 5]
def baseStart_4075961 : Nat := 118140960795 + 4075961 * 2 ^ 59
def prefixEnd_4075961 : Nat := 4983230072969 + 3 ^ 40 * 4075961 * 2
def baseEnd_4075961 : Nat := 465094915995696115009445

theorem tailTrace_4075961 : CollatzResearch.WordTrace tailWord_4075961 prefixEnd_4075961 465094915995696115009445 := by
  unfold tailWord_4075961
  simp only [CollatzResearch.WordTrace]
  refine ⟨148662510786496890563067737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99108340524331260375378491 148662510786496890563067737)
  ·
    refine ⟨111496883089872667922300803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148662510786496890563067737 111496883089872667922300803)
    ·
      refine ⟨167245324634809001883451205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111496883089872667922300803 167245324634809001883451205)
      ·
        refine ⟨31358498369026687853147101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167245324634809001883451205 31358498369026687853147101)
        ·
          refine ⟨11759436888385007944930163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31358498369026687853147101 11759436888385007944930163)
          ·
            refine ⟨17639155332577511917395245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11759436888385007944930163 17639155332577511917395245)
            ·
              refine ⟨6614683249716566969023217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17639155332577511917395245 6614683249716566969023217)
              ·
                refine ⟨4961012437287425226767413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6614683249716566969023217 4961012437287425226767413)
                ·
                  refine ⟨465094915995696115009445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961012437287425226767413 465094915995696115009445)
                  ·
                    rfl

theorem cell22_4075961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_4075961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4075961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4075961 prefixEnd_4075961 := by exact prefixLift 4075961
  have htrace : WordTrace (prefixWord ++ tailWord_4075961) baseStart_4075961 baseEnd_4075961 := by
    simpa [prefixWord, tailWord_4075961, baseEnd_4075961] using wordTrace_append hprefix tailTrace_4075961
  have hstable : (prefixWord ++ tailWord_4075961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075961).length < 2 ^ (prefixWord ++ tailWord_4075961).sum := by decide
  have hdescent : baseEnd_4075961 < baseStart_4075961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076068 : List Nat := [2, 3, 1, 5, 2, 9]
def baseStart_4076068 : Nat := 118140960795 + 4076068 * 2 ^ 59
def prefixEnd_4076068 : Nat := 4983230072969 + 3 ^ 40 * 4076068 * 2
def baseEnd_4076068 : Nat := 17226189830540441143247

theorem tailTrace_4076068 : CollatzResearch.WordTrace tailWord_4076068 prefixEnd_4076068 17226189830540441143247 := by
  unfold tailWord_4076068
  simp only [CollatzResearch.WordTrace]
  refine ⟨74333206698554623918606429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99110942264739498558141905 74333206698554623918606429)
  ·
    refine ⟨27874952511957983969477411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74333206698554623918606429 27874952511957983969477411)
    ·
      refine ⟨41812428767936975954216117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27874952511957983969477411 41812428767936975954216117)
      ·
        refine ⟨3919915196994091495707761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41812428767936975954216117 3919915196994091495707761)
        ·
          refine ⟨2939936397745568621780821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3919915196994091495707761 2939936397745568621780821)
          ·
            refine ⟨17226189830540441143247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2939936397745568621780821 17226189830540441143247)
            ·
              rfl

theorem cell22_4076068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 9].length) (baseStart_4076068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076068 prefixEnd_4076068 := by exact prefixLift 4076068
  have htrace : WordTrace (prefixWord ++ tailWord_4076068) baseStart_4076068 baseEnd_4076068 := by
    simpa [prefixWord, tailWord_4076068, baseEnd_4076068] using wordTrace_append hprefix tailTrace_4076068
  have hstable : (prefixWord ++ tailWord_4076068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076068).length < 2 ^ (prefixWord ++ tailWord_4076068).sum := by decide
  have hdescent : baseEnd_4076068 < baseStart_4076068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076096 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_4076096 : Nat := 118140960795 + 4076096 * 2 ^ 59
def prefixEnd_4076096 : Nat := 4983230072969 + 3 ^ 40 * 4076096 * 2
def baseEnd_4076096 : Nat := 465110320415330997634307

theorem tailTrace_4076096 : CollatzResearch.WordTrace tailWord_4076096 prefixEnd_4076096 465110320415330997634307 := by
  unfold tailWord_4076096
  simp only [CollatzResearch.WordTrace]
  refine ⟨74333717320503904309616071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99111623094005205746154761 74333717320503904309616071)
  ·
    refine ⟨111500575980755856464424107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74333717320503904309616071 111500575980755856464424107)
    ·
      refine ⟨167250863971133784696636161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111500575980755856464424107 167250863971133784696636161)
      ·
        refine ⟨125438147978350338522477121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167250863971133784696636161 125438147978350338522477121)
        ·
          refine ⟨94078610983762753891857841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125438147978350338522477121 94078610983762753891857841)
          ·
            refine ⟨70558958237822065418893381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94078610983762753891857841 70558958237822065418893381)
            ·
              refine ⟨13229804669591637266042509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70558958237822065418893381 13229804669591637266042509)
              ·
                refine ⟨4961176751096863974765941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13229804669591637266042509 4961176751096863974765941)
                ·
                  refine ⟨465110320415330997634307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961176751096863974765941 465110320415330997634307)
                  ·
                    rfl

theorem cell22_4076096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_4076096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076096 prefixEnd_4076096 := by exact prefixLift 4076096
  have htrace : WordTrace (prefixWord ++ tailWord_4076096) baseStart_4076096 baseEnd_4076096 := by
    simpa [prefixWord, tailWord_4076096, baseEnd_4076096] using wordTrace_append hprefix tailTrace_4076096
  have hstable : (prefixWord ++ tailWord_4076096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076096).length < 2 ^ (prefixWord ++ tailWord_4076096).sum := by decide
  have hdescent : baseEnd_4076096 < baseStart_4076096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076130 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_4076130 : Nat := 118140960795 + 4076130 * 2 ^ 59
def prefixEnd_4076130 : Nat := 4983230072969 + 3 ^ 40 * 4076130 * 2
def baseEnd_4076130 : Nat := 465114200046942745850939

theorem tailTrace_4076130 : CollatzResearch.WordTrace tailWord_4076130 prefixEnd_4076130 465114200046942745850939 := by
  unfold tailWord_4076130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167168680721158106492461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99112449815256421617313229 37167168680721158106492461)
  ·
    refine ⟨13937688255270434289934673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37167168680721158106492461 13937688255270434289934673)
    ·
      refine ⟨10453266191452825717451005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13937688255270434289934673 10453266191452825717451005)
      ·
        refine ⟨3919974821794809644044127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10453266191452825717451005 3919974821794809644044127)
        ·
          refine ⟨5879962232692214466066191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919974821794809644044127 5879962232692214466066191)
          ·
            refine ⟨8819943349038321699099287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879962232692214466066191 8819943349038321699099287)
            ·
              refine ⟨13229915023557482548648931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819943349038321699099287 13229915023557482548648931)
              ·
                refine ⟨19844872535336223822973397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229915023557482548648931 19844872535336223822973397)
                ·
                  refine ⟨465114200046942745850939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19844872535336223822973397 465114200046942745850939)
                  ·
                    rfl

theorem cell22_4076130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_4076130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076130 prefixEnd_4076130 := by exact prefixLift 4076130
  have htrace : WordTrace (prefixWord ++ tailWord_4076130) baseStart_4076130 baseEnd_4076130 := by
    simpa [prefixWord, tailWord_4076130, baseEnd_4076130] using wordTrace_append hprefix tailTrace_4076130
  have hstable : (prefixWord ++ tailWord_4076130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076130).length < 2 ^ (prefixWord ++ tailWord_4076130).sum := by decide
  have hdescent : baseEnd_4076130 < baseStart_4076130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076188 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_4076188 : Nat := 118140960795 + 4076188 * 2 ^ 59
def prefixEnd_4076188 : Nat := 4983230072969 + 3 ^ 40 * 4076188 * 2
def baseEnd_4076188 : Nat := 1395362454726135419602639

theorem tailTrace_4076188 : CollatzResearch.WordTrace tailWord_4076188 prefixEnd_4076188 1395362454726135419602639 := by
  unfold tailWord_4076188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74335395078337254165790609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99113860104449672221054145 74335395078337254165790609)
  ·
    refine ⟨55751546308752940624342957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74335395078337254165790609 55751546308752940624342957)
    ·
      refine ⟨20906829865782352734128609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55751546308752940624342957 20906829865782352734128609)
      ·
        refine ⟨15680122399336764550596457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20906829865782352734128609 15680122399336764550596457)
        ·
          refine ⟨11760091799502573412947343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15680122399336764550596457 11760091799502573412947343)
          ·
            refine ⟨17640137699253860119421015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760091799502573412947343 17640137699253860119421015)
            ·
              refine ⟨26460206548880790179131523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17640137699253860119421015 26460206548880790179131523)
              ·
                refine ⟨39690309823321185268697285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26460206548880790179131523 39690309823321185268697285)
                ·
                  refine ⟨7441933091872722237880741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39690309823321185268697285 7441933091872722237880741)
                  ·
                    refine ⟨1395362454726135419602639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7441933091872722237880741 1395362454726135419602639)
                    ·
                      rfl

theorem cell22_4076188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_4076188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076188 prefixEnd_4076188 := by exact prefixLift 4076188
  have htrace : WordTrace (prefixWord ++ tailWord_4076188) baseStart_4076188 baseEnd_4076188 := by
    simpa [prefixWord, tailWord_4076188, baseEnd_4076188] using wordTrace_append hprefix tailTrace_4076188
  have hstable : (prefixWord ++ tailWord_4076188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076188).length < 2 ^ (prefixWord ++ tailWord_4076188).sum := by decide
  have hdescent : baseEnd_4076188 < baseStart_4076188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076190 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4076190 : Nat := 118140960795 + 4076190 * 2 ^ 59
def prefixEnd_4076190 : Nat := 4983230072969 + 3 ^ 40 * 4076190 * 2
def baseEnd_4076190 : Nat := 1395363139367008081052633

theorem tailTrace_4076190 : CollatzResearch.WordTrace tailWord_4076190 prefixEnd_4076190 1395363139367008081052633 := by
  unfold tailWord_4076190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18583857887833407834144253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99113908735111508448769349 18583857887833407834144253)
  ·
    refine ⟨6968946707937527937804095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18583857887833407834144253 6968946707937527937804095)
    ·
      refine ⟨10453420061906291906706143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6968946707937527937804095 10453420061906291906706143)
      ·
        refine ⟨15680130092859437860059215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453420061906291906706143 15680130092859437860059215)
        ·
          refine ⟨23520195139289156790088823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15680130092859437860059215 23520195139289156790088823)
          ·
            refine ⟨35280292708933735185133235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23520195139289156790088823 35280292708933735185133235)
            ·
              refine ⟨52920439063400602777699853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35280292708933735185133235 52920439063400602777699853)
              ·
                refine ⟨19845164648775226041637445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52920439063400602777699853 19845164648775226041637445)
                ·
                  refine ⟨3720968371645354882807021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19845164648775226041637445 3720968371645354882807021)
                  ·
                    refine ⟨1395363139367008081052633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720968371645354882807021 1395363139367008081052633)
                    ·
                      rfl

theorem cell22_4076190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4076190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076190 prefixEnd_4076190 := by exact prefixLift 4076190
  have htrace : WordTrace (prefixWord ++ tailWord_4076190) baseStart_4076190 baseEnd_4076190 := by
    simpa [prefixWord, tailWord_4076190, baseEnd_4076190] using wordTrace_append hprefix tailTrace_4076190
  have hstable : (prefixWord ++ tailWord_4076190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076190).length < 2 ^ (prefixWord ++ tailWord_4076190).sum := by decide
  have hdescent : baseEnd_4076190 < baseStart_4076190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076192 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_4076192 : Nat := 118140960795 + 4076192 * 2 ^ 59
def prefixEnd_4076192 : Nat := 4983230072969 + 3 ^ 40 * 4076192 * 2
def baseEnd_4076192 : Nat := 465121274669293580834209

theorem tailTrace_4076192 : CollatzResearch.WordTrace tailWord_4076192 prefixEnd_4076192 465121274669293580834209 := by
  unfold tailWord_4076192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74335468024330008507363415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99113957365773344676484553 74335468024330008507363415)
  ·
    refine ⟨111503202036495012761045123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74335468024330008507363415 111503202036495012761045123)
    ·
      refine ⟨167254803054742519141567685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111503202036495012761045123 167254803054742519141567685)
      ·
        refine ⟨31360275572764222339043941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167254803054742519141567685 31360275572764222339043941)
        ·
          refine ⟨5880051669893291688570739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31360275572764222339043941 5880051669893291688570739)
          ·
            refine ⟨8820077504839937532856109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880051669893291688570739 8820077504839937532856109)
            ·
              refine ⟨3307529064314976574821041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8820077504839937532856109 3307529064314976574821041)
              ·
                refine ⟨2480646798236232431115781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307529064314976574821041 2480646798236232431115781)
                ·
                  refine ⟨465121274669293580834209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480646798236232431115781 465121274669293580834209)
                  ·
                    rfl

theorem cell22_4076192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_4076192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076192 prefixEnd_4076192 := by exact prefixLift 4076192
  have htrace : WordTrace (prefixWord ++ tailWord_4076192) baseStart_4076192 baseEnd_4076192 := by
    simpa [prefixWord, tailWord_4076192, baseEnd_4076192] using wordTrace_append hprefix tailTrace_4076192
  have hstable : (prefixWord ++ tailWord_4076192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076192).length < 2 ^ (prefixWord ++ tailWord_4076192).sum := by decide
  have hdescent : baseEnd_4076192 < baseStart_4076192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076207 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 2, 3]
def baseStart_4076207 : Nat := 118140960795 + 4076207 * 2 ^ 59
def prefixEnd_4076207 : Nat := 4983230072969 + 3 ^ 40 * 4076207 * 2
def baseEnd_4076207 : Nat := 1395368958814425703377581

theorem tailTrace_4076207 : CollatzResearch.WordTrace tailWord_4076207 prefixEnd_4076207 1395368958814425703377581 := by
  unfold tailWord_4076207
  simp only [CollatzResearch.WordTrace]
  refine ⟨148671483143605674576522875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99114322095737116384348583 148671483143605674576522875)
  ·
    refine ⟨223007224715408511864784313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148671483143605674576522875 223007224715408511864784313)
    ·
      refine ⟨167255418536556383898588235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223007224715408511864784313 167255418536556383898588235)
      ·
        refine ⟨250883127804834575847882353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167255418536556383898588235 250883127804834575847882353)
        ·
          refine ⟨188162345853625931885911765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250883127804834575847882353 188162345853625931885911765)
          ·
            refine ⟨4410054980944357778576057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188162345853625931885911765 4410054980944357778576057)
            ·
              refine ⟨3307541235708268333932043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410054980944357778576057 3307541235708268333932043)
              ·
                refine ⟨4961311853562402500898065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307541235708268333932043 4961311853562402500898065)
                ·
                  refine ⟨3720983890171801875673549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961311853562402500898065 3720983890171801875673549)
                  ·
                    refine ⟨1395368958814425703377581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720983890171801875673549 1395368958814425703377581)
                    ·
                      rfl

theorem cell22_4076207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_4076207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076207 prefixEnd_4076207 := by exact prefixLift 4076207
  have htrace : WordTrace (prefixWord ++ tailWord_4076207) baseStart_4076207 baseEnd_4076207 := by
    simpa [prefixWord, tailWord_4076207, baseEnd_4076207] using wordTrace_append hprefix tailTrace_4076207
  have hstable : (prefixWord ++ tailWord_4076207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076207).length < 2 ^ (prefixWord ++ tailWord_4076207).sum := by decide
  have hdescent : baseEnd_4076207 < baseStart_4076207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076218 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_4076218 : Nat := 118140960795 + 4076218 * 2 ^ 59
def prefixEnd_4076218 : Nat := 4983230072969 + 3 ^ 40 * 4076218 * 2
def baseEnd_4076218 : Nat := 1395372724339225341352547

theorem tailTrace_4076218 : CollatzResearch.WordTrace tailWord_4076218 prefixEnd_4076218 1395372724339225341352547 := by
  unfold tailWord_4076218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167971086641455863793327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99114589564377215636782205 37167971086641455863793327)
  ·
    refine ⟨55751956629962183795689991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37167971086641455863793327 55751956629962183795689991)
    ·
      refine ⟨83627934944943275693534987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55751956629962183795689991 83627934944943275693534987)
      ·
        refine ⟨125441902417414913540302481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83627934944943275693534987 125441902417414913540302481)
        ·
          refine ⟨94081426813061185155226861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125441902417414913540302481 94081426813061185155226861)
          ·
            refine ⟨35280535054897944433210073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94081426813061185155226861 35280535054897944433210073)
            ·
              refine ⟨26460401291173458324907555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35280535054897944433210073 26460401291173458324907555)
              ·
                refine ⟨39690601936760187487361333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26460401291173458324907555 39690601936760187487361333)
                ·
                  refine ⟨3720993931571267576940125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39690601936760187487361333 3720993931571267576940125)
                  ·
                    refine ⟨1395372724339225341352547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720993931571267576940125 1395372724339225341352547)
                    ·
                      rfl

theorem cell22_4076218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_4076218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076218 prefixEnd_4076218 := by exact prefixLift 4076218
  have htrace : WordTrace (prefixWord ++ tailWord_4076218) baseStart_4076218 baseEnd_4076218 := by
    simpa [prefixWord, tailWord_4076218, baseEnd_4076218] using wordTrace_append hprefix tailTrace_4076218
  have hstable : (prefixWord ++ tailWord_4076218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076218).length < 2 ^ (prefixWord ++ tailWord_4076218).sum := by decide
  have hdescent : baseEnd_4076218 < baseStart_4076218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076231 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 7]
def baseStart_4076231 : Nat := 118140960795 + 4076231 * 2 ^ 59
def prefixEnd_4076231 : Nat := 4983230072969 + 3 ^ 40 * 4076231 * 2
def baseEnd_4076231 : Nat := 465125724834965880259169

theorem tailTrace_4076231 : CollatzResearch.WordTrace tailWord_4076231 prefixEnd_4076231 465125724834965880259169 := by
  unfold tailWord_4076231
  simp only [CollatzResearch.WordTrace]
  refine ⟨148672358495518726675396547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99114905663679151116931031 148672358495518726675396547)
  ·
    refine ⟨223008537743278090013094821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148672358495518726675396547 223008537743278090013094821)
    ·
      refine ⟨41814100826864641877455279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223008537743278090013094821 41814100826864641877455279)
      ·
        refine ⟨62721151240296962816182919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41814100826864641877455279 62721151240296962816182919)
        ·
          refine ⟨94081726860445444224274379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62721151240296962816182919 94081726860445444224274379)
          ·
            refine ⟨141122590290668166336411569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94081726860445444224274379 141122590290668166336411569)
            ·
              refine ⟨105841942718001124752308677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141122590290668166336411569 105841942718001124752308677)
              ·
                refine ⟨19845364259625210891057877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105841942718001124752308677 19845364259625210891057877)
                ·
                  refine ⟨465125724834965880259169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19845364259625210891057877 465125724834965880259169)
                  ·
                    rfl

theorem cell22_4076231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_4076231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076231 prefixEnd_4076231 := by exact prefixLift 4076231
  have htrace : WordTrace (prefixWord ++ tailWord_4076231) baseStart_4076231 baseEnd_4076231 := by
    simpa [prefixWord, tailWord_4076231, baseEnd_4076231] using wordTrace_append hprefix tailTrace_4076231
  have hstable : (prefixWord ++ tailWord_4076231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076231).length < 2 ^ (prefixWord ++ tailWord_4076231).sum := by decide
  have hdescent : baseEnd_4076231 < baseStart_4076231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076248 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_4076248 : Nat := 118140960795 + 4076248 * 2 ^ 59
def prefixEnd_4076248 : Nat := 4983230072969 + 3 ^ 40 * 4076248 * 2
def baseEnd_4076248 : Nat := 465127664650771754367485

theorem tailTrace_4076248 : CollatzResearch.WordTrace tailWord_4076248 prefixEnd_4076248 465127664650771754367485 := by
  unfold tailWord_4076248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74336489268228569289382699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99115319024304759052510265 74336489268228569289382699)
  ·
    refine ⟨111504733902342853934074049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74336489268228569289382699 111504733902342853934074049)
    ·
      refine ⟨83628550426757140450555537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111504733902342853934074049 83628550426757140450555537)
      ·
        refine ⟨62721412820067855337916653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83628550426757140450555537 62721412820067855337916653)
        ·
          refine ⟨23520529807525445751718745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62721412820067855337916653 23520529807525445751718745)
          ·
            refine ⟨17640397355644084313789059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23520529807525445751718745 17640397355644084313789059)
            ·
              refine ⟨26460596033466126470683589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17640397355644084313789059 26460596033466126470683589)
              ·
                refine ⟨4961361756274898713253173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26460596033466126470683589 4961361756274898713253173)
                ·
                  refine ⟨465127664650771754367485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961361756274898713253173 465127664650771754367485)
                  ·
                    rfl

theorem cell22_4076248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_4076248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076248 prefixEnd_4076248 := by exact prefixLift 4076248
  have htrace : WordTrace (prefixWord ++ tailWord_4076248) baseStart_4076248 baseEnd_4076248 := by
    simpa [prefixWord, tailWord_4076248, baseEnd_4076248] using wordTrace_append hprefix tailTrace_4076248
  have hstable : (prefixWord ++ tailWord_4076248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076248).length < 2 ^ (prefixWord ++ tailWord_4076248).sum := by decide
  have hdescent : baseEnd_4076248 < baseStart_4076248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076338 : List Nat := [3, 2, 1, 1, 3, 1, 3, 8]
def baseStart_4076338 : Nat := 118140960795 + 4076338 * 2 ^ 59
def prefixEnd_4076338 : Nat := 4983230072969 + 3 ^ 40 * 4076338 * 2
def baseEnd_4076338 : Nat := 155045978087953892039131

theorem tailTrace_4076338 : CollatzResearch.WordTrace tailWord_4076338 prefixEnd_4076338 155045978087953892039131 := by
  unfold tailWord_4076338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37169065276532770987385417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99117507404087389299694445 37169065276532770987385417)
  ·
    refine ⟨27876798957399578240539063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37169065276532770987385417 27876798957399578240539063)
    ·
      refine ⟨41815198436099367360808595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27876798957399578240539063 41815198436099367360808595)
      ·
        refine ⟨62722797654149051041212893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41815198436099367360808595 62722797654149051041212893)
        ·
          refine ⟨23521049120305894140454835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62722797654149051041212893 23521049120305894140454835)
          ·
            refine ⟨35281573680458841210682253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23521049120305894140454835 35281573680458841210682253)
            ·
              refine ⟨13230590130172065454005845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35281573680458841210682253 13230590130172065454005845)
              ·
                refine ⟨155045978087953892039131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13230590130172065454005845 155045978087953892039131)
                ·
                  rfl

theorem cell22_4076338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_4076338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076338 prefixEnd_4076338 := by exact prefixLift 4076338
  have htrace : WordTrace (prefixWord ++ tailWord_4076338) baseStart_4076338 baseEnd_4076338 := by
    simpa [prefixWord, tailWord_4076338, baseEnd_4076338] using wordTrace_append hprefix tailTrace_4076338
  have hstable : (prefixWord ++ tailWord_4076338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076338).length < 2 ^ (prefixWord ++ tailWord_4076338).sum := by decide
  have hdescent : baseEnd_4076338 < baseStart_4076338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076421 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_4076421 : Nat := 118140960795 + 4076421 * 2 ^ 59
def prefixEnd_4076421 : Nat := 4983230072969 + 3 ^ 40 * 4076421 * 2
def baseEnd_4076421 : Nat := 1395442215387800478526925

theorem tailTrace_4076421 : CollatzResearch.WordTrace tailWord_4076421 prefixEnd_4076421 1395442215387800478526925 := by
  unfold tailWord_4076421
  simp only [CollatzResearch.WordTrace]
  refine ⟨148679288364830389124813117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99119525576553592749875411 148679288364830389124813117)
  ·
    refine ⟨55754733136811395921804919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148679288364830389124813117 55754733136811395921804919)
    ·
      refine ⟨83632099705217093882707379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55754733136811395921804919 83632099705217093882707379)
      ·
        refine ⟨125448149557825640824061069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83632099705217093882707379 125448149557825640824061069)
        ·
          refine ⟨47043056084184615309022901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125448149557825640824061069 47043056084184615309022901)
          ·
            refine ⟨4410286507892307685220897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47043056084184615309022901 4410286507892307685220897)
            ·
              refine ⟨3307714880919230763915673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410286507892307685220897 3307714880919230763915673)
              ·
                refine ⟨2480786160689423072936755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307714880919230763915673 2480786160689423072936755)
                ·
                  refine ⟨3721179241034134609405133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480786160689423072936755 3721179241034134609405133)
                  ·
                    refine ⟨1395442215387800478526925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721179241034134609405133 1395442215387800478526925)
                    ·
                      rfl

theorem cell22_4076421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_4076421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076421 prefixEnd_4076421 := by exact prefixLift 4076421
  have htrace : WordTrace (prefixWord ++ tailWord_4076421) baseStart_4076421 baseEnd_4076421 := by
    simpa [prefixWord, tailWord_4076421, baseEnd_4076421] using wordTrace_append hprefix tailTrace_4076421
  have hstable : (prefixWord ++ tailWord_4076421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076421).length < 2 ^ (prefixWord ++ tailWord_4076421).sum := by decide
  have hdescent : baseEnd_4076421 < baseStart_4076421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076445 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 6]
def baseStart_4076445 : Nat := 118140960795 + 4076445 * 2 ^ 59
def prefixEnd_4076445 : Nat := 4983230072969 + 3 ^ 40 * 4076445 * 2
def baseEnd_4076445 : Nat := 465150143692757471975617

theorem tailTrace_4076445 : CollatzResearch.WordTrace tailWord_4076445 prefixEnd_4076445 465150143692757471975617 := by
  unfold tailWord_4076445
  simp only [CollatzResearch.WordTrace]
  refine ⟨148680163716743441223686789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99120109144495627482457859 148680163716743441223686789)
  ·
    refine ⟨27877530696889395229441273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148680163716743441223686789 27877530696889395229441273)
    ·
      refine ⟨20908148022667046422080955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27877530696889395229441273 20908148022667046422080955)
      ·
        refine ⟨31362222034000569633121433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20908148022667046422080955 31362222034000569633121433)
        ·
          refine ⟨23521666525500427224841075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31362222034000569633121433 23521666525500427224841075)
          ·
            refine ⟨35282499788250640837261613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23521666525500427224841075 35282499788250640837261613)
            ·
              refine ⟨13230937420593990313973105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35282499788250640837261613 13230937420593990313973105)
              ·
                refine ⟨9923203065445492735479829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13230937420593990313973105 9923203065445492735479829)
                ·
                  refine ⟨465150143692757471975617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9923203065445492735479829 465150143692757471975617)
                  ·
                    rfl

theorem cell22_4076445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_4076445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076445 prefixEnd_4076445 := by exact prefixLift 4076445
  have htrace : WordTrace (prefixWord ++ tailWord_4076445) baseStart_4076445 baseEnd_4076445 := by
    simpa [prefixWord, tailWord_4076445, baseEnd_4076445] using wordTrace_append hprefix tailTrace_4076445
  have hstable : (prefixWord ++ tailWord_4076445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076445).length < 2 ^ (prefixWord ++ tailWord_4076445).sum := by decide
  have hdescent : baseEnd_4076445 < baseStart_4076445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076460 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_4076460 : Nat := 118140960795 + 4076460 * 2 ^ 59
def prefixEnd_4076460 : Nat := 4983230072969 + 3 ^ 40 * 4076460 * 2
def baseEnd_4076460 : Nat := 1395455565884817376801805

theorem tailTrace_4076460 : CollatzResearch.WordTrace tailWord_4076460 prefixEnd_4076460 1395455565884817376801805 := by
  unfold tailWord_4076460
  simp only [CollatzResearch.WordTrace]
  refine ⟨74340355405844549392741417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99120473874459399190321889 74340355405844549392741417)
  ·
    refine ⟨55755266554383412044556063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74340355405844549392741417 55755266554383412044556063)
    ·
      refine ⟨83632899831575118066834095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55755266554383412044556063 83632899831575118066834095)
      ·
        refine ⟨125449349747362677100251143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83632899831575118066834095 125449349747362677100251143)
        ·
          refine ⟨188174024621044015650376715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125449349747362677100251143 188174024621044015650376715)
          ·
            refine ⟨282261036931566023475565073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188174024621044015650376715 282261036931566023475565073)
            ·
              refine ⟨211695777698674517606673805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282261036931566023475565073 211695777698674517606673805)
              ·
                refine ⟨79385916637002944102502677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211695777698674517606673805 79385916637002944102502677)
                ·
                  refine ⟨3721214842359513004804813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79385916637002944102502677 3721214842359513004804813)
                  ·
                    refine ⟨1395455565884817376801805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721214842359513004804813 1395455565884817376801805)
                    ·
                      rfl

theorem cell22_4076460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_4076460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076460 prefixEnd_4076460 := by exact prefixLift 4076460
  have htrace : WordTrace (prefixWord ++ tailWord_4076460) baseStart_4076460 baseEnd_4076460 := by
    simpa [prefixWord, tailWord_4076460, baseEnd_4076460] using wordTrace_append hprefix tailTrace_4076460
  have hstable : (prefixWord ++ tailWord_4076460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076460).length < 2 ^ (prefixWord ++ tailWord_4076460).sum := by decide
  have hdescent : baseEnd_4076460 < baseStart_4076460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076552 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_4076552 : Nat := 118140960795 + 4076552 * 2 ^ 59
def prefixEnd_4076552 : Nat := 4983230072969 + 3 ^ 40 * 4076552 * 2
def baseEnd_4076552 : Nat := 465162353121653267833841

theorem tailTrace_4076552 : CollatzResearch.WordTrace tailWord_4076552 prefixEnd_4076552 465162353121653267833841 := by
  unfold tailWord_4076552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74342033163677899248915955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99122710884903865665221273 74342033163677899248915955)
  ·
    refine ⟨111513049745516848873373933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74342033163677899248915955 111513049745516848873373933)
    ·
      refine ⟨41817393654568818327515225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111513049745516848873373933 41817393654568818327515225)
      ·
        refine ⟨31363045240926613745636419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41817393654568818327515225 31363045240926613745636419)
        ·
          refine ⟨47044567861389920618454629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31363045240926613745636419 47044567861389920618454629)
          ·
            refine ⟨8820856474010610115960243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47044567861389920618454629 8820856474010610115960243)
            ·
              refine ⟨13231284711015915173940365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820856474010610115960243 13231284711015915173940365)
              ·
                refine ⟨4961731766630968190227637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13231284711015915173940365 4961731766630968190227637)
                ·
                  refine ⟨465162353121653267833841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961731766630968190227637 465162353121653267833841)
                  ·
                    rfl

theorem cell22_4076552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_4076552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076552 prefixEnd_4076552 := by exact prefixLift 4076552
  have htrace : WordTrace (prefixWord ++ tailWord_4076552) baseStart_4076552 baseEnd_4076552 := by
    simpa [prefixWord, tailWord_4076552, baseEnd_4076552] using wordTrace_append hprefix tailTrace_4076552
  have hstable : (prefixWord ++ tailWord_4076552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076552).length < 2 ^ (prefixWord ++ tailWord_4076552).sum := by decide
  have hdescent : baseEnd_4076552 < baseStart_4076552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076595 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_4076595 : Nat := 118140960795 + 4076595 * 2 ^ 59
def prefixEnd_4076595 : Nat := 4983230072969 + 3 ^ 40 * 4076595 * 2
def baseEnd_4076595 : Nat := 1395501779143722024676391

theorem tailTrace_4076595 : CollatzResearch.WordTrace tailWord_4076595 prefixEnd_4076595 1395501779143722024676391 := by
  unfold tailWord_4076595
  simp only [CollatzResearch.WordTrace]
  refine ⟨148685634666200016841647239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99123756444133344561098159 148685634666200016841647239)
  ·
    refine ⟨223028451999300025262470859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148685634666200016841647239 223028451999300025262470859)
    ·
      refine ⟨334542677998950037893706289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223028451999300025262470859 334542677998950037893706289)
      ·
        refine ⟨250907008499212528420279717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334542677998950037893706289 250907008499212528420279717)
        ·
          refine ⟨47045064093602349078802447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250907008499212528420279717 47045064093602349078802447)
          ·
            refine ⟨70567596140403523618203671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47045064093602349078802447 70567596140403523618203671)
            ·
              refine ⟨105851394210605285427305507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70567596140403523618203671 105851394210605285427305507)
              ·
                refine ⟨158777091315907928140958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105851394210605285427305507 158777091315907928140958261)
                ·
                  refine ⟨14885352310866368263214837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158777091315907928140958261 14885352310866368263214837)
                  ·
                    refine ⟨1395501779143722024676391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14885352310866368263214837 1395501779143722024676391)
                    ·
                      rfl

theorem cell22_4076595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_4076595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076595 prefixEnd_4076595 := by exact prefixLift 4076595
  have htrace : WordTrace (prefixWord ++ tailWord_4076595) baseStart_4076595 baseEnd_4076595 := by
    simpa [prefixWord, tailWord_4076595, baseEnd_4076595] using wordTrace_append hprefix tailTrace_4076595
  have hstable : (prefixWord ++ tailWord_4076595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076595).length < 2 ^ (prefixWord ++ tailWord_4076595).sum := by decide
  have hdescent : baseEnd_4076595 < baseStart_4076595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076614 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4076614 : Nat := 118140960795 + 4076614 * 2 ^ 59
def prefixEnd_4076614 : Nat := 4983230072969 + 3 ^ 40 * 4076614 * 2
def baseEnd_4076614 : Nat := 465169427744004102817111

theorem tailTrace_4076614 : CollatzResearch.WordTrace tailWord_4076614 prefixEnd_4076614 465169427744004102817111 := by
  unfold tailWord_4076614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646447739160349471455903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99124218435420788724392597 4646447739160349471455903)
  ·
    refine ⟨6969671608740524207183855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4646447739160349471455903 6969671608740524207183855)
    ·
      refine ⟨10454507413110786310775783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969671608740524207183855 10454507413110786310775783)
      ·
        refine ⟨15681761119666179466163675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454507413110786310775783 15681761119666179466163675)
        ·
          refine ⟨23522641679499269199245513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681761119666179466163675 23522641679499269199245513)
          ·
            refine ⟨17641981259624451899434135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23522641679499269199245513 17641981259624451899434135)
            ·
              refine ⟨26462971889436677849151203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17641981259624451899434135 26462971889436677849151203)
              ·
                refine ⟨39694457834155016773726805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26462971889436677849151203 39694457834155016773726805)
                ·
                  refine ⟨465169427744004102817111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39694457834155016773726805 465169427744004102817111)
                  ·
                    rfl

theorem cell22_4076614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4076614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076614 prefixEnd_4076614 := by exact prefixLift 4076614
  have htrace : WordTrace (prefixWord ++ tailWord_4076614) baseStart_4076614 baseEnd_4076614 := by
    simpa [prefixWord, tailWord_4076614, baseEnd_4076614] using wordTrace_append hprefix tailTrace_4076614
  have hstable : (prefixWord ++ tailWord_4076614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076614).length < 2 ^ (prefixWord ++ tailWord_4076614).sum := by decide
  have hdescent : baseEnd_4076614 < baseStart_4076614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076625 : List Nat := [1, 2, 2, 1, 3, 1, 2, 10]
def baseStart_4076625 : Nat := 118140960795 + 4076625 * 2 ^ 59
def prefixEnd_4076625 : Nat := 4983230072969 + 3 ^ 40 * 4076625 * 2
def baseEnd_4076625 : Nat := 155056894306312438491811

theorem tailTrace_4076625 : CollatzResearch.WordTrace tailWord_4076625 prefixEnd_4076625 155056894306312438491811 := by
  unfold tailWord_4076625
  simp only [CollatzResearch.WordTrace]
  refine ⟨148686728856091331965239329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99124485904060887976826219 148686728856091331965239329)
  ·
    refine ⟨111515046642068498973929497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148686728856091331965239329 111515046642068498973929497)
    ·
      refine ⟨83636284981551374230447123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111515046642068498973929497 83636284981551374230447123)
      ·
        refine ⟨125454427472327061345670685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83636284981551374230447123 125454427472327061345670685)
        ·
          refine ⟨47045410302122648004626507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125454427472327061345670685 47045410302122648004626507)
          ·
            refine ⟨70568115453183972006939761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47045410302122648004626507 70568115453183972006939761)
            ·
              refine ⟨52926086589887979005204821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70568115453183972006939761 52926086589887979005204821)
              ·
                refine ⟨155056894306312438491811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52926086589887979005204821 155056894306312438491811)
                ·
                  rfl

theorem cell22_4076625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 10].length) (baseStart_4076625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076625 prefixEnd_4076625 := by exact prefixLift 4076625
  have htrace : WordTrace (prefixWord ++ tailWord_4076625) baseStart_4076625 baseEnd_4076625 := by
    simpa [prefixWord, tailWord_4076625, baseEnd_4076625] using wordTrace_append hprefix tailTrace_4076625
  have hstable : (prefixWord ++ tailWord_4076625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076625).length < 2 ^ (prefixWord ++ tailWord_4076625).sum := by decide
  have hdescent : baseEnd_4076625 < baseStart_4076625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076691 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 1, 3]
def baseStart_4076691 : Nat := 118140960795 + 4076691 * 2 ^ 59
def prefixEnd_4076691 : Nat := 4983230072969 + 3 ^ 40 * 4076691 * 2
def baseEnd_4076691 : Nat := 1395534641905609774276097

theorem tailTrace_4076691 : CollatzResearch.WordTrace tailWord_4076691 prefixEnd_4076691 1395534641905609774276097 := by
  unfold tailWord_4076691
  simp only [CollatzResearch.WordTrace]
  refine ⟨148689136073852225237141927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99126090715901483491427951 148689136073852225237141927)
  ·
    refine ⟨223033704110778337855712891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148689136073852225237141927 223033704110778337855712891)
    ·
      refine ⟨334550556166167506783569337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223033704110778337855712891 334550556166167506783569337)
      ·
        refine ⟨250912917124625630087677003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334550556166167506783569337 250912917124625630087677003)
        ·
          refine ⟨376369375686938445131515505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250912917124625630087677003 376369375686938445131515505)
          ·
            refine ⟨282277031765203833848636629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376369375686938445131515505 282277031765203833848636629)
            ·
              refine ⟨6615867931996964855827421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 282277031765203833848636629 6615867931996964855827421)
              ·
                refine ⟨2480950474498861820935283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6615867931996964855827421 2480950474498861820935283)
                ·
                  refine ⟨3721425711748292731402925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480950474498861820935283 3721425711748292731402925)
                  ·
                    refine ⟨1395534641905609774276097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721425711748292731402925 1395534641905609774276097)
                    ·
                      rfl

theorem cell22_4076691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 3].length) (baseStart_4076691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076691 prefixEnd_4076691 := by exact prefixLift 4076691
  have htrace : WordTrace (prefixWord ++ tailWord_4076691) baseStart_4076691 baseEnd_4076691 := by
    simpa [prefixWord, tailWord_4076691, baseEnd_4076691] using wordTrace_append hprefix tailTrace_4076691
  have hstable : (prefixWord ++ tailWord_4076691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076691).length < 2 ^ (prefixWord ++ tailWord_4076691).sum := by decide
  have hdescent : baseEnd_4076691 < baseStart_4076691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076721 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 5]
def baseStart_4076721 : Nat := 118140960795 + 4076721 * 2 ^ 59
def prefixEnd_4076721 : Nat := 4983230072969 + 3 ^ 40 * 4076721 * 2
def baseEnd_4076721 : Nat := 465181637172899898675335

theorem tailTrace_4076721 : CollatzResearch.WordTrace tailWord_4076721 prefixEnd_4076721 465181637172899898675335 := by
  unfold tailWord_4076721
  simp only [CollatzResearch.WordTrace]
  refine ⟨148690230263743540360734017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99126820175829026907156011 148690230263743540360734017)
  ·
    refine ⟨111517672697807655270550513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148690230263743540360734017 111517672697807655270550513)
    ·
      refine ⟨83638254523355741452912885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111517672697807655270550513 83638254523355741452912885)
      ·
        refine ⟨7841086361564600761210583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83638254523355741452912885 7841086361564600761210583)
        ·
          refine ⟨11761629542346901141815875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841086361564600761210583 11761629542346901141815875)
          ·
            refine ⟨17642444313520351712723813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761629542346901141815875 17642444313520351712723813)
            ·
              refine ⟨3307958308785065946135715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17642444313520351712723813 3307958308785065946135715)
              ·
                refine ⟨4961937463177598919203573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307958308785065946135715 4961937463177598919203573)
                ·
                  refine ⟨465181637172899898675335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961937463177598919203573 465181637172899898675335)
                  ·
                    rfl

theorem cell22_4076721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_4076721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076721 prefixEnd_4076721 := by exact prefixLift 4076721
  have htrace : WordTrace (prefixWord ++ tailWord_4076721) baseStart_4076721 baseEnd_4076721 := by
    simpa [prefixWord, tailWord_4076721, baseEnd_4076721] using wordTrace_append hprefix tailTrace_4076721
  have hstable : (prefixWord ++ tailWord_4076721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076721).length < 2 ^ (prefixWord ++ tailWord_4076721).sum := by decide
  have hdescent : baseEnd_4076721 < baseStart_4076721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076762 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_4076762 : Nat := 118140960795 + 4076762 * 2 ^ 59
def prefixEnd_4076762 : Nat := 4983230072969 + 3 ^ 40 * 4076762 * 2
def baseEnd_4076762 : Nat := 1395558946656589255750879

theorem tailTrace_4076762 : CollatzResearch.WordTrace tailWord_4076762 prefixEnd_4076762 1395558946656589255750879 := by
  unfold tailWord_4076762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172931414148751090744135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99127817104396669575317693 37172931414148751090744135)
  ·
    refine ⟨55759397121223126636116203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37172931414148751090744135 55759397121223126636116203)
    ·
      refine ⟨83639095681834689954174305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55759397121223126636116203 83639095681834689954174305)
      ·
        refine ⟨62729321761376017465630729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83639095681834689954174305 62729321761376017465630729)
        ·
          refine ⟨47046991321032013099223047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62729321761376017465630729 47046991321032013099223047)
          ·
            refine ⟨70570486981548019648834571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47046991321032013099223047 70570486981548019648834571)
            ·
              refine ⟨105855730472322029473251857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70570486981548019648834571 105855730472322029473251857)
              ·
                refine ⟨79391797854241522104938893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105855730472322029473251857 79391797854241522104938893)
                ·
                  refine ⟨29771924195340570789352085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79391797854241522104938893 29771924195340570789352085)
                  ·
                    refine ⟨1395558946656589255750879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29771924195340570789352085 1395558946656589255750879)
                    ·
                      rfl

theorem cell22_4076762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_4076762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076762 prefixEnd_4076762 := by exact prefixLift 4076762
  have htrace : WordTrace (prefixWord ++ tailWord_4076762) baseStart_4076762 baseEnd_4076762 := by
    simpa [prefixWord, tailWord_4076762, baseEnd_4076762] using wordTrace_append hprefix tailTrace_4076762
  have hstable : (prefixWord ++ tailWord_4076762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076762).length < 2 ^ (prefixWord ++ tailWord_4076762).sum := by decide
  have hdescent : baseEnd_4076762 < baseStart_4076762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076781 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4076781 : Nat := 118140960795 + 4076781 * 2 ^ 59
def prefixEnd_4076781 : Nat := 4983230072969 + 3 ^ 40 * 4076781 * 2
def baseEnd_4076781 : Nat := 1395565450744879539525821

theorem tailTrace_4076781 : CollatzResearch.WordTrace tailWord_4076781 prefixEnd_4076781 1395565450744879539525821 := by
  unfold tailWord_4076781
  simp only [CollatzResearch.WordTrace]
  refine ⟨148692418643526170607918197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99128279095684113738612131 148692418643526170607918197)
  ·
    refine ⟨13939914247830578494492331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148692418643526170607918197 13939914247830578494492331)
    ·
      refine ⟨20909871371745867741738497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939914247830578494492331 20909871371745867741738497)
      ·
        refine ⟨15682403528809400806303873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20909871371745867741738497 15682403528809400806303873)
        ·
          refine ⟨11761802646607050604727905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682403528809400806303873 11761802646607050604727905)
          ·
            refine ⟨8821351984955287953545929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761802646607050604727905 8821351984955287953545929)
            ·
              refine ⟨6616013988716465965159447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821351984955287953545929 6616013988716465965159447)
              ·
                refine ⟨9924020983074698947739171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616013988716465965159447 9924020983074698947739171)
                ·
                  refine ⟨14886031474612048421608757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924020983074698947739171 14886031474612048421608757)
                  ·
                    refine ⟨1395565450744879539525821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14886031474612048421608757 1395565450744879539525821)
                    ·
                      rfl

theorem cell22_4076781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4076781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076781 prefixEnd_4076781 := by exact prefixLift 4076781
  have htrace : WordTrace (prefixWord ++ tailWord_4076781) baseStart_4076781 baseEnd_4076781 := by
    simpa [prefixWord, tailWord_4076781, baseEnd_4076781] using wordTrace_append hprefix tailTrace_4076781
  have hstable : (prefixWord ++ tailWord_4076781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076781).length < 2 ^ (prefixWord ++ tailWord_4076781).sum := by decide
  have hdescent : baseEnd_4076781 < baseStart_4076781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076794 : List Nat := [3, 1, 1, 1, 1, 4, 5, 6]
def baseStart_4076794 : Nat := 118140960795 + 4076794 * 2 ^ 59
def prefixEnd_4076794 : Nat := 4983230072969 + 3 ^ 40 * 4076794 * 2
def baseEnd_4076794 : Nat := 155063322323394648772309

theorem tailTrace_4076794 : CollatzResearch.WordTrace tailWord_4076794 prefixEnd_4076794 155063322323394648772309 := by
  unfold tailWord_4076794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173223198119768457035359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99128595194986049218760957 37173223198119768457035359)
  ·
    refine ⟨55759834797179652685553039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37173223198119768457035359 55759834797179652685553039)
    ·
      refine ⟨83639752195769479028329559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55759834797179652685553039 83639752195769479028329559)
      ·
        refine ⟨125459628293654218542494339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83639752195769479028329559 125459628293654218542494339)
        ·
          refine ⟨188189442440481327813741509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125459628293654218542494339 188189442440481327813741509)
          ·
            refine ⟨35285520457590248965076533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188189442440481327813741509 35285520457590248965076533)
            ·
              refine ⟨3308017542899085840475925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35285520457590248965076533 3308017542899085840475925)
              ·
                refine ⟨155063322323394648772309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3308017542899085840475925 155063322323394648772309)
                ·
                  rfl

theorem cell22_4076794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_4076794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076794 prefixEnd_4076794 := by exact prefixLift 4076794
  have htrace : WordTrace (prefixWord ++ tailWord_4076794) baseStart_4076794 baseEnd_4076794 := by
    simpa [prefixWord, tailWord_4076794, baseEnd_4076794] using wordTrace_append hprefix tailTrace_4076794
  have hstable : (prefixWord ++ tailWord_4076794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076794).length < 2 ^ (prefixWord ++ tailWord_4076794).sum := by decide
  have hdescent : baseEnd_4076794 < baseStart_4076794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076802 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_4076802 : Nat := 118140960795 + 4076802 * 2 ^ 59
def prefixEnd_4076802 : Nat := 4983230072969 + 3 ^ 40 * 4076802 * 2
def baseEnd_4076802 : Nat := 1395572639474042484750757

theorem tailTrace_4076802 : CollatzResearch.WordTrace tailWord_4076802 prefixEnd_4076802 1395572639474042484750757 := by
  unfold tailWord_4076802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173296144112522798608165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99128789717633394129621773 37173296144112522798608165)
  ·
    refine ⟨6969993027021098024739031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37173296144112522798608165 6969993027021098024739031)
    ·
      refine ⟨10454989540531647037108547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969993027021098024739031 10454989540531647037108547)
      ·
        refine ⟨15682484310797470555662821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454989540531647037108547 15682484310797470555662821)
        ·
          refine ⟨2940465808274525729186779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15682484310797470555662821 2940465808274525729186779)
          ·
            refine ⟨4410698712411788593780169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940465808274525729186779 4410698712411788593780169)
            ·
              refine ⟨3308024034308841445335127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410698712411788593780169 3308024034308841445335127)
              ·
                refine ⟨4962036051463262168002691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308024034308841445335127 4962036051463262168002691)
                ·
                  refine ⟨7443054077194893252004037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962036051463262168002691 7443054077194893252004037)
                  ·
                    refine ⟨1395572639474042484750757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443054077194893252004037 1395572639474042484750757)
                    ·
                      rfl

theorem cell22_4076802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_4076802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076802 prefixEnd_4076802 := by exact prefixLift 4076802
  have htrace : WordTrace (prefixWord ++ tailWord_4076802) baseStart_4076802 baseEnd_4076802 := by
    simpa [prefixWord, tailWord_4076802, baseEnd_4076802] using wordTrace_append hprefix tailTrace_4076802
  have hstable : (prefixWord ++ tailWord_4076802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076802).length < 2 ^ (prefixWord ++ tailWord_4076802).sum := by decide
  have hdescent : baseEnd_4076802 < baseStart_4076802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076809 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_4076809 : Nat := 118140960795 + 4076809 * 2 ^ 59
def prefixEnd_4076809 : Nat := 4983230072969 + 3 ^ 40 * 4076809 * 2
def baseEnd_4076809 : Nat := 1395575035717096799825735

theorem tailTrace_4076809 : CollatzResearch.WordTrace tailWord_4076809 prefixEnd_4076809 1395575035717096799825735 := by
  unfold tailWord_4076809
  simp only [CollatzResearch.WordTrace]
  refine ⟨148693439887424731389937481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99128959924949820926624987 148693439887424731389937481)
  ·
    refine ⟨111520079915568548542453111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148693439887424731389937481 111520079915568548542453111)
    ·
      refine ⟨167280119873352822813679667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111520079915568548542453111 167280119873352822813679667)
      ·
        refine ⟨250920179810029234220519501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167280119873352822813679667 250920179810029234220519501)
        ·
          refine ⟨94095067428760962832694813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250920179810029234220519501 94095067428760962832694813)
          ·
            refine ⟨35285650285785361062260555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94095067428760962832694813 35285650285785361062260555)
            ·
              refine ⟨52928475428678041593390833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35285650285785361062260555 52928475428678041593390833)
              ·
                refine ⟨39696356571508531195043125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52928475428678041593390833 39696356571508531195043125)
                ·
                  refine ⟨3721533428578924799535293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39696356571508531195043125 3721533428578924799535293)
                  ·
                    refine ⟨1395575035717096799825735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721533428578924799535293 1395575035717096799825735)
                    ·
                      rfl

theorem cell22_4076809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_4076809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076809 prefixEnd_4076809 := by exact prefixLift 4076809
  have htrace : WordTrace (prefixWord ++ tailWord_4076809) baseStart_4076809 baseEnd_4076809 := by
    simpa [prefixWord, tailWord_4076809, baseEnd_4076809] using wordTrace_append hprefix tailTrace_4076809
  have hstable : (prefixWord ++ tailWord_4076809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076809).length < 2 ^ (prefixWord ++ tailWord_4076809).sum := by decide
  have hdescent : baseEnd_4076809 < baseStart_4076809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076826 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_4076826 : Nat := 118140960795 + 4076826 * 2 ^ 59
def prefixEnd_4076826 : Nat := 4983230072969 + 3 ^ 40 * 4076826 * 2
def baseEnd_4076826 : Nat := 1395580855164514422150683

theorem tailTrace_4076826 : CollatzResearch.WordTrace tailWord_4076826 prefixEnd_4076826 1395580855164514422150683 := by
  unfold tailWord_4076826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173514982090785823326583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99129373285575428862204221 37173514982090785823326583)
  ·
    refine ⟨55760272473136178734989875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37173514982090785823326583 55760272473136178734989875)
    ·
      refine ⟨83640408709704268102484813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55760272473136178734989875 83640408709704268102484813)
      ·
        refine ⟨31365153266139100538431805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83640408709704268102484813 31365153266139100538431805)
        ·
          refine ⟨11761932474802162701911927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31365153266139100538431805 11761932474802162701911927)
          ·
            refine ⟨17642898712203244052867891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761932474802162701911927 17642898712203244052867891)
            ·
              refine ⟨26464348068304866079301837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642898712203244052867891 26464348068304866079301837)
              ·
                refine ⟨9924130525614324779738189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26464348068304866079301837 9924130525614324779738189)
                ·
                  refine ⟨3721548947105371792401821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9924130525614324779738189 3721548947105371792401821)
                  ·
                    refine ⟨1395580855164514422150683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721548947105371792401821 1395580855164514422150683)
                    ·
                      rfl

theorem cell22_4076826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_4076826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076826 prefixEnd_4076826 := by exact prefixLift 4076826
  have htrace : WordTrace (prefixWord ++ tailWord_4076826) baseStart_4076826 baseEnd_4076826 := by
    simpa [prefixWord, tailWord_4076826, baseEnd_4076826] using wordTrace_append hprefix tailTrace_4076826
  have hstable : (prefixWord ++ tailWord_4076826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076826).length < 2 ^ (prefixWord ++ tailWord_4076826).sum := by decide
  have hdescent : baseEnd_4076826 < baseStart_4076826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076860 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_4076860 : Nat := 118140960795 + 4076860 * 2 ^ 59
def prefixEnd_4076860 : Nat := 4983230072969 + 3 ^ 40 * 4076860 * 2
def baseEnd_4076860 : Nat := 1395592494059349666800579

theorem tailTrace_4076860 : CollatzResearch.WordTrace tailWord_4076860 prefixEnd_4076860 1395592494059349666800579 := by
  unfold tailWord_4076860
  simp only [CollatzResearch.WordTrace]
  refine ⟨74347650005119983550022017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99130200006826644733362689 74347650005119983550022017)
  ·
    refine ⟨55760737503839987662516513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74347650005119983550022017 55760737503839987662516513)
    ·
      refine ⟨41820553127879990746887385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55760737503839987662516513 41820553127879990746887385)
      ·
        refine ⟨31365414845909993060165539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41820553127879990746887385 31365414845909993060165539)
        ·
          refine ⟨47048122268864989590248309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31365414845909993060165539 47048122268864989590248309)
          ·
            refine ⟨4410761462706092774085779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47048122268864989590248309 4410761462706092774085779)
            ·
              refine ⟨6616142194059139161128669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410761462706092774085779 6616142194059139161128669)
              ·
                refine ⟨2481053322772177185423251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6616142194059139161128669 2481053322772177185423251)
                ·
                  refine ⟨3721579984158265778134877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481053322772177185423251 3721579984158265778134877)
                  ·
                    refine ⟨1395592494059349666800579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721579984158265778134877 1395592494059349666800579)
                    ·
                      rfl

theorem cell22_4076860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_4076860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076860 prefixEnd_4076860 := by exact prefixLift 4076860
  have htrace : WordTrace (prefixWord ++ tailWord_4076860) baseStart_4076860 baseEnd_4076860 := by
    simpa [prefixWord, tailWord_4076860, baseEnd_4076860] using wordTrace_append hprefix tailTrace_4076860
  have hstable : (prefixWord ++ tailWord_4076860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076860).length < 2 ^ (prefixWord ++ tailWord_4076860).sum := by decide
  have hdescent : baseEnd_4076860 < baseStart_4076860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076877 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4076877 : Nat := 118140960795 + 4076877 * 2 ^ 59
def prefixEnd_4076877 : Nat := 4983230072969 + 3 ^ 40 * 4076877 * 2
def baseEnd_4076877 : Nat := 1395598313506767289125527

theorem tailTrace_4076877 : CollatzResearch.WordTrace tailWord_4076877 prefixEnd_4076877 1395598313506767289125527 := by
  unfold tailWord_4076877
  simp only [CollatzResearch.WordTrace]
  refine ⟨148695920051178379003412885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99130613367452252668941923 148695920051178379003412885)
  ·
    refine ⟨6970121252398986515784979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148695920051178379003412885 6970121252398986515784979)
    ·
      refine ⟨10455181878598479773677469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970121252398986515784979 10455181878598479773677469)
      ·
        refine ⟨3920693204474429915129051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10455181878598479773677469 3920693204474429915129051)
        ·
          refine ⟨5881039806711644872693577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920693204474429915129051 5881039806711644872693577)
          ·
            refine ⟨4410779855033733654520183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5881039806711644872693577 4410779855033733654520183)
            ·
              refine ⟨6616169782550600481780275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410779855033733654520183 6616169782550600481780275)
              ·
                refine ⟨9924254673825900722670413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616169782550600481780275 9924254673825900722670413)
                ·
                  refine ⟨3721595502684712771001405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9924254673825900722670413 3721595502684712771001405)
                  ·
                    refine ⟨1395598313506767289125527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721595502684712771001405 1395598313506767289125527)
                    ·
                      rfl

theorem cell22_4076877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4076877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076877 prefixEnd_4076877 := by exact prefixLift 4076877
  have htrace : WordTrace (prefixWord ++ tailWord_4076877) baseStart_4076877 baseEnd_4076877 := by
    simpa [prefixWord, tailWord_4076877, baseEnd_4076877] using wordTrace_append hprefix tailTrace_4076877
  have hstable : (prefixWord ++ tailWord_4076877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076877).length < 2 ^ (prefixWord ++ tailWord_4076877).sum := by decide
  have hdescent : baseEnd_4076877 < baseStart_4076877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076929 : List Nat := [1, 2, 4, 3, 12]
def baseStart_4076929 : Nat := 118140960795 + 4076929 * 2 ^ 59
def prefixEnd_4076929 : Nat := 4983230072969 + 3 ^ 40 * 4076929 * 2
def baseEnd_4076929 : Nat := 5743276189997763320269

theorem tailTrace_4076929 : CollatzResearch.WordTrace tailWord_4076929 prefixEnd_4076929 5743276189997763320269 := by
  unfold tailWord_4076929
  simp only [CollatzResearch.WordTrace]
  refine ⟨148697816646989991884305841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99131877764659994589537227 148697816646989991884305841)
  ·
    refine ⟨111523362485242493913229381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148697816646989991884305841 111523362485242493913229381)
    ·
      refine ⟨20910630465982967608730509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111523362485242493913229381 20910630465982967608730509)
      ·
        refine ⟨7841486424743612853273941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20910630465982967608730509 7841486424743612853273941)
        ·
          refine ⟨5743276189997763320269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7841486424743612853273941 5743276189997763320269)
          ·
            rfl

theorem cell22_4076929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 12].length) (baseStart_4076929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076929 prefixEnd_4076929 := by exact prefixLift 4076929
  have htrace : WordTrace (prefixWord ++ tailWord_4076929) baseStart_4076929 baseEnd_4076929 := by
    simpa [prefixWord, tailWord_4076929, baseEnd_4076929] using wordTrace_append hprefix tailTrace_4076929
  have hstable : (prefixWord ++ tailWord_4076929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076929).length < 2 ^ (prefixWord ++ tailWord_4076929).sum := by decide
  have hdescent : baseEnd_4076929 < baseStart_4076929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076931 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_4076931 : Nat := 118140960795 + 4076931 * 2 ^ 59
def prefixEnd_4076931 : Nat := 4983230072969 + 3 ^ 40 * 4076931 * 2
def baseEnd_4076931 : Nat := 1395616798810329148275361

theorem tailTrace_4076931 : CollatzResearch.WordTrace tailWord_4076931 prefixEnd_4076931 1395616798810329148275361 := by
  unfold tailWord_4076931
  simp only [CollatzResearch.WordTrace]
  refine ⟨148697889592982746225878647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99131926395321830817252431 148697889592982746225878647)
  ·
    refine ⟨223046834389474119338817971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148697889592982746225878647 223046834389474119338817971)
    ·
      refine ⟨334570251584211179008226957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223046834389474119338817971 334570251584211179008226957)
      ·
        refine ⟨125463844344079192128085109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334570251584211179008226957 125463844344079192128085109)
        ·
          refine ⟨11762235407257424262007979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125463844344079192128085109 11762235407257424262007979)
          ·
            refine ⟨17643353110886136393011969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762235407257424262007979 17643353110886136393011969)
            ·
              refine ⟨13232514833164602294758977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17643353110886136393011969 13232514833164602294758977)
              ·
                refine ⟨9924386124873451721069233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13232514833164602294758977 9924386124873451721069233)
                ·
                  refine ⟨7443289593655088790801925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924386124873451721069233 7443289593655088790801925)
                  ·
                    refine ⟨1395616798810329148275361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443289593655088790801925 1395616798810329148275361)
                    ·
                      rfl

theorem cell22_4076931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_4076931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076931 prefixEnd_4076931 := by exact prefixLift 4076931
  have htrace : WordTrace (prefixWord ++ tailWord_4076931) baseStart_4076931 baseEnd_4076931 := by
    simpa [prefixWord, tailWord_4076931, baseEnd_4076931] using wordTrace_append hprefix tailTrace_4076931
  have hstable : (prefixWord ++ tailWord_4076931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076931).length < 2 ^ (prefixWord ++ tailWord_4076931).sum := by decide
  have hdescent : baseEnd_4076931 < baseStart_4076931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076935 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 4]
def baseStart_4076935 : Nat := 118140960795 + 4076935 * 2 ^ 59
def prefixEnd_4076935 : Nat := 4983230072969 + 3 ^ 40 * 4076935 * 2
def baseEnd_4076935 : Nat := 465206056030691490391783

theorem tailTrace_4076935 : CollatzResearch.WordTrace tailWord_4076935 prefixEnd_4076935 465206056030691490391783 := by
  unfold tailWord_4076935
  simp only [CollatzResearch.WordTrace]
  refine ⟨148698035484968254909024259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99132023656645503272682839 148698035484968254909024259)
  ·
    refine ⟨223047053227452382363536389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148698035484968254909024259 223047053227452382363536389)
    ·
      refine ⟨41821322480147321693163073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223047053227452382363536389 41821322480147321693163073)
      ·
        refine ⟨31365991860110491269872305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41821322480147321693163073 31365991860110491269872305)
        ·
          refine ⟨23524493895082868452404229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31365991860110491269872305 23524493895082868452404229)
          ·
            refine ⟨4410842605328037834825793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23524493895082868452404229 4410842605328037834825793)
            ·
              refine ⟨3308131953996028376119345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410842605328037834825793 3308131953996028376119345)
              ·
                refine ⟨2481098965497021282089509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308131953996028376119345 2481098965497021282089509)
                ·
                  refine ⟨465206056030691490391783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481098965497021282089509 465206056030691490391783)
                  ·
                    rfl

theorem cell22_4076935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 4].length) (baseStart_4076935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4076935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4076935 prefixEnd_4076935 := by exact prefixLift 4076935
  have htrace : WordTrace (prefixWord ++ tailWord_4076935) baseStart_4076935 baseEnd_4076935 := by
    simpa [prefixWord, tailWord_4076935, baseEnd_4076935] using wordTrace_append hprefix tailTrace_4076935
  have hstable : (prefixWord ++ tailWord_4076935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076935).length < 2 ^ (prefixWord ++ tailWord_4076935).sum := by decide
  have hdescent : baseEnd_4076935 < baseStart_4076935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077006 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_4077006 : Nat := 118140960795 + 4077006 * 2 ^ 59
def prefixEnd_4077006 : Nat := 4983230072969 + 3 ^ 40 * 4077006 * 2
def baseEnd_4077006 : Nat := 1395642472843053952650131

theorem tailTrace_4077006 : CollatzResearch.WordTrace tailWord_4077006 prefixEnd_4077006 1395642472843053952650131 := by
  unfold tailWord_4077006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587578133463879254357359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99133750045140689356572581 18587578133463879254357359)
  ·
    refine ⟨27881367200195818881536039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18587578133463879254357359 27881367200195818881536039)
    ·
      refine ⟨41822050800293728322304059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27881367200195818881536039 41822050800293728322304059)
      ·
        refine ⟨62733076200440592483456089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41822050800293728322304059 62733076200440592483456089)
        ·
          refine ⟨47049807150330444362592067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62733076200440592483456089 47049807150330444362592067)
          ·
            refine ⟨70574710725495666543888101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47049807150330444362592067 70574710725495666543888101)
            ·
              refine ⟨13232758261030437476979019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70574710725495666543888101 13232758261030437476979019)
              ·
                refine ⟨19849137391545656215468529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13232758261030437476979019 19849137391545656215468529)
                ·
                  refine ⟨14886853043659242161601397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19849137391545656215468529 14886853043659242161601397)
                  ·
                    refine ⟨1395642472843053952650131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14886853043659242161601397 1395642472843053952650131)
                    ·
                      rfl

theorem cell22_4077006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_4077006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077006 prefixEnd_4077006 := by exact prefixLift 4077006
  have htrace : WordTrace (prefixWord ++ tailWord_4077006) baseStart_4077006 baseEnd_4077006 := by
    simpa [prefixWord, tailWord_4077006, baseEnd_4077006] using wordTrace_append hprefix tailTrace_4077006
  have hstable : (prefixWord ++ tailWord_4077006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077006).length < 2 ^ (prefixWord ++ tailWord_4077006).sum := by decide
  have hdescent : baseEnd_4077006 < baseStart_4077006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077038 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_4077038 : Nat := 118140960795 + 4077038 * 2 ^ 59
def prefixEnd_4077038 : Nat := 4983230072969 + 3 ^ 40 * 4077038 * 2
def baseEnd_4077038 : Nat := 1395653427097016535850033

theorem tailTrace_4077038 : CollatzResearch.WordTrace tailWord_4077038 prefixEnd_4077038 1395653427097016535850033 := by
  unfold tailWord_4077038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587724025449387937502971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99134528135730069000015845 18587724025449387937502971)
  ·
    refine ⟨27881586038174081906254457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18587724025449387937502971 27881586038174081906254457)
    ·
      refine ⟨20911189528630561429690843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27881586038174081906254457 20911189528630561429690843)
      ·
        refine ⟨31366784292945842144536265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20911189528630561429690843 31366784292945842144536265)
        ·
          refine ⟨23525088219709381608402199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31366784292945842144536265 23525088219709381608402199)
          ·
            refine ⟨35287632329564072412603299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23525088219709381608402199 35287632329564072412603299)
            ·
              refine ⟨52931448494346108618904949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35287632329564072412603299 52931448494346108618904949)
              ·
                refine ⟨4962323296344947683022339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52931448494346108618904949 4962323296344947683022339)
                ·
                  refine ⟨7443484944517421524533509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962323296344947683022339 7443484944517421524533509)
                  ·
                    refine ⟨1395653427097016535850033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443484944517421524533509 1395653427097016535850033)
                    ·
                      rfl

theorem cell22_4077038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_4077038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077038 prefixEnd_4077038 := by exact prefixLift 4077038
  have htrace : WordTrace (prefixWord ++ tailWord_4077038) baseStart_4077038 baseEnd_4077038 := by
    simpa [prefixWord, tailWord_4077038, baseEnd_4077038] using wordTrace_append hprefix tailTrace_4077038
  have hstable : (prefixWord ++ tailWord_4077038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077038).length < 2 ^ (prefixWord ++ tailWord_4077038).sum := by decide
  have hdescent : baseEnd_4077038 < baseStart_4077038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077053 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 6]
def baseStart_4077053 : Nat := 118140960795 + 4077053 * 2 ^ 59
def prefixEnd_4077053 : Nat := 4983230072969 + 3 ^ 40 * 4077053 * 2
def baseEnd_4077053 : Nat := 465219520634520498908329

theorem tailTrace_4077053 : CollatzResearch.WordTrace tailWord_4077053 prefixEnd_4077053 465219520634520498908329 := by
  unfold tailWord_4077053
  simp only [CollatzResearch.WordTrace]
  refine ⟨148702339298540761061819813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99134892865693840707879875 148702339298540761061819813)
  ·
    refine ⟨27881688618476392699091215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148702339298540761061819813 27881688618476392699091215)
    ·
      refine ⟨41822532927714589048636823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27881688618476392699091215 41822532927714589048636823)
      ·
        refine ⟨62733799391571883572955235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41822532927714589048636823 62733799391571883572955235)
        ·
          refine ⟨94100699087357825359432853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62733799391571883572955235 94100699087357825359432853)
          ·
            refine ⟨4410970269719898063723415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94100699087357825359432853 4410970269719898063723415)
            ·
              refine ⟨6616455404579847095585123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410970269719898063723415 6616455404579847095585123)
              ·
                refine ⟨9924683106869770643377685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616455404579847095585123 9924683106869770643377685)
                ·
                  refine ⟨465219520634520498908329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9924683106869770643377685 465219520634520498908329)
                  ·
                    rfl

theorem cell22_4077053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_4077053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077053 prefixEnd_4077053 := by exact prefixLift 4077053
  have htrace : WordTrace (prefixWord ++ tailWord_4077053) baseStart_4077053 baseEnd_4077053 := by
    simpa [prefixWord, tailWord_4077053, baseEnd_4077053] using wordTrace_append hprefix tailTrace_4077053
  have hstable : (prefixWord ++ tailWord_4077053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077053).length < 2 ^ (prefixWord ++ tailWord_4077053).sum := by decide
  have hdescent : baseEnd_4077053 < baseStart_4077053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077102 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4077102 : Nat := 118140960795 + 4077102 * 2 ^ 59
def prefixEnd_4077102 : Nat := 4983230072969 + 3 ^ 40 * 4077102 * 2
def baseEnd_4077102 : Nat := 1395675335604941702249837

theorem tailTrace_4077102 : CollatzResearch.WordTrace tailWord_4077102 prefixEnd_4077102 1395675335604941702249837 := by
  unfold tailWord_4077102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588015809420405303794195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99136084316908828286902373 18588015809420405303794195)
  ·
    refine ⟨27882023714130607955691293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18588015809420405303794195 27882023714130607955691293)
    ·
      refine ⟨10455758892798977983384235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27882023714130607955691293 10455758892798977983384235)
      ·
        refine ⟨15683638339198466975076353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455758892798977983384235 15683638339198466975076353)
        ·
          refine ⟨11762728754398850231307265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15683638339198466975076353 11762728754398850231307265)
          ·
            refine ⟨8822046565799137673480449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11762728754398850231307265 8822046565799137673480449)
            ·
              refine ⟨6616534924349353255110337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8822046565799137673480449 6616534924349353255110337)
              ·
                refine ⟨4962401193262014941332753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616534924349353255110337 4962401193262014941332753)
                ·
                  refine ⟨3721800894946511205999565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962401193262014941332753 3721800894946511205999565)
                  ·
                    refine ⟨1395675335604941702249837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721800894946511205999565 1395675335604941702249837)
                    ·
                      rfl

theorem cell22_4077102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4077102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077102 prefixEnd_4077102 := by exact prefixLift 4077102
  have htrace : WordTrace (prefixWord ++ tailWord_4077102) baseStart_4077102 baseEnd_4077102 := by
    simpa [prefixWord, tailWord_4077102, baseEnd_4077102] using wordTrace_append hprefix tailTrace_4077102
  have hstable : (prefixWord ++ tailWord_4077102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077102).length < 2 ^ (prefixWord ++ tailWord_4077102).sum := by decide
  have hdescent : baseEnd_4077102 < baseStart_4077102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077111 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4077111 : Nat := 118140960795 + 4077111 * 2 ^ 59
def prefixEnd_4077111 : Nat := 4983230072969 + 3 ^ 40 * 4077111 * 2
def baseEnd_4077111 : Nat := 1395678416488868678774809

theorem tailTrace_4077111 : CollatzResearch.WordTrace tailWord_4077111 prefixEnd_4077111 1395678416488868678774809 := by
  unfold tailWord_4077111
  simp only [CollatzResearch.WordTrace]
  refine ⟨148704454732330636967431187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99136303154887091311620791 148704454732330636967431187)
  ·
    refine ⟨223056682098495955451146781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148704454732330636967431187 223056682098495955451146781)
    ·
      refine ⟨83646255786935983294180043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223056682098495955451146781 83646255786935983294180043)
      ·
        refine ⟨125469383680403974941270065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83646255786935983294180043 125469383680403974941270065)
        ·
          refine ⟨94102037760302981205952549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125469383680403974941270065 94102037760302981205952549)
          ·
            refine ⟨17644132080056808976116103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94102037760302981205952549 17644132080056808976116103)
            ·
              refine ⟨26466198120085213464174155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644132080056808976116103 26466198120085213464174155)
              ·
                refine ⟨39699297180127820196261233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26466198120085213464174155 39699297180127820196261233)
                ·
                  refine ⟨29774472885095865147195925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39699297180127820196261233 29774472885095865147195925)
                  ·
                    refine ⟨1395678416488868678774809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29774472885095865147195925 1395678416488868678774809)
                    ·
                      rfl

theorem cell22_4077111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4077111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077111 prefixEnd_4077111 := by exact prefixLift 4077111
  have htrace : WordTrace (prefixWord ++ tailWord_4077111) baseStart_4077111 baseEnd_4077111 := by
    simpa [prefixWord, tailWord_4077111, baseEnd_4077111] using wordTrace_append hprefix tailTrace_4077111
  have hstable : (prefixWord ++ tailWord_4077111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077111).length < 2 ^ (prefixWord ++ tailWord_4077111).sum := by decide
  have hdescent : baseEnd_4077111 < baseStart_4077111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077141 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_4077141 : Nat := 118140960795 + 4077141 * 2 ^ 59
def prefixEnd_4077141 : Nat := 4983230072969 + 3 ^ 40 * 4077141 * 2
def baseEnd_4077141 : Nat := 1395688686101958600524717

theorem tailTrace_4077141 : CollatzResearch.WordTrace tailWord_4077141 prefixEnd_4077141 1395688686101958600524717 := by
  unfold tailWord_4077141
  simp only [CollatzResearch.WordTrace]
  refine ⟨148705548922221952091023277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99137032614814634727348851 148705548922221952091023277)
  ·
    refine ⟨55764580845833232034133729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148705548922221952091023277 55764580845833232034133729)
    ·
      refine ⟨41823435634374924025600297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55764580845833232034133729 41823435634374924025600297)
      ·
        refine ⟨31367576725781193019200223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41823435634374924025600297 31367576725781193019200223)
        ·
          refine ⟨47051365088671789528800335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31367576725781193019200223 47051365088671789528800335)
          ·
            refine ⟨70577047633007684293200503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47051365088671789528800335 70577047633007684293200503)
            ·
              refine ⟨105865571449511526439800755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70577047633007684293200503 105865571449511526439800755)
              ·
                refine ⟨158798357174267289659701133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105865571449511526439800755 158798357174267289659701133)
                ·
                  refine ⟨59549383940350233622387925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158798357174267289659701133 59549383940350233622387925)
                  ·
                    refine ⟨1395688686101958600524717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59549383940350233622387925 1395688686101958600524717)
                    ·
                      rfl

theorem cell22_4077141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_4077141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077141 prefixEnd_4077141 := by exact prefixLift 4077141
  have htrace : WordTrace (prefixWord ++ tailWord_4077141) baseStart_4077141 baseEnd_4077141 := by
    simpa [prefixWord, tailWord_4077141, baseEnd_4077141] using wordTrace_append hprefix tailTrace_4077141
  have hstable : (prefixWord ++ tailWord_4077141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077141).length < 2 ^ (prefixWord ++ tailWord_4077141).sum := by decide
  have hdescent : baseEnd_4077141 < baseStart_4077141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077160 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_4077160 : Nat := 118140960795 + 4077160 * 2 ^ 59
def prefixEnd_4077160 : Nat := 4983230072969 + 3 ^ 40 * 4077160 * 2
def baseEnd_4077160 : Nat := 465231730063416294766553

theorem tailTrace_4077160 : CollatzResearch.WordTrace tailWord_4077160 prefixEnd_4077160 465231730063416294766553 := by
  unfold tailWord_4077160
  simp only [CollatzResearch.WordTrace]
  refine ⟨74353120954576559167982467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99137494606102078890643289 74353120954576559167982467)
  ·
    refine ⟨111529681431864838751973701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74353120954576559167982467 111529681431864838751973701)
    ·
      refine ⟨20911815268474657265995069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111529681431864838751973701 20911815268474657265995069)
      ·
        refine ⟨7841930725677996474748151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20911815268474657265995069 7841930725677996474748151)
        ·
          refine ⟨11762896088516994712122227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841930725677996474748151 11762896088516994712122227)
          ·
            refine ⟨17644344132775492068183341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762896088516994712122227 17644344132775492068183341)
            ·
              refine ⟨6616629049790809525568753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17644344132775492068183341 6616629049790809525568753)
              ·
                refine ⟨4962471787343107144176565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616629049790809525568753 4962471787343107144176565)
                ·
                  refine ⟨465231730063416294766553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4962471787343107144176565 465231730063416294766553)
                  ·
                    rfl

theorem cell22_4077160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_4077160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077160 prefixEnd_4077160 := by exact prefixLift 4077160
  have htrace : WordTrace (prefixWord ++ tailWord_4077160) baseStart_4077160 baseEnd_4077160 := by
    simpa [prefixWord, tailWord_4077160, baseEnd_4077160] using wordTrace_append hprefix tailTrace_4077160
  have hstable : (prefixWord ++ tailWord_4077160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077160).length < 2 ^ (prefixWord ++ tailWord_4077160).sum := by decide
  have hdescent : baseEnd_4077160 < baseStart_4077160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077220 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_4077220 : Nat := 118140960795 + 4077220 * 2 ^ 59
def prefixEnd_4077220 : Nat := 4983230072969 + 3 ^ 40 * 4077220 * 2
def baseEnd_4077220 : Nat := 1395715729416428727799475

theorem tailTrace_4077220 : CollatzResearch.WordTrace tailWord_4077220 prefixEnd_4077220 1395715729416428727799475 := by
  unfold tailWord_4077220
  simp only [CollatzResearch.WordTrace]
  refine ⟨74354215144467874291574557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99138953525957165722099409 74354215144467874291574557)
  ·
    refine ⟨27882830679175452859340459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74354215144467874291574557 27882830679175452859340459)
    ·
      refine ⟨41824246018763179289010689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27882830679175452859340459 41824246018763179289010689)
      ·
        refine ⟨31368184514072384466758017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41824246018763179289010689 31368184514072384466758017)
        ·
          refine ⟨23526138385554288350068513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31368184514072384466758017 23526138385554288350068513)
          ·
            refine ⟨17644603789165716262551385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23526138385554288350068513 17644603789165716262551385)
            ·
              refine ⟨13233452841874287196913539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17644603789165716262551385 13233452841874287196913539)
              ·
                refine ⟨19850179262811430795370309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13233452841874287196913539 19850179262811430795370309)
                ·
                  refine ⟨3721908611777143274131933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19850179262811430795370309 3721908611777143274131933)
                  ·
                    refine ⟨1395715729416428727799475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721908611777143274131933 1395715729416428727799475)
                    ·
                      rfl

theorem cell22_4077220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_4077220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077220 prefixEnd_4077220 := by exact prefixLift 4077220
  have htrace : WordTrace (prefixWord ++ tailWord_4077220) baseStart_4077220 baseEnd_4077220 := by
    simpa [prefixWord, tailWord_4077220, baseEnd_4077220] using wordTrace_append hprefix tailTrace_4077220
  have hstable : (prefixWord ++ tailWord_4077220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077220).length < 2 ^ (prefixWord ++ tailWord_4077220).sum := by decide
  have hdescent : baseEnd_4077220 < baseStart_4077220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077254 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4077254 : Nat := 118140960795 + 4077254 * 2 ^ 59
def prefixEnd_4077254 : Nat := 4983230072969 + 3 ^ 40 * 4077254 * 2
def baseEnd_4077254 : Nat := 1395727368311263972449371

theorem tailTrace_4077254 : CollatzResearch.WordTrace tailWord_4077254 prefixEnd_4077254 1395727368311263972449371 := by
  unfold tailWord_4077254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647177199087892887183963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99139780247208381593257877 4647177199087892887183963)
  ·
    refine ⟨6970765798631839330775945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4647177199087892887183963 6970765798631839330775945)
    ·
      refine ⟨5228074348973879498081959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6970765798631839330775945 5228074348973879498081959)
      ·
        refine ⟨7842111523460819247122939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228074348973879498081959 7842111523460819247122939)
        ·
          refine ⟨11763167285191228870684409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842111523460819247122939 11763167285191228870684409)
          ·
            refine ⟨8822375463893421653013307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11763167285191228870684409 8822375463893421653013307)
            ·
              refine ⟨13233563195840132479519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822375463893421653013307 13233563195840132479519961)
              ·
                refine ⟨9925172396880099359639971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13233563195840132479519961 9925172396880099359639971)
                ·
                  refine ⟨14887758595320149039459957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925172396880099359639971 14887758595320149039459957)
                  ·
                    refine ⟨1395727368311263972449371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14887758595320149039459957 1395727368311263972449371)
                    ·
                      rfl

theorem cell22_4077254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4077254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077254 prefixEnd_4077254 := by exact prefixLift 4077254
  have htrace : WordTrace (prefixWord ++ tailWord_4077254) baseStart_4077254 baseEnd_4077254 := by
    simpa [prefixWord, tailWord_4077254, baseEnd_4077254] using wordTrace_append hprefix tailTrace_4077254
  have hstable : (prefixWord ++ tailWord_4077254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077254).length < 2 ^ (prefixWord ++ tailWord_4077254).sum := by decide
  have hdescent : baseEnd_4077254 < baseStart_4077254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077340 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_4077340 : Nat := 118140960795 + 4077340 * 2 ^ 59
def prefixEnd_4077340 : Nat := 4983230072969 + 3 ^ 40 * 4077340 * 2
def baseEnd_4077340 : Nat := 465252269289596138266369

theorem tailTrace_4077340 : CollatzResearch.WordTrace tailWord_4077340 prefixEnd_4077340 465252269289596138266369 := by
  unfold tailWord_4077340
  simp only [CollatzResearch.WordTrace]
  refine ⟨74356403524250504538758737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99141871365667339385011649 74356403524250504538758737)
  ·
    refine ⟨55767302643187878404069053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74356403524250504538758737 55767302643187878404069053)
    ·
      refine ⟨20912738491195454401525895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55767302643187878404069053 20912738491195454401525895)
      ·
        refine ⟨31369107736793181602288843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20912738491195454401525895 31369107736793181602288843)
        ·
          refine ⟨47053661605189772403433265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31369107736793181602288843 47053661605189772403433265)
          ·
            refine ⟨35290246203892329302574949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47053661605189772403433265 35290246203892329302574949)
            ·
              refine ⟨6616921163229811744232803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35290246203892329302574949 6616921163229811744232803)
              ·
                refine ⟨9925381744844717616349205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616921163229811744232803 9925381744844717616349205)
                ·
                  refine ⟨465252269289596138266369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9925381744844717616349205 465252269289596138266369)
                  ·
                    rfl

theorem cell22_4077340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_4077340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077340 prefixEnd_4077340 := by exact prefixLift 4077340
  have htrace : WordTrace (prefixWord ++ tailWord_4077340) baseStart_4077340 baseEnd_4077340 := by
    simpa [prefixWord, tailWord_4077340, baseEnd_4077340] using wordTrace_append hprefix tailTrace_4077340
  have hstable : (prefixWord ++ tailWord_4077340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077340).length < 2 ^ (prefixWord ++ tailWord_4077340).sum := by decide
  have hdescent : baseEnd_4077340 < baseStart_4077340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077370 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_4077370 : Nat := 118140960795 + 4077370 * 2 ^ 59
def prefixEnd_4077370 : Nat := 4983230072969 + 3 ^ 40 * 4077370 * 2
def baseEnd_4077370 : Nat := 1395767077481878336549015

theorem tailTrace_4077370 : CollatzResearch.WordTrace tailWord_4077370 prefixEnd_4077370 1395767077481878336549015 := by
  unfold tailWord_4077370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178475309598081050277391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99142600825594882800739709 37178475309598081050277391)
  ·
    refine ⟨55767712964397121575416087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37178475309598081050277391 55767712964397121575416087)
    ·
      refine ⟨83651569446595682363124131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55767712964397121575416087 83651569446595682363124131)
      ·
        refine ⟨125477354169893523544686197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83651569446595682363124131 125477354169893523544686197)
        ·
          refine ⟨11763501953427517832314331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125477354169893523544686197 11763501953427517832314331)
          ·
            refine ⟨17645252930141276748471497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763501953427517832314331 17645252930141276748471497)
            ·
              refine ⟨13233939697605957561353623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17645252930141276748471497 13233939697605957561353623)
              ·
                refine ⟨19850909546408936342030435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13233939697605957561353623 19850909546408936342030435)
                ·
                  refine ⟨29776364319613404513045653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19850909546408936342030435 29776364319613404513045653)
                  ·
                    refine ⟨1395767077481878336549015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29776364319613404513045653 1395767077481878336549015)
                    ·
                      rfl

theorem cell22_4077370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_4077370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077370 prefixEnd_4077370 := by exact prefixLift 4077370
  have htrace : WordTrace (prefixWord ++ tailWord_4077370) baseStart_4077370 baseEnd_4077370 := by
    simpa [prefixWord, tailWord_4077370, baseEnd_4077370] using wordTrace_append hprefix tailTrace_4077370
  have hstable : (prefixWord ++ tailWord_4077370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077370).length < 2 ^ (prefixWord ++ tailWord_4077370).sum := by decide
  have hdescent : baseEnd_4077370 < baseStart_4077370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077374 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_4077374 : Nat := 118140960795 + 4077374 * 2 ^ 59
def prefixEnd_4077374 : Nat := 4983230072969 + 3 ^ 40 * 4077374 * 2
def baseEnd_4077374 : Nat := 465256148921207886483001

theorem tailTrace_4077374 : CollatzResearch.WordTrace tailWord_4077374 prefixEnd_4077374 465256148921207886483001 := by
  unfold tailWord_4077374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18589255891297229110531897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99142698086918555256170117 18589255891297229110531897)
  ·
    refine ⟨13941941918472921832898923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18589255891297229110531897 13941941918472921832898923)
    ·
      refine ⟨20912912877709382749348385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13941941918472921832898923 20912912877709382749348385)
      ·
        refine ⟨15684684658282037062011289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20912912877709382749348385 15684684658282037062011289)
        ·
          refine ⟨11763513493711527796508467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15684684658282037062011289 11763513493711527796508467)
          ·
            refine ⟨17645270240567291694762701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763513493711527796508467 17645270240567291694762701)
            ·
              refine ⟨6616976340212734385536013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17645270240567291694762701 6616976340212734385536013)
              ·
                refine ⟨2481366127579775394576005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6616976340212734385536013 2481366127579775394576005)
                ·
                  refine ⟨465256148921207886483001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481366127579775394576005 465256148921207886483001)
                  ·
                    rfl

theorem cell22_4077374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_4077374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077374 prefixEnd_4077374 := by exact prefixLift 4077374
  have htrace : WordTrace (prefixWord ++ tailWord_4077374) baseStart_4077374 baseEnd_4077374 := by
    simpa [prefixWord, tailWord_4077374, baseEnd_4077374] using wordTrace_append hprefix tailTrace_4077374
  have hstable : (prefixWord ++ tailWord_4077374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077374).length < 2 ^ (prefixWord ++ tailWord_4077374).sum := by decide
  have hdescent : baseEnd_4077374 < baseStart_4077374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077389 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4077389 : Nat := 118140960795 + 4077389 * 2 ^ 59
def prefixEnd_4077389 : Nat := 4983230072969 + 3 ^ 40 * 4077389 * 2
def baseEnd_4077389 : Nat := 1395773581570168620323957

theorem tailTrace_4077389 : CollatzResearch.WordTrace tailWord_4077389 prefixEnd_4077389 1395773581570168620323957 := by
  unfold tailWord_4077389
  simp only [CollatzResearch.WordTrace]
  refine ⟨148714594225323490446051221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99143062816882326964034147 148714594225323490446051221)
  ·
    refine ⟨6970996604312038614658651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148714594225323490446051221 6970996604312038614658651)
    ·
      refine ⟨10456494906468057921987977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970996604312038614658651 10456494906468057921987977)
      ·
        refine ⟨7842371179851043441490983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10456494906468057921987977 7842371179851043441490983)
        ·
          refine ⟨11763556769776565162236475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842371179851043441490983 11763556769776565162236475)
          ·
            refine ⟨17645335154664847743354713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763556769776565162236475 17645335154664847743354713)
            ·
              refine ⟨13234001365998635807516035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17645335154664847743354713 13234001365998635807516035)
              ·
                refine ⟨19851002048997953711274053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234001365998635807516035 19851002048997953711274053)
                ·
                  refine ⟨3722062884187116320863885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19851002048997953711274053 3722062884187116320863885)
                  ·
                    refine ⟨1395773581570168620323957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722062884187116320863885 1395773581570168620323957)
                    ·
                      rfl

theorem cell22_4077389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4077389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077389 prefixEnd_4077389 := by exact prefixLift 4077389
  have htrace : WordTrace (prefixWord ++ tailWord_4077389) baseStart_4077389 baseEnd_4077389 := by
    simpa [prefixWord, tailWord_4077389, baseEnd_4077389] using wordTrace_append hprefix tailTrace_4077389
  have hstable : (prefixWord ++ tailWord_4077389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077389).length < 2 ^ (prefixWord ++ tailWord_4077389).sum := by decide
  have hdescent : baseEnd_4077389 < baseStart_4077389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077445 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_4077445 : Nat := 118140960795 + 4077445 * 2 ^ 59
def prefixEnd_4077445 : Nat := 4983230072969 + 3 ^ 40 * 4077445 * 2
def baseEnd_4077445 : Nat := 1395792751514603140923785

theorem tailTrace_4077445 : CollatzResearch.WordTrace tailWord_4077445 prefixEnd_4077445 1395792751514603140923785 := by
  unfold tailWord_4077445
  simp only [CollatzResearch.WordTrace]
  refine ⟨148716636713120612010089789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99144424475413741340059859 148716636713120612010089789)
  ·
    refine ⟨55768738767420229503783671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148716636713120612010089789 55768738767420229503783671)
    ·
      refine ⟨83653108151130344255675507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55768738767420229503783671 83653108151130344255675507)
      ·
        refine ⟨125479662226695516383513261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83653108151130344255675507 125479662226695516383513261)
        ·
          refine ⟨47054873335010818643817473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125479662226695516383513261 47054873335010818643817473)
          ·
            refine ⟨35291155001258113982863105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47054873335010818643817473 35291155001258113982863105)
            ·
              refine ⟨26468366250943585487147329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35291155001258113982863105 26468366250943585487147329)
              ·
                refine ⟨19851274688207689115360497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26468366250943585487147329 19851274688207689115360497)
                ·
                  refine ⟨14888456016155766836520373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19851274688207689115360497 14888456016155766836520373)
                  ·
                    refine ⟨1395792751514603140923785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14888456016155766836520373 1395792751514603140923785)
                    ·
                      rfl

theorem cell22_4077445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_4077445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077445 prefixEnd_4077445 := by exact prefixLift 4077445
  have htrace : WordTrace (prefixWord ++ tailWord_4077445) baseStart_4077445 baseEnd_4077445 := by
    simpa [prefixWord, tailWord_4077445, baseEnd_4077445] using wordTrace_append hprefix tailTrace_4077445
  have hstable : (prefixWord ++ tailWord_4077445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077445).length < 2 ^ (prefixWord ++ tailWord_4077445).sum := by decide
  have hdescent : baseEnd_4077445 < baseStart_4077445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077537 : List Nat := [1, 2, 3, 1, 2, 1, 6, 6]
def baseStart_4077537 : Nat := 118140960795 + 4077537 * 2 ^ 59
def prefixEnd_4077537 : Nat := 4983230072969 + 3 ^ 40 * 4077537 * 2
def baseEnd_4077537 : Nat := 155091582777193951958167

theorem tailTrace_4077537 : CollatzResearch.WordTrace tailWord_4077537 prefixEnd_4077537 155091582777193951958167 := by
  unfold tailWord_4077537
  simp only [CollatzResearch.WordTrace]
  refine ⟨148719992228787311722438865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99146661485858207814959243 148719992228787311722438865)
  ·
    refine ⟨111539994171590483791829149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148719992228787311722438865 111539994171590483791829149)
    ·
      refine ⟨41827497814346431421935931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111539994171590483791829149 41827497814346431421935931)
      ·
        refine ⟨62741246721519647132903897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41827497814346431421935931 62741246721519647132903897)
        ·
          refine ⟨47055935041139735349677923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62741246721519647132903897 47055935041139735349677923)
          ·
            refine ⟨70583902561709603024516885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47055935041139735349677923 70583902561709603024516885)
            ·
              refine ⟨3308620432580137641774229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70583902561709603024516885 3308620432580137641774229)
              ·
                refine ⟨155091582777193951958167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3308620432580137641774229 155091582777193951958167)
                ·
                  rfl

theorem cell22_4077537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 6].length) (baseStart_4077537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077537 prefixEnd_4077537 := by exact prefixLift 4077537
  have htrace : WordTrace (prefixWord ++ tailWord_4077537) baseStart_4077537 baseEnd_4077537 := by
    simpa [prefixWord, tailWord_4077537, baseEnd_4077537] using wordTrace_append hprefix tailTrace_4077537
  have hstable : (prefixWord ++ tailWord_4077537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077537).length < 2 ^ (prefixWord ++ tailWord_4077537).sum := by decide
  have hdescent : baseEnd_4077537 < baseStart_4077537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077543 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 4]
def baseStart_4077543 : Nat := 118140960795 + 4077543 * 2 ^ 59
def prefixEnd_4077543 : Nat := 4983230072969 + 3 ^ 40 * 4077543 * 2
def baseEnd_4077543 : Nat := 465275432972454517324495

theorem tailTrace_4077543 : CollatzResearch.WordTrace tailWord_4077543 prefixEnd_4077543 465275432972454517324495 := by
  unfold tailWord_4077543
  simp only [CollatzResearch.WordTrace]
  refine ⟨148720211066765574747157283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99146807377843716498104855 148720211066765574747157283)
  ·
    refine ⟨223080316600148362120735925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148720211066765574747157283 223080316600148362120735925)
    ·
      refine ⟨20913779681263908948818993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223080316600148362120735925 20913779681263908948818993)
      ·
        refine ⟨15685334760947931711614245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20913779681263908948818993 15685334760947931711614245)
        ·
          refine ⟨2941000267677737195927671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15685334760947931711614245 2941000267677737195927671)
          ·
            refine ⟨4411500401516605793891507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941000267677737195927671 4411500401516605793891507)
            ·
              refine ⟨6617250602274908690837261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411500401516605793891507 6617250602274908690837261)
              ·
                refine ⟨2481468975853090759063973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6617250602274908690837261 2481468975853090759063973)
                ·
                  refine ⟨465275432972454517324495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481468975853090759063973 465275432972454517324495)
                  ·
                    rfl

theorem cell22_4077543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 4].length) (baseStart_4077543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077543 prefixEnd_4077543 := by exact prefixLift 4077543
  have htrace : WordTrace (prefixWord ++ tailWord_4077543) baseStart_4077543 baseEnd_4077543 := by
    simpa [prefixWord, tailWord_4077543, baseEnd_4077543] using wordTrace_append hprefix tailTrace_4077543
  have hstable : (prefixWord ++ tailWord_4077543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077543).length < 2 ^ (prefixWord ++ tailWord_4077543).sum := by decide
  have hdescent : baseEnd_4077543 < baseStart_4077543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077552 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_4077552 : Nat := 118140960795 + 4077552 * 2 ^ 59
def prefixEnd_4077552 : Nat := 4983230072969 + 3 ^ 40 * 4077552 * 2
def baseEnd_4077552 : Nat := 1395829379801290528498457

theorem tailTrace_4077552 : CollatzResearch.WordTrace tailWord_4077552 prefixEnd_4077552 1395829379801290528498457 := by
  unfold tailWord_4077552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74360269661866484642117455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99147026215821979522823273 74360269661866484642117455)
  ·
    refine ⟨111540404492799726963176183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74360269661866484642117455 111540404492799726963176183)
    ·
      refine ⟨167310606739199590444764275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111540404492799726963176183 167310606739199590444764275)
      ·
        refine ⟨250965910108799385667146413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167310606739199590444764275 250965910108799385667146413)
        ·
          refine ⟨94112216290799769625179905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250965910108799385667146413 94112216290799769625179905)
          ·
            refine ⟨70584162218099827218884929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94112216290799769625179905 70584162218099827218884929)
            ·
              refine ⟨52938121663574870414163697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70584162218099827218884929 52938121663574870414163697)
              ·
                refine ⟨39703591247681152810622773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52938121663574870414163697 39703591247681152810622773)
                ·
                  refine ⟨3722211679470108075995885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39703591247681152810622773 3722211679470108075995885)
                  ·
                    refine ⟨1395829379801290528498457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722211679470108075995885 1395829379801290528498457)
                    ·
                      rfl

theorem cell22_4077552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_4077552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077552 prefixEnd_4077552 := by exact prefixLift 4077552
  have htrace : WordTrace (prefixWord ++ tailWord_4077552) baseStart_4077552 baseEnd_4077552 := by
    simpa [prefixWord, tailWord_4077552, baseEnd_4077552] using wordTrace_append hprefix tailTrace_4077552
  have hstable : (prefixWord ++ tailWord_4077552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077552).length < 2 ^ (prefixWord ++ tailWord_4077552).sum := by decide
  have hdescent : baseEnd_4077552 < baseStart_4077552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077620 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4077620 : Nat := 118140960795 + 4077620 * 2 ^ 59
def prefixEnd_4077620 : Nat := 4983230072969 + 3 ^ 40 * 4077620 * 2
def baseEnd_4077620 : Nat := 1395852657590961017798249

theorem tailTrace_4077620 : CollatzResearch.WordTrace tailWord_4077620 prefixEnd_4077620 1395852657590961017798249 := by
  unfold tailWord_4077620
  simp only [CollatzResearch.WordTrace]
  refine ⟨74361509743743308448855157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99148679658324411265140209 74361509743743308448855157)
  ·
    refine ⟨6971391538475935167080171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74361509743743308448855157 6971391538475935167080171)
    ·
      refine ⟨10457087307713902750620257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6971391538475935167080171 10457087307713902750620257)
      ·
        refine ⟨7842815480785427062965193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10457087307713902750620257 7842815480785427062965193)
        ·
          refine ⟨5882111610589070297223895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842815480785427062965193 5882111610589070297223895)
          ·
            refine ⟨8823167415883605445835843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882111610589070297223895 8823167415883605445835843)
            ·
              refine ⟨13234751123825408168753765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8823167415883605445835843 13234751123825408168753765)
              ·
                refine ⟨2481515835717264031641331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13234751123825408168753765 2481515835717264031641331)
                ·
                  refine ⟨3722273753575896047461997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481515835717264031641331 3722273753575896047461997)
                  ·
                    refine ⟨1395852657590961017798249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722273753575896047461997 1395852657590961017798249)
                    ·
                      rfl

theorem cell22_4077620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4077620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077620 prefixEnd_4077620 := by exact prefixLift 4077620
  have htrace : WordTrace (prefixWord ++ tailWord_4077620) baseStart_4077620 baseEnd_4077620 := by
    simpa [prefixWord, tailWord_4077620, baseEnd_4077620] using wordTrace_append hprefix tailTrace_4077620
  have hstable : (prefixWord ++ tailWord_4077620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077620).length < 2 ^ (prefixWord ++ tailWord_4077620).sum := by decide
  have hdescent : baseEnd_4077620 < baseStart_4077620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077657 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_4077657 : Nat := 118140960795 + 4077657 * 2 ^ 59
def prefixEnd_4077657 : Nat := 4983230072969 + 3 ^ 40 * 4077657 * 2
def baseEnd_4077657 : Nat := 1395865323447105254623135

theorem tailTrace_4077657 : CollatzResearch.WordTrace tailWord_4077657 prefixEnd_4077657 1395865323447105254623135 := by
  unfold tailWord_4077657
  simp only [CollatzResearch.WordTrace]
  refine ⟨148724368988352572216807225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99149579325568381477871483 148724368988352572216807225)
  ·
    refine ⟨111543276741264429162605419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148724368988352572216807225 111543276741264429162605419)
    ·
      refine ⟨167314915111896643743908129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111543276741264429162605419 167314915111896643743908129)
      ·
        refine ⟨125486186333922482807931097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167314915111896643743908129 125486186333922482807931097)
        ·
          refine ⟨94114639750441862105948323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125486186333922482807931097 94114639750441862105948323)
          ·
            refine ⟨141171959625662793158922485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94114639750441862105948323 141171959625662793158922485)
            ·
              refine ⟨13234871214905886858648983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141171959625662793158922485 13234871214905886858648983)
              ·
                refine ⟨19852306822358830287973475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234871214905886858648983 19852306822358830287973475)
                ·
                  refine ⟨29778460233538245431960213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19852306822358830287973475 29778460233538245431960213)
                  ·
                    refine ⟨1395865323447105254623135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29778460233538245431960213 1395865323447105254623135)
                    ·
                      rfl

theorem cell22_4077657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_4077657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077657 prefixEnd_4077657 := by exact prefixLift 4077657
  have htrace : WordTrace (prefixWord ++ tailWord_4077657) baseStart_4077657 baseEnd_4077657 := by
    simpa [prefixWord, tailWord_4077657, baseEnd_4077657] using wordTrace_append hprefix tailTrace_4077657
  have hstable : (prefixWord ++ tailWord_4077657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077657).length < 2 ^ (prefixWord ++ tailWord_4077657).sum := by decide
  have hdescent : baseEnd_4077657 < baseStart_4077657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077676 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_4077676 : Nat := 118140960795 + 4077676 * 2 ^ 59
def prefixEnd_4077676 : Nat := 4983230072969 + 3 ^ 40 * 4077676 * 2
def baseEnd_4077676 : Nat := 1395871827535395538398077

theorem tailTrace_4077676 : CollatzResearch.WordTrace tailWord_4077676 prefixEnd_4077676 1395871827535395538398077 := by
  unfold tailWord_4077676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74362530987641869230874441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99150041316855825641165921 74362530987641869230874441)
  ·
    refine ⟨55771898240731401923155831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74362530987641869230874441 55771898240731401923155831)
    ·
      refine ⟨83657847361097102884733747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55771898240731401923155831 83657847361097102884733747)
      ·
        refine ⟨125486771041645654327100621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83657847361097102884733747 125486771041645654327100621)
        ·
          refine ⟨47057539140617120372662733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125486771041645654327100621 47057539140617120372662733)
          ·
            refine ⟨17646577177731420139748525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47057539140617120372662733 17646577177731420139748525)
            ·
              refine ⟨6617466441649282552405697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17646577177731420139748525 6617466441649282552405697)
              ·
                refine ⟨4963099831236961914304273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617466441649282552405697 4963099831236961914304273)
                ·
                  refine ⟨3722324873427721435728205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963099831236961914304273 3722324873427721435728205)
                  ·
                    refine ⟨1395871827535395538398077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722324873427721435728205 1395871827535395538398077)
                    ·
                      rfl

theorem cell22_4077676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_4077676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077676 prefixEnd_4077676 := by exact prefixLift 4077676
  have htrace : WordTrace (prefixWord ++ tailWord_4077676) baseStart_4077676 baseEnd_4077676 := by
    simpa [prefixWord, tailWord_4077676, baseEnd_4077676] using wordTrace_append hprefix tailTrace_4077676
  have hstable : (prefixWord ++ tailWord_4077676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077676).length < 2 ^ (prefixWord ++ tailWord_4077676).sum := by decide
  have hdescent : baseEnd_4077676 < baseStart_4077676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077693 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_4077693 : Nat := 118140960795 + 4077693 * 2 ^ 59
def prefixEnd_4077693 : Nat := 4983230072969 + 3 ^ 40 * 4077693 * 2
def baseEnd_4077693 : Nat := 1395877646982813160723025

theorem tailTrace_4077693 : CollatzResearch.WordTrace tailWord_4077693 prefixEnd_4077693 1395877646982813160723025 := by
  unfold tailWord_4077693
  simp only [CollatzResearch.WordTrace]
  refine ⟨148725682016222150365117733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99150454677481433576745155 148725682016222150365117733)
  ·
    refine ⟨27886065378041653193459575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148725682016222150365117733 27886065378041653193459575)
    ·
      refine ⟨41829098067062479790189363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27886065378041653193459575 41829098067062479790189363)
      ·
        refine ⟨62743647100593719685284045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41829098067062479790189363 62743647100593719685284045)
        ·
          refine ⟨23528867662722644881981517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62743647100593719685284045 23528867662722644881981517)
          ·
            refine ⟨8823325373520991830743069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23528867662722644881981517 8823325373520991830743069)
            ·
              refine ⟨3308747015070371936528651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8823325373520991830743069 3308747015070371936528651)
              ·
                refine ⟨4963120522605557904792977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308747015070371936528651 4963120522605557904792977)
                ·
                  refine ⟨3722340391954168428594733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963120522605557904792977 3722340391954168428594733)
                  ·
                    refine ⟨1395877646982813160723025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722340391954168428594733 1395877646982813160723025)
                    ·
                      rfl

theorem cell22_4077693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_4077693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077693 prefixEnd_4077693 := by exact prefixLift 4077693
  have htrace : WordTrace (prefixWord ++ tailWord_4077693) baseStart_4077693 baseEnd_4077693 := by
    simpa [prefixWord, tailWord_4077693, baseEnd_4077693] using wordTrace_append hprefix tailTrace_4077693
  have hstable : (prefixWord ++ tailWord_4077693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077693).length < 2 ^ (prefixWord ++ tailWord_4077693).sum := by decide
  have hdescent : baseEnd_4077693 < baseStart_4077693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077706 : List Nat := [3, 1, 2, 3, 1, 4, 2, 6]
def baseStart_4077706 : Nat := 118140960795 + 4077706 * 2 ^ 59
def prefixEnd_4077706 : Nat := 4983230072969 + 3 ^ 40 * 4077706 * 2
def baseEnd_4077706 : Nat := 155098010794276162238665

theorem tailTrace_4077706 : CollatzResearch.WordTrace tailWord_4077706 prefixEnd_4077706 155098010794276162238665 := by
  unfold tailWord_4077706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37181539041293763396335243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99150770776783369056893981 37181539041293763396335243)
  ·
    refine ⟨55772308561940645094502865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37181539041293763396335243 55772308561940645094502865)
    ·
      refine ⟨41829231421455483820877149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55772308561940645094502865 41829231421455483820877149)
      ·
        refine ⟨15685961783045806432828931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41829231421455483820877149 15685961783045806432828931)
        ·
          refine ⟨23528942674568709649243397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15685961783045806432828931 23528942674568709649243397)
          ·
            refine ⟨4411676751481633059233137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23528942674568709649243397 4411676751481633059233137)
            ·
              refine ⟨3308757563611224794424853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411676751481633059233137 3308757563611224794424853)
              ·
                refine ⟨155098010794276162238665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3308757563611224794424853 155098010794276162238665)
                ·
                  rfl

theorem cell22_4077706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_4077706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077706 prefixEnd_4077706 := by exact prefixLift 4077706
  have htrace : WordTrace (prefixWord ++ tailWord_4077706) baseStart_4077706 baseEnd_4077706 := by
    simpa [prefixWord, tailWord_4077706, baseEnd_4077706] using wordTrace_append hprefix tailTrace_4077706
  have hstable : (prefixWord ++ tailWord_4077706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077706).length < 2 ^ (prefixWord ++ tailWord_4077706).sum := by decide
  have hdescent : baseEnd_4077706 < baseStart_4077706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077717 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 9]
def baseStart_4077717 : Nat := 118140960795 + 4077717 * 2 ^ 59
def prefixEnd_4077717 : Nat := 4983230072969 + 3 ^ 40 * 4077717 * 2
def baseEnd_4077717 : Nat := 465295287557761699374317

theorem tailTrace_4077717 : CollatzResearch.WordTrace tailWord_4077717 prefixEnd_4077717 465295287557761699374317 := by
  unfold tailWord_4077717
  simp only [CollatzResearch.WordTrace]
  refine ⟨148726557368135202463991405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99151038245423468309327603 148726557368135202463991405)
  ·
    refine ⟨55772459013050700923996777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148726557368135202463991405 55772459013050700923996777)
    ·
      refine ⟨41829344259788025692997583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55772459013050700923996777 41829344259788025692997583)
      ·
        refine ⟨62744016389682038539496375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41829344259788025692997583 62744016389682038539496375)
        ·
          refine ⟨94116024584523057809244563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62744016389682038539496375 94116024584523057809244563)
          ·
            refine ⟨141174036876784586713866845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94116024584523057809244563 141174036876784586713866845)
            ·
              refine ⟨52940263828794220017700067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141174036876784586713866845 52940263828794220017700067)
              ·
                refine ⟨79410395743191330026550101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52940263828794220017700067 79410395743191330026550101)
                ·
                  refine ⟨465295287557761699374317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79410395743191330026550101 465295287557761699374317)
                  ·
                    rfl

theorem cell22_4077717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_4077717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077717 prefixEnd_4077717 := by exact prefixLift 4077717
  have htrace : WordTrace (prefixWord ++ tailWord_4077717) baseStart_4077717 baseEnd_4077717 := by
    simpa [prefixWord, tailWord_4077717, baseEnd_4077717] using wordTrace_append hprefix tailTrace_4077717
  have hstable : (prefixWord ++ tailWord_4077717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077717).length < 2 ^ (prefixWord ++ tailWord_4077717).sum := by decide
  have hdescent : baseEnd_4077717 < baseStart_4077717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077747 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_4077747 : Nat := 118140960795 + 4077747 * 2 ^ 59
def prefixEnd_4077747 : Nat := 4983230072969 + 3 ^ 40 * 4077747 * 2
def baseEnd_4077747 : Nat := 1395896132286375019872859

theorem tailTrace_4077747 : CollatzResearch.WordTrace tailWord_4077747 prefixEnd_4077747 1395896132286375019872859 := by
  unfold tailWord_4077747
  simp only [CollatzResearch.WordTrace]
  refine ⟨148727651558026517587583495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99151767705351011725055663 148727651558026517587583495)
  ·
    refine ⟨223091477337039776381375243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148727651558026517587583495 223091477337039776381375243)
    ·
      refine ⟨334637216005559664572062865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223091477337039776381375243 334637216005559664572062865)
      ·
        refine ⟨250977912004169748429047149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334637216005559664572062865 250977912004169748429047149)
        ·
          refine ⟨94116717001563655660892681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250977912004169748429047149 94116717001563655660892681)
          ·
            refine ⟨70587537751172741745669511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94116717001563655660892681 70587537751172741745669511)
            ·
              refine ⟨105881306626759112618504267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70587537751172741745669511 105881306626759112618504267)
              ·
                refine ⟨158821959940138668927756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105881306626759112618504267 158821959940138668927756401)
                ·
                  refine ⟨119116469955104001695817301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158821959940138668927756401 119116469955104001695817301)
                  ·
                    refine ⟨1395896132286375019872859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119116469955104001695817301 1395896132286375019872859)
                    ·
                      rfl

theorem cell22_4077747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_4077747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077747 prefixEnd_4077747 := by exact prefixLift 4077747
  have htrace : WordTrace (prefixWord ++ tailWord_4077747) baseStart_4077747 baseEnd_4077747 := by
    simpa [prefixWord, tailWord_4077747, baseEnd_4077747] using wordTrace_append hprefix tailTrace_4077747
  have hstable : (prefixWord ++ tailWord_4077747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077747).length < 2 ^ (prefixWord ++ tailWord_4077747).sum := by decide
  have hdescent : baseEnd_4077747 < baseStart_4077747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077751 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 5]
def baseStart_4077751 : Nat := 118140960795 + 4077751 * 2 ^ 59
def prefixEnd_4077751 : Nat := 4983230072969 + 3 ^ 40 * 4077751 * 2
def baseEnd_4077751 : Nat := 465299167189373447590949

theorem tailTrace_4077751 : CollatzResearch.WordTrace tailWord_4077751 prefixEnd_4077751 465299167189373447590949 := by
  unfold tailWord_4077751
  simp only [CollatzResearch.WordTrace]
  refine ⟨148727797450012026270729107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99151864966674684180486071 148727797450012026270729107)
  ·
    refine ⟨223091696175018039406093661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148727797450012026270729107 223091696175018039406093661)
    ·
      refine ⟨83659386065631764777285123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223091696175018039406093661 83659386065631764777285123)
      ·
        refine ⟨125489079098447647165927685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83659386065631764777285123 125489079098447647165927685)
        ·
          refine ⟨23529202330958933843611441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125489079098447647165927685 23529202330958933843611441)
          ·
            refine ⟨17646901748219200382708581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23529202330958933843611441 17646901748219200382708581)
            ·
              refine ⟨3308794077791100071757859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17646901748219200382708581 3308794077791100071757859)
              ·
                refine ⟨4963191116686650107636789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308794077791100071757859 4963191116686650107636789)
                ·
                  refine ⟨465299167189373447590949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4963191116686650107636789 465299167189373447590949)
                  ·
                    rfl

theorem cell22_4077751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 5].length) (baseStart_4077751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077751 prefixEnd_4077751 := by exact prefixLift 4077751
  have htrace : WordTrace (prefixWord ++ tailWord_4077751) baseStart_4077751 baseEnd_4077751 := by
    simpa [prefixWord, tailWord_4077751, baseEnd_4077751] using wordTrace_append hprefix tailTrace_4077751
  have hstable : (prefixWord ++ tailWord_4077751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077751).length < 2 ^ (prefixWord ++ tailWord_4077751).sum := by decide
  have hdescent : baseEnd_4077751 < baseStart_4077751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077809 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_4077809 : Nat := 118140960795 + 4077809 * 2 ^ 59
def prefixEnd_4077809 : Nat := 4983230072969 + 3 ^ 40 * 4077809 * 2
def baseEnd_4077809 : Nat := 1395917356153427524822669

theorem tailTrace_4077809 : CollatzResearch.WordTrace tailWord_4077809 prefixEnd_4077809 1395917356153427524822669 := by
  unfold tailWord_4077809
  simp only [CollatzResearch.WordTrace]
  refine ⟨148729912883801902176340481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99153275255867934784226987 148729912883801902176340481)
  ·
    refine ⟨111547434662851426632255361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148729912883801902176340481 111547434662851426632255361)
    ·
      refine ⟨83660575997138569974191521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111547434662851426632255361 83660575997138569974191521)
      ·
        refine ⟨62745431997853927480643641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83660575997138569974191521 62745431997853927480643641)
        ·
          refine ⟨47059073998390445610482731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62745431997853927480643641 47059073998390445610482731)
          ·
            refine ⟨70588610997585668415724097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47059073998390445610482731 70588610997585668415724097)
            ·
              refine ⟨52941458248189251311793073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70588610997585668415724097 52941458248189251311793073)
              ·
                refine ⟨39706093686141938483844805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52941458248189251311793073 39706093686141938483844805)
                ·
                  refine ⟨7444892566151613465720901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39706093686141938483844805 7444892566151613465720901)
                  ·
                    refine ⟨1395917356153427524822669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444892566151613465720901 1395917356153427524822669)
                    ·
                      rfl

theorem cell22_4077809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_4077809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077809 prefixEnd_4077809 := by exact prefixLift 4077809
  have htrace : WordTrace (prefixWord ++ tailWord_4077809) baseStart_4077809 baseEnd_4077809 := by
    simpa [prefixWord, tailWord_4077809, baseEnd_4077809] using wordTrace_append hprefix tailTrace_4077809
  have hstable : (prefixWord ++ tailWord_4077809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077809).length < 2 ^ (prefixWord ++ tailWord_4077809).sum := by decide
  have hdescent : baseEnd_4077809 < baseStart_4077809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077811 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 2, 3]
def baseStart_4077811 : Nat := 118140960795 + 4077811 * 2 ^ 59
def prefixEnd_4077811 : Nat := 4983230072969 + 3 ^ 40 * 4077811 * 2
def baseEnd_4077811 : Nat := 1395918040794300186272663

theorem tailTrace_4077811 : CollatzResearch.WordTrace tailWord_4077811 prefixEnd_4077811 1395918040794300186272663 := by
  unfold tailWord_4077811
  simp only [CollatzResearch.WordTrace]
  refine ⟨148729985829794656517913287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99153323886529771011942191 148729985829794656517913287)
  ·
    refine ⟨223094978744691984776869931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148729985829794656517913287 223094978744691984776869931)
    ·
      refine ⟨334642468117037977165304897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223094978744691984776869931 334642468117037977165304897)
      ·
        refine ⟨250981851087778482873978673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334642468117037977165304897 250981851087778482873978673)
        ·
          refine ⟨188236388315833862155484005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250981851087778482873978673 188236388315833862155484005)
          ·
            refine ⟨35294322809218849154153251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188236388315833862155484005 35294322809218849154153251)
            ·
              refine ⟨52941484213828273731229877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35294322809218849154153251 52941484213828273731229877)
              ·
                refine ⟨4963264145046400662302801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52941484213828273731229877 4963264145046400662302801)
                ·
                  refine ⟨3722448108784800496727101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963264145046400662302801 3722448108784800496727101)
                  ·
                    refine ⟨1395918040794300186272663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722448108784800496727101 1395918040794300186272663)
                    ·
                      rfl

theorem cell22_4077811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3].length) (baseStart_4077811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077811 prefixEnd_4077811 := by exact prefixLift 4077811
  have htrace : WordTrace (prefixWord ++ tailWord_4077811) baseStart_4077811 baseEnd_4077811 := by
    simpa [prefixWord, tailWord_4077811, baseEnd_4077811] using wordTrace_append hprefix tailTrace_4077811
  have hstable : (prefixWord ++ tailWord_4077811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077811).length < 2 ^ (prefixWord ++ tailWord_4077811).sum := by decide
  have hdescent : baseEnd_4077811 < baseStart_4077811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077886 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4077886 : Nat := 118140960795 + 4077886 * 2 ^ 59
def prefixEnd_4077886 : Nat := 4983230072969 + 3 ^ 40 * 4077886 * 2
def baseEnd_4077886 : Nat := 465314571609008330215811

theorem tailTrace_4077886 : CollatzResearch.WordTrace tailWord_4077886 prefixEnd_4077886 465314571609008330215811 := by
  unfold tailWord_4077886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18591590163065368040861689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99155147536348629551262341 18591590163065368040861689)
  ·
    refine ⟨13943692622299026030646267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18591590163065368040861689 13943692622299026030646267)
    ·
      refine ⟨20915538933448539045969401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13943692622299026030646267 20915538933448539045969401)
      ·
        refine ⟨15686654200086404284477051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20915538933448539045969401 15686654200086404284477051)
        ·
          refine ⟨23529981300129606426715577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15686654200086404284477051 23529981300129606426715577)
          ·
            refine ⟨17647485975097204820036683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23529981300129606426715577 17647485975097204820036683)
            ·
              refine ⟨26471228962645807230055025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647485975097204820036683 26471228962645807230055025)
              ·
                refine ⟨19853421721984355422541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26471228962645807230055025 19853421721984355422541269)
                ·
                  refine ⟨465314571609008330215811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19853421721984355422541269 465314571609008330215811)
                  ·
                    rfl

theorem cell22_4077886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4077886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077886 prefixEnd_4077886 := by exact prefixLift 4077886
  have htrace : WordTrace (prefixWord ++ tailWord_4077886) baseStart_4077886 baseEnd_4077886 := by
    simpa [prefixWord, tailWord_4077886, baseEnd_4077886] using wordTrace_append hprefix tailTrace_4077886
  have hstable : (prefixWord ++ tailWord_4077886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077886).length < 2 ^ (prefixWord ++ tailWord_4077886).sum := by decide
  have hdescent : baseEnd_4077886 < baseStart_4077886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077920 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_4077920 : Nat := 118140960795 + 4077920 * 2 ^ 59
def prefixEnd_4077920 : Nat := 4983230072969 + 3 ^ 40 * 4077920 * 2
def baseEnd_4077920 : Nat := 465318451240620078432443

theorem tailTrace_4077920 : CollatzResearch.WordTrace tailWord_4077920 prefixEnd_4077920 465318451240620078432443 := by
  unfold tailWord_4077920
  simp only [CollatzResearch.WordTrace]
  refine ⟨74366980693199884066815607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99155974257599845422420809 74366980693199884066815607)
  ·
    refine ⟨111550471039799826100223411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74366980693199884066815607 111550471039799826100223411)
    ·
      refine ⟨167325706559699739150335117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111550471039799826100223411 167325706559699739150335117)
      ·
        refine ⟨62747139959887402181375669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167325706559699739150335117 62747139959887402181375669)
        ·
          refine ⟨5882544371239443954503969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62747139959887402181375669 5882544371239443954503969)
          ·
            refine ⟨4411908278429582965877977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882544371239443954503969 4411908278429582965877977)
            ·
              refine ⟨3308931208822187224408483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411908278429582965877977 3308931208822187224408483)
              ·
                refine ⟨4963396813233280836612725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308931208822187224408483 4963396813233280836612725)
                ·
                  refine ⟨465318451240620078432443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4963396813233280836612725 465318451240620078432443)
                  ·
                    rfl

theorem cell22_4077920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_4077920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077920 prefixEnd_4077920 := by exact prefixLift 4077920
  have htrace : WordTrace (prefixWord ++ tailWord_4077920) baseStart_4077920 baseEnd_4077920 := by
    simpa [prefixWord, tailWord_4077920, baseEnd_4077920] using wordTrace_append hprefix tailTrace_4077920
  have hstable : (prefixWord ++ tailWord_4077920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077920).length < 2 ^ (prefixWord ++ tailWord_4077920).sum := by decide
  have hdescent : baseEnd_4077920 < baseStart_4077920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077963 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 2, 3]
def baseStart_4077963 : Nat := 118140960795 + 4077963 * 2 ^ 59
def prefixEnd_4077963 : Nat := 4983230072969 + 3 ^ 40 * 4077963 * 2
def baseEnd_4077963 : Nat := 1395970073500622456472197

theorem tailTrace_4077963 : CollatzResearch.WordTrace tailWord_4077963 prefixEnd_4077963 1395970073500622456472197 := by
  unfold tailWord_4077963
  simp only [CollatzResearch.WordTrace]
  refine ⟨148735529725243986477446543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99157019816829324318297695 148735529725243986477446543)
  ·
    refine ⟨223103294587865979716169815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148735529725243986477446543 223103294587865979716169815)
    ·
      refine ⟨334654941881798969574254723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223103294587865979716169815 334654941881798969574254723)
      ·
        refine ⟨501982412822698454361382085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334654941881798969574254723 501982412822698454361382085)
        ·
          refine ⟨94121702404255960192759141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501982412822698454361382085 94121702404255960192759141)
          ·
            refine ⟨17647819200797992536142339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94121702404255960192759141 17647819200797992536142339)
            ·
              refine ⟨26471728801196988804213509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647819200797992536142339 26471728801196988804213509)
              ·
                refine ⟨4963449150224435400790033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26471728801196988804213509 4963449150224435400790033)
                ·
                  refine ⟨3722586862668326550592525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963449150224435400790033 3722586862668326550592525)
                  ·
                    refine ⟨1395970073500622456472197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722586862668326550592525 1395970073500622456472197)
                    ·
                      rfl

theorem cell22_4077963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 3].length) (baseStart_4077963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4077963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4077963 prefixEnd_4077963 := by exact prefixLift 4077963
  have htrace : WordTrace (prefixWord ++ tailWord_4077963) baseStart_4077963 baseEnd_4077963 := by
    simpa [prefixWord, tailWord_4077963, baseEnd_4077963] using wordTrace_append hprefix tailTrace_4077963
  have hstable : (prefixWord ++ tailWord_4077963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077963).length < 2 ^ (prefixWord ++ tailWord_4077963).sum := by decide
  have hdescent : baseEnd_4077963 < baseStart_4077963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078025 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 1, 3]
def baseStart_4078025 : Nat := 118140960795 + 4078025 * 2 ^ 59
def prefixEnd_4078025 : Nat := 4983230072969 + 3 ^ 40 * 4078025 * 2
def baseEnd_4078025 : Nat := 1395991297367674961422007

theorem tailTrace_4078025 : CollatzResearch.WordTrace tailWord_4078025 prefixEnd_4078025 1395991297367674961422007 := by
  unfold tailWord_4078025
  simp only [CollatzResearch.WordTrace]
  refine ⟨148737791051019371066203529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99158527367346247377469019 148737791051019371066203529)
  ·
    refine ⟨111553343288264528299652647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148737791051019371066203529 111553343288264528299652647)
    ·
      refine ⟨167330014932396792449478971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111553343288264528299652647 167330014932396792449478971)
      ·
        refine ⟨250995022398595188674218457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167330014932396792449478971 250995022398595188674218457)
        ·
          refine ⟨188246266798946391505663843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250995022398595188674218457 188246266798946391505663843)
          ·
            refine ⟨282369400198419587258495765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188246266798946391505663843 282369400198419587258495765)
            ·
              refine ⟨13236065634300918152741989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282369400198419587258495765 13236065634300918152741989)
              ·
                refine ⟨2481762306431422153639123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13236065634300918152741989 2481762306431422153639123)
                ·
                  refine ⟨3722643459647133230458685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481762306431422153639123 3722643459647133230458685)
                  ·
                    refine ⟨1395991297367674961422007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722643459647133230458685 1395991297367674961422007)
                    ·
                      rfl

theorem cell22_4078025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_4078025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078025 prefixEnd_4078025 := by exact prefixLift 4078025
  have htrace : WordTrace (prefixWord ++ tailWord_4078025) baseStart_4078025 baseEnd_4078025 := by
    simpa [prefixWord, tailWord_4078025, baseEnd_4078025] using wordTrace_append hprefix tailTrace_4078025
  have hstable : (prefixWord ++ tailWord_4078025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078025).length < 2 ^ (prefixWord ++ tailWord_4078025).sum := by decide
  have hdescent : baseEnd_4078025 < baseStart_4078025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078134 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_4078134 : Nat := 118140960795 + 4078134 * 2 ^ 59
def prefixEnd_4078134 : Nat := 4983230072969 + 3 ^ 40 * 4078134 * 2
def baseEnd_4078134 : Nat := 465342870098411670148891

theorem tailTrace_4078134 : CollatzResearch.WordTrace tailWord_4078134 prefixEnd_4078134 465342870098411670148891 := by
  unfold tailWord_4078134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9296360412976530167620091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99161177738416321787947637 9296360412976530167620091)
  ·
    refine ⟨13944540619464795251430137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9296360412976530167620091 13944540619464795251430137)
    ·
      refine ⟨10458405464598596438572603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13944540619464795251430137 10458405464598596438572603)
      ·
        refine ⟨15687608196897894657858905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10458405464598596438572603 15687608196897894657858905)
        ·
          refine ⟨11765706147673420993394179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15687608196897894657858905 11765706147673420993394179)
          ·
            refine ⟨17648559221510131490091269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765706147673420993394179 17648559221510131490091269)
            ·
              refine ⟨3309104854033149654392113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17648559221510131490091269 3309104854033149654392113)
              ·
                refine ⟨2481828640524862240794085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309104854033149654392113 2481828640524862240794085)
                ·
                  refine ⟨465342870098411670148891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481828640524862240794085 465342870098411670148891)
                  ·
                    rfl

theorem cell22_4078134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_4078134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078134 prefixEnd_4078134 := by exact prefixLift 4078134
  have htrace : WordTrace (prefixWord ++ tailWord_4078134) baseStart_4078134 baseEnd_4078134 := by
    simpa [prefixWord, tailWord_4078134, baseEnd_4078134] using wordTrace_append hprefix tailTrace_4078134
  have hstable : (prefixWord ++ tailWord_4078134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078134).length < 2 ^ (prefixWord ++ tailWord_4078134).sum := by decide
  have hdescent : baseEnd_4078134 < baseStart_4078134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078145 : List Nat := [1, 2, 5, 1, 1, 4, 1, 7]
def baseStart_4078145 : Nat := 118140960795 + 4078145 * 2 ^ 59
def prefixEnd_4078145 : Nat := 4983230072969 + 3 ^ 40 * 4078145 * 2
def baseEnd_4078145 : Nat := 155114708424448294269071

theorem tailTrace_4078145 : CollatzResearch.WordTrace tailWord_4078145 prefixEnd_4078145 155114708424448294269071 := by
  unfold tailWord_4078145
  simp only [CollatzResearch.WordTrace]
  refine ⟨148742167810584631560571889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99161445207056421040381259 148742167810584631560571889)
  ·
    refine ⟨111556625857938473670428917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148742167810584631560571889 111556625857938473670428917)
    ·
      refine ⟨10458433674181731906602711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111556625857938473670428917 10458433674181731906602711)
      ·
        refine ⟨15687650511272597859904067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10458433674181731906602711 15687650511272597859904067)
        ·
          refine ⟨23531475766908896789856101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687650511272597859904067 23531475766908896789856101)
          ·
            refine ⟨4412151706295418148098019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23531475766908896789856101 4412151706295418148098019)
            ·
              refine ⟨6618227559443127222147029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412151706295418148098019 6618227559443127222147029)
              ·
                refine ⟨155114708424448294269071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6618227559443127222147029 155114708424448294269071)
                ·
                  rfl

theorem cell22_4078145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 7].length) (baseStart_4078145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078145 prefixEnd_4078145 := by exact prefixLift 4078145
  have htrace : WordTrace (prefixWord ++ tailWord_4078145) baseStart_4078145 baseEnd_4078145 := by
    simpa [prefixWord, tailWord_4078145, baseEnd_4078145] using wordTrace_append hprefix tailTrace_4078145
  have hstable : (prefixWord ++ tailWord_4078145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078145).length < 2 ^ (prefixWord ++ tailWord_4078145).sum := by decide
  have hdescent : baseEnd_4078145 < baseStart_4078145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078177 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 1, 3]
def baseStart_4078177 : Nat := 118140960795 + 4078177 * 2 ^ 59
def prefixEnd_4078177 : Nat := 4983230072969 + 3 ^ 40 * 4078177 * 2
def baseEnd_4078177 : Nat := 1396043330073997231621541

theorem tailTrace_4078177 : CollatzResearch.WordTrace tailWord_4078177 prefixEnd_4078177 1396043330073997231621541 := by
  unfold tailWord_4078177
  simp only [CollatzResearch.WordTrace]
  refine ⟨148743334946468701025736785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99162223297645800683824523 148743334946468701025736785)
  ·
    refine ⟨111557501209851525769302589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148743334946468701025736785 111557501209851525769302589)
    ·
      refine ⟨41834062953694322163488471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111557501209851525769302589 41834062953694322163488471)
      ·
        refine ⟨62751094430541483245232707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41834062953694322163488471 62751094430541483245232707)
        ·
          refine ⟨94126641645812224867849061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62751094430541483245232707 94126641645812224867849061)
          ·
            refine ⟨17648745308589792162721699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94126641645812224867849061 17648745308589792162721699)
            ·
              refine ⟨26473117962884688244082549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17648745308589792162721699 26473117962884688244082549)
              ·
                refine ⟨2481854809020439522882739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26473117962884688244082549 2481854809020439522882739)
                ·
                  refine ⟨3722782213530659284324109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481854809020439522882739 3722782213530659284324109)
                  ·
                    refine ⟨1396043330073997231621541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722782213530659284324109 1396043330073997231621541)
                    ·
                      rfl

theorem cell22_4078177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_4078177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078177 prefixEnd_4078177 := by exact prefixLift 4078177
  have htrace : WordTrace (prefixWord ++ tailWord_4078177) baseStart_4078177 baseEnd_4078177 := by
    simpa [prefixWord, tailWord_4078177, baseEnd_4078177] using wordTrace_append hprefix tailTrace_4078177
  have hstable : (prefixWord ++ tailWord_4078177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078177).length < 2 ^ (prefixWord ++ tailWord_4078177).sum := by decide
  have hdescent : baseEnd_4078177 < baseStart_4078177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078188 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_4078188 : Nat := 118140960795 + 4078188 * 2 ^ 59
def prefixEnd_4078188 : Nat := 4983230072969 + 3 ^ 40 * 4078188 * 2
def baseEnd_4078188 : Nat := 1396047095598796869596507

theorem tailTrace_4078188 : CollatzResearch.WordTrace tailWord_4078188 prefixEnd_4078188 1396047095598796869596507 := by
  unfold tailWord_4078188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74371868074714424952193609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99162490766285899936258145 74371868074714424952193609)
  ·
    refine ⟨55778901056035818714145207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74371868074714424952193609 55778901056035818714145207)
    ·
      refine ⟨83668351584053728071217811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55778901056035818714145207 83668351584053728071217811)
      ·
        refine ⟨125502527376080592106826717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83668351584053728071217811 125502527376080592106826717)
        ·
          refine ⟨47063447766030222040060019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125502527376080592106826717 47063447766030222040060019)
          ·
            refine ⟨70595171649045333060090029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47063447766030222040060019 70595171649045333060090029)
            ·
              refine ⟨26473189368391999897533761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70595171649045333060090029 26473189368391999897533761)
              ·
                refine ⟨19854892026293999923150321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26473189368391999897533761 19854892026293999923150321)
                ·
                  refine ⟨14891169019720499942362741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19854892026293999923150321 14891169019720499942362741)
                  ·
                    refine ⟨1396047095598796869596507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14891169019720499942362741 1396047095598796869596507)
                    ·
                      rfl

theorem cell22_4078188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_4078188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078188 prefixEnd_4078188 := by exact prefixLift 4078188
  have htrace : WordTrace (prefixWord ++ tailWord_4078188) baseStart_4078188 baseEnd_4078188 := by
    simpa [prefixWord, tailWord_4078188, baseEnd_4078188] using wordTrace_append hprefix tailTrace_4078188
  have hstable : (prefixWord ++ tailWord_4078188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078188).length < 2 ^ (prefixWord ++ tailWord_4078188).sum := by decide
  have hdescent : baseEnd_4078188 < baseStart_4078188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078190 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_4078190 : Nat := 118140960795 + 4078190 * 2 ^ 59
def prefixEnd_4078190 : Nat := 4983230072969 + 3 ^ 40 * 4078190 * 2
def baseEnd_4078190 : Nat := 465349260079889843682167

theorem tailTrace_4078190 : CollatzResearch.WordTrace tailWord_4078190 prefixEnd_4078190 465349260079889843682167 := by
  unfold tailWord_4078190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592976136927700530745003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99162539396947736163973349 18592976136927700530745003)
  ·
    refine ⟨27889464205391550796117505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592976136927700530745003 27889464205391550796117505)
    ·
      refine ⟨20917098154043663097088129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27889464205391550796117505 20917098154043663097088129)
      ·
        refine ⟨15687823615532747322816097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20917098154043663097088129 15687823615532747322816097)
        ·
          refine ⟨11765867711649560492112073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15687823615532747322816097 11765867711649560492112073)
          ·
            refine ⟨8824400783737170369084055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11765867711649560492112073 8824400783737170369084055)
            ·
              refine ⟨13236601175605755553626083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824400783737170369084055 13236601175605755553626083)
              ·
                refine ⟨19854901763408633330439125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236601175605755553626083 19854901763408633330439125)
                ·
                  refine ⟨465349260079889843682167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19854901763408633330439125 465349260079889843682167)
                  ·
                    rfl

theorem cell22_4078190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_4078190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078190 prefixEnd_4078190 := by exact prefixLift 4078190
  have htrace : WordTrace (prefixWord ++ tailWord_4078190) baseStart_4078190 baseEnd_4078190 := by
    simpa [prefixWord, tailWord_4078190, baseEnd_4078190] using wordTrace_append hprefix tailTrace_4078190
  have hstable : (prefixWord ++ tailWord_4078190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078190).length < 2 ^ (prefixWord ++ tailWord_4078190).sum := by decide
  have hdescent : baseEnd_4078190 < baseStart_4078190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078203 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_4078203 : Nat := 118140960795 + 4078203 * 2 ^ 59
def prefixEnd_4078203 : Nat := 4983230072969 + 3 ^ 40 * 4078203 * 2
def baseEnd_4078203 : Nat := 1396052230405341830471461

theorem tailTrace_4078203 : CollatzResearch.WordTrace tailWord_4078203 prefixEnd_4078203 1396052230405341830471461 := by
  unfold tailWord_4078203
  simp only [CollatzResearch.WordTrace]
  refine ⟨148744283244374507466183263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99162855496249671644122175 148744283244374507466183263)
  ·
    refine ⟨223116424866561761199274895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148744283244374507466183263 223116424866561761199274895)
    ·
      refine ⟨334674637299842641798912343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223116424866561761199274895 334674637299842641798912343)
      ·
        refine ⟨502011955949763962698368515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334674637299842641798912343 502011955949763962698368515)
        ·
          refine ⟨753017933924645944047552773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502011955949763962698368515 753017933924645944047552773)
          ·
            refine ⟨141190862610871114508916145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 753017933924645944047552773 141190862610871114508916145)
            ·
              refine ⟨105893146958153335881687109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141190862610871114508916145 105893146958153335881687109)
              ·
                refine ⟨19854965054653750477816333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105893146958153335881687109 19854965054653750477816333)
                ·
                  refine ⟨7445611895495156429181125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19854965054653750477816333 7445611895495156429181125)
                  ·
                    refine ⟨1396052230405341830471461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445611895495156429181125 1396052230405341830471461)
                    ·
                      rfl

theorem cell22_4078203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_4078203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078203 prefixEnd_4078203 := by exact prefixLift 4078203
  have htrace : WordTrace (prefixWord ++ tailWord_4078203) baseStart_4078203 baseEnd_4078203 := by
    simpa [prefixWord, tailWord_4078203, baseEnd_4078203] using wordTrace_append hprefix tailTrace_4078203
  have hstable : (prefixWord ++ tailWord_4078203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078203).length < 2 ^ (prefixWord ++ tailWord_4078203).sum := by decide
  have hdescent : baseEnd_4078203 < baseStart_4078203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078233 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_4078233 : Nat := 118140960795 + 4078233 * 2 ^ 59
def prefixEnd_4078233 : Nat := 4983230072969 + 3 ^ 40 * 4078233 * 2
def baseEnd_4078233 : Nat := 1396062500018431752221369

theorem tailTrace_4078233 : CollatzResearch.WordTrace tailWord_4078233 prefixEnd_4078233 1396062500018431752221369 := by
  unfold tailWord_4078233
  simp only [CollatzResearch.WordTrace]
  refine ⟨148745377434265822589775353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99163584956177215059850235 148745377434265822589775353)
  ·
    refine ⟨111559033075699366942331515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148745377434265822589775353 111559033075699366942331515)
    ·
      refine ⟨167338549613549050413497273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111559033075699366942331515 167338549613549050413497273)
      ·
        refine ⟨125503912210161787810122955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167338549613549050413497273 125503912210161787810122955)
        ·
          refine ⟨188255868315242681715184433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125503912210161787810122955 188255868315242681715184433)
          ·
            refine ⟨141191901236432011286388325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188255868315242681715184433 141191901236432011286388325)
            ·
              refine ⟨26473481481831002116197811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141191901236432011286388325 26473481481831002116197811)
              ·
                refine ⟨39710222222746503174296717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26473481481831002116197811 39710222222746503174296717)
                ·
                  refine ⟨14891333333529938690361269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39710222222746503174296717 14891333333529938690361269)
                  ·
                    refine ⟨1396062500018431752221369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14891333333529938690361269 1396062500018431752221369)
                    ·
                      rfl

theorem cell22_4078233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_4078233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078233 prefixEnd_4078233 := by exact prefixLift 4078233
  have htrace : WordTrace (prefixWord ++ tailWord_4078233) baseStart_4078233 baseEnd_4078233 := by
    simpa [prefixWord, tailWord_4078233, baseEnd_4078233] using wordTrace_append hprefix tailTrace_4078233
  have hstable : (prefixWord ++ tailWord_4078233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078233).length < 2 ^ (prefixWord ++ tailWord_4078233).sum := by decide
  have hdescent : baseEnd_4078233 < baseStart_4078233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078282 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_4078282 : Nat := 118140960795 + 4078282 * 2 ^ 59
def prefixEnd_4078282 : Nat := 4983230072969 + 3 ^ 40 * 4078282 * 2
def baseEnd_4078282 : Nat := 1396079273719811957746219

theorem tailTrace_4078282 : CollatzResearch.WordTrace tailWord_4078282 prefixEnd_4078282 1396079273719811957746219 := by
  unfold tailWord_4078282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37186791152772075989577275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99164776407392202638872733 37186791152772075989577275)
  ·
    refine ⟨55780186729158113984365913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37186791152772075989577275 55780186729158113984365913)
    ·
      refine ⟨41835140046868585488274435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55780186729158113984365913 41835140046868585488274435)
      ·
        refine ⟨62752710070302878232411653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41835140046868585488274435 62752710070302878232411653)
        ·
          refine ⟨11766133138181789668577185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62752710070302878232411653 11766133138181789668577185)
          ·
            refine ⟨8824599853636342251432889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11766133138181789668577185 8824599853636342251432889)
            ·
              refine ⟨6618449890227256688574667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8824599853636342251432889 6618449890227256688574667)
              ·
                refine ⟨9927674835340885032862001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6618449890227256688574667 9927674835340885032862001)
                ·
                  refine ⟨7445756126505663774646501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9927674835340885032862001 7445756126505663774646501)
                  ·
                    refine ⟨1396079273719811957746219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445756126505663774646501 1396079273719811957746219)
                    ·
                      rfl

theorem cell22_4078282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_4078282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078282 prefixEnd_4078282 := by exact prefixLift 4078282
  have htrace : WordTrace (prefixWord ++ tailWord_4078282) baseStart_4078282 baseEnd_4078282 := by
    simpa [prefixWord, tailWord_4078282, baseEnd_4078282] using wordTrace_append hprefix tailTrace_4078282
  have hstable : (prefixWord ++ tailWord_4078282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078282).length < 2 ^ (prefixWord ++ tailWord_4078282).sum := by decide
  have hdescent : baseEnd_4078282 < baseStart_4078282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078340 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4078340 : Nat := 118140960795 + 4078340 * 2 ^ 59
def prefixEnd_4078340 : Nat := 4983230072969 + 3 ^ 40 * 4078340 * 2
def baseEnd_4078340 : Nat := 1396099128305119139796041

theorem tailTrace_4078340 : CollatzResearch.WordTrace tailWord_4078340 prefixEnd_4078340 1396099128305119139796041 := by
  unfold tailWord_4078340
  simp only [CollatzResearch.WordTrace]
  refine ⟨74374640022439089931960237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99166186696585453242613649 74374640022439089931960237)
  ·
    refine ⟨27890490008414658724485089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74374640022439089931960237 27890490008414658724485089)
    ·
      refine ⟨20917867506310994043363817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27890490008414658724485089 20917867506310994043363817)
      ·
        refine ⟨15688400629733245532522863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20917867506310994043363817 15688400629733245532522863)
        ·
          refine ⟨23532600944599868298784295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15688400629733245532522863 23532600944599868298784295)
          ·
            refine ⟨35298901416899802448176443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23532600944599868298784295 35298901416899802448176443)
            ·
              refine ⟨52948352125349703672264665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35298901416899802448176443 52948352125349703672264665)
              ·
                refine ⟨39711264094012277754198499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52948352125349703672264665 39711264094012277754198499)
                ·
                  refine ⟨59566896141018416631297749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39711264094012277754198499 59566896141018416631297749)
                  ·
                    refine ⟨1396099128305119139796041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59566896141018416631297749 1396099128305119139796041)
                    ·
                      rfl

theorem cell22_4078340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4078340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078340 prefixEnd_4078340 := by exact prefixLift 4078340
  have htrace : WordTrace (prefixWord ++ tailWord_4078340) baseStart_4078340 baseEnd_4078340 := by
    simpa [prefixWord, tailWord_4078340, baseEnd_4078340] using wordTrace_append hprefix tailTrace_4078340
  have hstable : (prefixWord ++ tailWord_4078340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078340).length < 2 ^ (prefixWord ++ tailWord_4078340).sum := by decide
  have hdescent : baseEnd_4078340 < baseStart_4078340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078359 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 5]
def baseStart_4078359 : Nat := 118140960795 + 4078359 * 2 ^ 59
def prefixEnd_4078359 : Nat := 4983230072969 + 3 ^ 40 * 4078359 * 2
def baseEnd_4078359 : Nat := 465368544131136474523661

theorem tailTrace_4078359 : CollatzResearch.WordTrace tailWord_4078359 prefixEnd_4078359 465368544131136474523661 := by
  unfold tailWord_4078359
  simp only [CollatzResearch.WordTrace]
  refine ⟨148749973031809346108862131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99166648687872897405908087 148749973031809346108862131)
  ·
    refine ⟨223124959547714019163293197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148749973031809346108862131 223124959547714019163293197)
    ·
      refine ⟨83671859830392757186234949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223124959547714019163293197 83671859830392757186234949)
      ·
        refine ⟨15688473718198641972419053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83671859830392757186234949 15688473718198641972419053)
        ·
          refine ⟨5883177644324490739657145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15688473718198641972419053 5883177644324490739657145)
          ·
            refine ⟨4412383233243368054742859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5883177644324490739657145 4412383233243368054742859)
            ·
              refine ⟨6618574849865052082114289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412383233243368054742859 6618574849865052082114289)
              ·
                refine ⟨4963931137398789061585717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6618574849865052082114289 4963931137398789061585717)
                ·
                  refine ⟨465368544131136474523661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4963931137398789061585717 465368544131136474523661)
                  ·
                    rfl

theorem cell22_4078359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 5].length) (baseStart_4078359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078359 prefixEnd_4078359 := by exact prefixLift 4078359
  have htrace : WordTrace (prefixWord ++ tailWord_4078359) baseStart_4078359 baseEnd_4078359 := by
    simpa [prefixWord, tailWord_4078359, baseEnd_4078359] using wordTrace_append hprefix tailTrace_4078359
  have hstable : (prefixWord ++ tailWord_4078359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078359).length < 2 ^ (prefixWord ++ tailWord_4078359).sum := by decide
  have hdescent : baseEnd_4078359 < baseStart_4078359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078389 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4078389 : Nat := 118140960795 + 4078389 * 2 ^ 59
def prefixEnd_4078389 : Nat := 4983230072969 + 3 ^ 40 * 4078389 * 2
def baseEnd_4078389 : Nat := 1396115902006499345320891

theorem tailTrace_4078389 : CollatzResearch.WordTrace tailWord_4078389 prefixEnd_4078389 1396115902006499345320891 := by
  unfold tailWord_4078389
  simp only [CollatzResearch.WordTrace]
  refine ⟨148751067221700661232454221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99167378147800440821636147 148751067221700661232454221)
  ·
    refine ⟨55781650208137747962170333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148751067221700661232454221 55781650208137747962170333)
    ·
      refine ⟨20918118828051655485813875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55781650208137747962170333 20918118828051655485813875)
      ·
        refine ⟨31377178242077483228720813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20918118828051655485813875 31377178242077483228720813)
        ·
          refine ⟨11766441840779056210770305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31377178242077483228720813 11766441840779056210770305)
          ·
            refine ⟨8824831380584292158077729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11766441840779056210770305 8824831380584292158077729)
            ·
              refine ⟨6618623535438219118558297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8824831380584292158077729 6618623535438219118558297)
              ·
                refine ⟨4963967651578664338918723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6618623535438219118558297 4963967651578664338918723)
                ·
                  refine ⟨7445951477367996508378085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963967651578664338918723 7445951477367996508378085)
                  ·
                    refine ⟨1396115902006499345320891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445951477367996508378085 1396115902006499345320891)
                    ·
                      rfl

theorem cell22_4078389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4078389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078389 prefixEnd_4078389 := by exact prefixLift 4078389
  have htrace : WordTrace (prefixWord ++ tailWord_4078389) baseStart_4078389 baseEnd_4078389 := by
    simpa [prefixWord, tailWord_4078389, baseEnd_4078389] using wordTrace_append hprefix tailTrace_4078389
  have hstable : (prefixWord ++ tailWord_4078389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078389).length < 2 ^ (prefixWord ++ tailWord_4078389).sum := by decide
  have hdescent : baseEnd_4078389 < baseStart_4078389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078400 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_4078400 : Nat := 118140960795 + 4078400 * 2 ^ 59
def prefixEnd_4078400 : Nat := 4983230072969 + 3 ^ 40 * 4078400 * 2
def baseEnd_4078400 : Nat := 1396119667531298983295857

theorem tailTrace_4078400 : CollatzResearch.WordTrace tailWord_4078400 prefixEnd_4078400 1396119667531298983295857 := by
  unfold tailWord_4078400
  simp only [CollatzResearch.WordTrace]
  refine ⟨74375734212330405055552327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99167645616440540074069769 74375734212330405055552327)
  ·
    refine ⟨111563601318495607583328491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74375734212330405055552327 111563601318495607583328491)
    ·
      refine ⟨167345401977743411374992737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111563601318495607583328491 167345401977743411374992737)
      ·
        refine ⟨125509051483307558531244553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167345401977743411374992737 125509051483307558531244553)
        ·
          refine ⟨94131788612480668898433415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125509051483307558531244553 94131788612480668898433415)
          ·
            refine ⟨141197682918721003347650123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94131788612480668898433415 141197682918721003347650123)
            ·
              refine ⟨211796524378081505021475185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141197682918721003347650123 211796524378081505021475185)
              ·
                refine ⟨158847393283561128766106389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211796524378081505021475185 158847393283561128766106389)
                ·
                  refine ⟨7445971560166927910911237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158847393283561128766106389 7445971560166927910911237)
                  ·
                    refine ⟨1396119667531298983295857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445971560166927910911237 1396119667531298983295857)
                    ·
                      rfl

theorem cell22_4078400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_4078400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078400 prefixEnd_4078400 := by exact prefixLift 4078400
  have htrace : WordTrace (prefixWord ++ tailWord_4078400) baseStart_4078400 baseEnd_4078400 := by
    simpa [prefixWord, tailWord_4078400, baseEnd_4078400] using wordTrace_append hprefix tailTrace_4078400
  have hstable : (prefixWord ++ tailWord_4078400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078400).length < 2 ^ (prefixWord ++ tailWord_4078400).sum := by decide
  have hdescent : baseEnd_4078400 < baseStart_4078400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078436 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_4078436 : Nat := 118140960795 + 4078436 * 2 ^ 59
def prefixEnd_4078436 : Nat := 4983230072969 + 3 ^ 40 * 4078436 * 2
def baseEnd_4078436 : Nat := 1396131991067006889395747

theorem tailTrace_4078436 : CollatzResearch.WordTrace tailWord_4078436 prefixEnd_4078436 1396131991067006889395747 := by
  unfold tailWord_4078436
  simp only [CollatzResearch.WordTrace]
  refine ⟨74376390726265194129707581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99168520968353592172943441 74376390726265194129707581)
  ·
    refine ⟨27891146522349447798640343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74376390726265194129707581 27891146522349447798640343)
    ·
      refine ⟨41836719783524171697960515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27891146522349447798640343 41836719783524171697960515)
      ·
        refine ⟨62755079675286257546940773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41836719783524171697960515 62755079675286257546940773)
        ·
          refine ⟨11766577439116173290051395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62755079675286257546940773 11766577439116173290051395)
          ·
            refine ⟨17649866158674259935077093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766577439116173290051395 17649866158674259935077093)
            ·
              refine ⟨3309349904751423737826955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17649866158674259935077093 3309349904751423737826955)
              ·
                refine ⟨4964024857127135606740433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309349904751423737826955 4964024857127135606740433)
                ·
                  refine ⟨3723018642845351705055325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964024857127135606740433 3723018642845351705055325)
                  ·
                    refine ⟨1396131991067006889395747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723018642845351705055325 1396131991067006889395747)
                    ·
                      rfl

theorem cell22_4078436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_4078436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078436 prefixEnd_4078436 := by exact prefixLift 4078436
  have htrace : WordTrace (prefixWord ++ tailWord_4078436) baseStart_4078436 baseEnd_4078436 := by
    simpa [prefixWord, tailWord_4078436, baseEnd_4078436] using wordTrace_append hprefix tailTrace_4078436
  have hstable : (prefixWord ++ tailWord_4078436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078436).length < 2 ^ (prefixWord ++ tailWord_4078436).sum := by decide
  have hdescent : baseEnd_4078436 < baseStart_4078436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078447 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 3, 3]
def baseStart_4078447 : Nat := 118140960795 + 4078447 * 2 ^ 59
def prefixEnd_4078447 : Nat := 4983230072969 + 3 ^ 40 * 4078447 * 2
def baseEnd_4078447 : Nat := 1396135756591806527370713

theorem tailTrace_4078447 : CollatzResearch.WordTrace tailWord_4078447 prefixEnd_4078447 1396135756591806527370713 := by
  unfold tailWord_4078447
  simp only [CollatzResearch.WordTrace]
  refine ⟨148753182655490537138065595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99168788436993691425377063 148753182655490537138065595)
  ·
    refine ⟨223129773983235805707098393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148753182655490537138065595 223129773983235805707098393)
    ·
      refine ⟨167347330487426854280323795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223129773983235805707098393 167347330487426854280323795)
      ·
        refine ⟨251020995731140281420485693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167347330487426854280323795 251020995731140281420485693)
        ·
          refine ⟨94132873399177605532682135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251020995731140281420485693 94132873399177605532682135)
          ·
            refine ⟨141199310098766408299023203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94132873399177605532682135 141199310098766408299023203)
            ·
              refine ⟨211798965148149612448534805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141199310098766408299023203 211798965148149612448534805)
              ·
                refine ⟨9928076491319513083525069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211798965148149612448534805 9928076491319513083525069)
                ·
                  refine ⟨3723028684244817406321901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9928076491319513083525069 3723028684244817406321901)
                  ·
                    refine ⟨1396135756591806527370713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723028684244817406321901 1396135756591806527370713)
                    ·
                      rfl

theorem cell22_4078447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_4078447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078447 prefixEnd_4078447 := by exact prefixLift 4078447
  have htrace : WordTrace (prefixWord ++ tailWord_4078447) baseStart_4078447 baseEnd_4078447 := by
    simpa [prefixWord, tailWord_4078447, baseEnd_4078447] using wordTrace_append hprefix tailTrace_4078447
  have hstable : (prefixWord ++ tailWord_4078447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078447).length < 2 ^ (prefixWord ++ tailWord_4078447).sum := by decide
  have hdescent : baseEnd_4078447 < baseStart_4078447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078460 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_4078460 : Nat := 118140960795 + 4078460 * 2 ^ 59
def prefixEnd_4078460 : Nat := 4983230072969 + 3 ^ 40 * 4078460 * 2
def baseEnd_4078460 : Nat := 465380068919159608931891

theorem tailTrace_4078460 : CollatzResearch.WordTrace tailWord_4078460 prefixEnd_4078460 465380068919159608931891 := by
  unfold tailWord_4078460
  simp only [CollatzResearch.WordTrace]
  refine ⟨74376828402221720179144417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99169104536295626905525889 74376828402221720179144417)
  ·
    refine ⟨55782621301666290134358313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74376828402221720179144417 55782621301666290134358313)
    ·
      refine ⟨41836965976249717600768735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55782621301666290134358313 41836965976249717600768735)
      ·
        refine ⟨62755448964374576401153103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41836965976249717600768735 62755448964374576401153103)
        ·
          refine ⟨94133173446561864601729655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62755448964374576401153103 94133173446561864601729655)
          ·
            refine ⟨141199760169842796902594483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94133173446561864601729655 141199760169842796902594483)
            ·
              refine ⟨211799640254764195353891725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141199760169842796902594483 211799640254764195353891725)
              ·
                refine ⟨79424865095536573257709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211799640254764195353891725 79424865095536573257709397)
                ·
                  refine ⟨465380068919159608931891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79424865095536573257709397 465380068919159608931891)
                  ·
                    rfl

theorem cell22_4078460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_4078460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078460 prefixEnd_4078460 := by exact prefixLift 4078460
  have htrace : WordTrace (prefixWord ++ tailWord_4078460) baseStart_4078460 baseEnd_4078460 := by
    simpa [prefixWord, tailWord_4078460, baseEnd_4078460] using wordTrace_append hprefix tailTrace_4078460
  have hstable : (prefixWord ++ tailWord_4078460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078460).length < 2 ^ (prefixWord ++ tailWord_4078460).sum := by decide
  have hdescent : baseEnd_4078460 < baseStart_4078460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078466 : List Nat := [3, 4, 2, 2, 2, 9]
def baseStart_4078466 : Nat := 118140960795 + 4078466 * 2 ^ 59
def prefixEnd_4078466 : Nat := 4983230072969 + 3 ^ 40 * 4078466 * 2
def baseEnd_4078466 : Nat := 17236324205927121125255

theorem tailTrace_4078466 : CollatzResearch.WordTrace tailWord_4078466 prefixEnd_4078466 17236324205927121125255 := by
  unfold tailWord_4078466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37188468910605425845751813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99169250428281135588671501 37188468910605425845751813)
  ·
    refine ⟨6972837920738517346078465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37188468910605425845751813 6972837920738517346078465)
    ·
      refine ⟨5229628440553888009558849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6972837920738517346078465 5229628440553888009558849)
      ·
        refine ⟨3922221330415416007169137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5229628440553888009558849 3922221330415416007169137)
        ·
          refine ⟨2941665997811562005376853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3922221330415416007169137 2941665997811562005376853)
          ·
            refine ⟨17236324205927121125255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2941665997811562005376853 17236324205927121125255)
            ·
              rfl

theorem cell22_4078466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 9].length) (baseStart_4078466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078466 prefixEnd_4078466 := by exact prefixLift 4078466
  have htrace : WordTrace (prefixWord ++ tailWord_4078466) baseStart_4078466 baseEnd_4078466 := by
    simpa [prefixWord, tailWord_4078466, baseEnd_4078466] using wordTrace_append hprefix tailTrace_4078466
  have hstable : (prefixWord ++ tailWord_4078466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078466).length < 2 ^ (prefixWord ++ tailWord_4078466).sum := by decide
  have hdescent : baseEnd_4078466 < baseStart_4078466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078539 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 4]
def baseStart_4078539 : Nat := 118140960795 + 4078539 * 2 ^ 59
def prefixEnd_4078539 : Nat := 4983230072969 + 3 ^ 40 * 4078539 * 2
def baseEnd_4078539 : Nat := 465389083357316318023477

theorem tailTrace_4078539 : CollatzResearch.WordTrace tailWord_4078539 prefixEnd_4078539 465389083357316318023477 := by
  unfold tailWord_4078539
  simp only [CollatzResearch.WordTrace]
  refine ⟨148756538171157236850414671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99171025447438157900276447 148756538171157236850414671)
  ·
    refine ⟨223134807256735855275622007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148756538171157236850414671 223134807256735855275622007)
    ·
      refine ⟨334702210885103782913433011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223134807256735855275622007 334702210885103782913433011)
      ·
        refine ⟨502053316327655674370149517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334702210885103782913433011 502053316327655674370149517)
        ·
          refine ⟨188269993622870877888806069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502053316327655674370149517 188269993622870877888806069)
          ·
            refine ⟨17650311902144144802075569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188269993622870877888806069 17650311902144144802075569)
            ·
              refine ⟨13237733926608108601556677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17650311902144144802075569 13237733926608108601556677)
              ·
                refine ⟨2482075111239020362791877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13237733926608108601556677 2482075111239020362791877)
                ·
                  refine ⟨465389083357316318023477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482075111239020362791877 465389083357316318023477)
                  ·
                    rfl

theorem cell22_4078539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 4].length) (baseStart_4078539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078539 prefixEnd_4078539 := by exact prefixLift 4078539
  have htrace : WordTrace (prefixWord ++ tailWord_4078539) baseStart_4078539 baseEnd_4078539 := by
    simpa [prefixWord, tailWord_4078539, baseEnd_4078539] using wordTrace_append hprefix tailTrace_4078539
  have hstable : (prefixWord ++ tailWord_4078539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078539).length < 2 ^ (prefixWord ++ tailWord_4078539).sum := by decide
  have hdescent : baseEnd_4078539 < baseStart_4078539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078552 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_4078552 : Nat := 118140960795 + 4078552 * 2 ^ 59
def prefixEnd_4078552 : Nat := 4983230072969 + 3 ^ 40 * 4078552 * 2
def baseEnd_4078552 : Nat := 1396171700237621253495391

theorem tailTrace_4078552 : CollatzResearch.WordTrace tailWord_4078552 prefixEnd_4078552 1396171700237621253495391 := by
  unfold tailWord_4078552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74378506160055070035318955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99171341546740093380425273 74378506160055070035318955)
  ·
    refine ⟨111567759240082605052978433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74378506160055070035318955 111567759240082605052978433)
    ·
      refine ⟨83675819430061953789733825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111567759240082605052978433 83675819430061953789733825)
      ·
        refine ⟨62756864572546465342300369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83675819430061953789733825 62756864572546465342300369)
        ·
          refine ⟨47067648429409849006725277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62756864572546465342300369 47067648429409849006725277)
          ·
            refine ⟨17650368161028693377521979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47067648429409849006725277 17650368161028693377521979)
            ·
              refine ⟨26475552241543040066282969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17650368161028693377521979 26475552241543040066282969)
              ·
                refine ⟨19856664181157280049712227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26475552241543040066282969 19856664181157280049712227)
                ·
                  refine ⟨29784996271735920074568341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19856664181157280049712227 29784996271735920074568341)
                  ·
                    refine ⟨1396171700237621253495391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29784996271735920074568341 1396171700237621253495391)
                    ·
                      rfl

theorem cell22_4078552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_4078552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078552 prefixEnd_4078552 := by exact prefixLift 4078552
  have htrace : WordTrace (prefixWord ++ tailWord_4078552) baseStart_4078552 baseEnd_4078552 := by
    simpa [prefixWord, tailWord_4078552, baseEnd_4078552] using wordTrace_append hprefix tailTrace_4078552
  have hstable : (prefixWord ++ tailWord_4078552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078552).length < 2 ^ (prefixWord ++ tailWord_4078552).sum := by decide
  have hdescent : baseEnd_4078552 < baseStart_4078552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078554 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_4078554 : Nat := 118140960795 + 4078554 * 2 ^ 59
def prefixEnd_4078554 : Nat := 4983230072969 + 3 ^ 40 * 4078554 * 2
def baseEnd_4078554 : Nat := 1396172384878493914945385

theorem tailTrace_4078554 : CollatzResearch.WordTrace tailWord_4078554 prefixEnd_4078554 1396172384878493914945385 := by
  unfold tailWord_4078554
  simp only [CollatzResearch.WordTrace]
  refine ⟨37189271316525723603052679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99171390177401929608140477 37189271316525723603052679)
  ·
    refine ⟨55783906974788585404579019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37189271316525723603052679 55783906974788585404579019)
    ·
      refine ⟨83675860462182878106868529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55783906974788585404579019 83675860462182878106868529)
      ·
        refine ⟨62756895346637158580151397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83675860462182878106868529 62756895346637158580151397)
        ·
          refine ⟨11766917877494467233778387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62756895346637158580151397 11766917877494467233778387)
          ·
            refine ⟨17650376816241700850667581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766917877494467233778387 17650376816241700850667581)
            ·
              refine ⟨6618891306090637819000343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17650376816241700850667581 6618891306090637819000343)
              ·
                refine ⟨9928336959135956728500515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6618891306090637819000343 9928336959135956728500515)
                ·
                  refine ⟨14892505438703935092750773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928336959135956728500515 14892505438703935092750773)
                  ·
                    refine ⟨1396172384878493914945385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14892505438703935092750773 1396172384878493914945385)
                    ·
                      rfl

theorem cell22_4078554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_4078554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078554 prefixEnd_4078554 := by exact prefixLift 4078554
  have htrace : WordTrace (prefixWord ++ tailWord_4078554) baseStart_4078554 baseEnd_4078554 := by
    simpa [prefixWord, tailWord_4078554, baseEnd_4078554] using wordTrace_append hprefix tailTrace_4078554
  have hstable : (prefixWord ++ tailWord_4078554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078554).length < 2 ^ (prefixWord ++ tailWord_4078554).sum := by decide
  have hdescent : baseEnd_4078554 < baseStart_4078554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078590 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4078590 : Nat := 118140960795 + 4078590 * 2 ^ 59
def prefixEnd_4078590 : Nat := 4983230072969 + 3 ^ 40 * 4078590 * 2
def baseEnd_4078590 : Nat := 465394902804733940348425

theorem tailTrace_4078590 : CollatzResearch.WordTrace tailWord_4078590 prefixEnd_4078590 465394902804733940348425 := by
  unfold tailWord_4078590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18594799786746559070065153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99172265529314981707014149 18594799786746559070065153)
  ·
    refine ⟨13946099840059919302548865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18594799786746559070065153 13946099840059919302548865)
    ·
      refine ⟨10459574880044939476911649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13946099840059919302548865 10459574880044939476911649)
      ·
        refine ⟨7844681160033704607683737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10459574880044939476911649 7844681160033704607683737)
        ·
          refine ⟨5883510870025278455762803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7844681160033704607683737 5883510870025278455762803)
          ·
            refine ⟨8825266305037917683644205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883510870025278455762803 8825266305037917683644205)
            ·
              refine ⟨3309474864389219131366577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8825266305037917683644205 3309474864389219131366577)
              ·
                refine ⟨2482106148291914348524933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309474864389219131366577 2482106148291914348524933)
                ·
                  refine ⟨465394902804733940348425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482106148291914348524933 465394902804733940348425)
                  ·
                    rfl

theorem cell22_4078590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4078590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078590 prefixEnd_4078590 := by exact prefixLift 4078590
  have htrace : WordTrace (prefixWord ++ tailWord_4078590) baseStart_4078590 baseEnd_4078590 := by
    simpa [prefixWord, tailWord_4078590, baseEnd_4078590] using wordTrace_append hprefix tailTrace_4078590
  have hstable : (prefixWord ++ tailWord_4078590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078590).length < 2 ^ (prefixWord ++ tailWord_4078590).sum := by decide
  have hdescent : baseEnd_4078590 < baseStart_4078590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078597 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_4078597 : Nat := 118140960795 + 4078597 * 2 ^ 59
def prefixEnd_4078597 : Nat := 4983230072969 + 3 ^ 40 * 4078597 * 2
def baseEnd_4078597 : Nat := 1396187104657256136120253

theorem tailTrace_4078597 : CollatzResearch.WordTrace tailWord_4078597 prefixEnd_4078597 1396187104657256136120253 := by
  unfold tailWord_4078597
  simp only [CollatzResearch.WordTrace]
  refine ⟨148758653604947112756026045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99172435736631408504017363 148758653604947112756026045)
  ·
    refine ⟨55784495101855167283509767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148758653604947112756026045 55784495101855167283509767)
    ·
      refine ⟨83676742652782750925264651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55784495101855167283509767 83676742652782750925264651)
      ·
        refine ⟨125515113979174126387896977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83676742652782750925264651 125515113979174126387896977)
        ·
          refine ⟨94136335484380594790922733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125515113979174126387896977 94136335484380594790922733)
          ·
            refine ⟨35301125806642723046596025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94136335484380594790922733 35301125806642723046596025)
            ·
              refine ⟨26475844354982042284947019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35301125806642723046596025 26475844354982042284947019)
              ·
                refine ⟨39713766532473063427420529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26475844354982042284947019 39713766532473063427420529)
                ·
                  refine ⟨29785324899354797570565397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39713766532473063427420529 29785324899354797570565397)
                  ·
                    refine ⟨1396187104657256136120253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29785324899354797570565397 1396187104657256136120253)
                    ·
                      rfl

theorem cell22_4078597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_4078597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078597 prefixEnd_4078597 := by exact prefixLift 4078597
  have htrace : WordTrace (prefixWord ++ tailWord_4078597) baseStart_4078597 baseEnd_4078597 := by
    simpa [prefixWord, tailWord_4078597, baseEnd_4078597] using wordTrace_append hprefix tailTrace_4078597
  have hstable : (prefixWord ++ tailWord_4078597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078597).length < 2 ^ (prefixWord ++ tailWord_4078597).sum := by decide
  have hdescent : baseEnd_4078597 < baseStart_4078597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078646 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_4078646 : Nat := 118140960795 + 4078646 * 2 ^ 59
def prefixEnd_4078646 : Nat := 4983230072969 + 3 ^ 40 * 4078646 * 2
def baseEnd_4078646 : Nat := 465401292786212113881701

theorem tailTrace_4078646 : CollatzResearch.WordTrace tailWord_4078646 prefixEnd_4078646 465401292786212113881701 := by
  unfold tailWord_4078646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297527548860599632784987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99173627187846396083039861 9297527548860599632784987)
  ·
    refine ⟨13946291323290899449177481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9297527548860599632784987 13946291323290899449177481)
    ·
      refine ⟨10459718492468174586883111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13946291323290899449177481 10459718492468174586883111)
      ·
        refine ⟨15689577738702261880324667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10459718492468174586883111 15689577738702261880324667)
        ·
          refine ⟨23534366608053392820487001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15689577738702261880324667 23534366608053392820487001)
          ·
            refine ⟨17650774956040044615365251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23534366608053392820487001 17650774956040044615365251)
            ·
              refine ⟨26476162434060066923047877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17650774956040044615365251 26476162434060066923047877)
              ·
                refine ⟨4964280456386262548071477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26476162434060066923047877 4964280456386262548071477)
                ·
                  refine ⟨465401292786212113881701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4964280456386262548071477 465401292786212113881701)
                  ·
                    rfl

theorem cell22_4078646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_4078646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078646 prefixEnd_4078646 := by exact prefixLift 4078646
  have htrace : WordTrace (prefixWord ++ tailWord_4078646) baseStart_4078646 baseEnd_4078646 := by
    simpa [prefixWord, tailWord_4078646, baseEnd_4078646] using wordTrace_append hprefix tailTrace_4078646
  have hstable : (prefixWord ++ tailWord_4078646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078646).length < 2 ^ (prefixWord ++ tailWord_4078646).sum := by decide
  have hdescent : baseEnd_4078646 < baseStart_4078646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078674 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_4078674 : Nat := 118140960795 + 4078674 * 2 ^ 59
def prefixEnd_4078674 : Nat := 4983230072969 + 3 ^ 40 * 4078674 * 2
def baseEnd_4078674 : Nat := 465404487776951200648339

theorem tailTrace_4078674 : CollatzResearch.WordTrace tailWord_4078674 prefixEnd_4078674 465404487776951200648339 := by
  unfold tailWord_4078674
  simp only [CollatzResearch.WordTrace]
  refine ⟨37190365506417038726644769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99174308017112103271052717 37190365506417038726644769)
  ·
    refine ⟨27892774129812779044983577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37190365506417038726644769 27892774129812779044983577)
    ·
      refine ⟨20919580597359584283737683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27892774129812779044983577 20919580597359584283737683)
      ·
        refine ⟨31379370896039376425606525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20919580597359584283737683 31379370896039376425606525)
        ·
          refine ⟨11767264086014766159602447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31379370896039376425606525 11767264086014766159602447)
          ·
            refine ⟨17650896129022149239403671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11767264086014766159602447 17650896129022149239403671)
            ·
              refine ⟨26476344193533223859105507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17650896129022149239403671 26476344193533223859105507)
              ·
                refine ⟨39714516290299835788658261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26476344193533223859105507 39714516290299835788658261)
                ·
                  refine ⟨465404487776951200648339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39714516290299835788658261 465404487776951200648339)
                  ·
                    rfl

theorem cell22_4078674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_4078674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078674 prefixEnd_4078674 := by exact prefixLift 4078674
  have htrace : WordTrace (prefixWord ++ tailWord_4078674) baseStart_4078674 baseEnd_4078674 := by
    simpa [prefixWord, tailWord_4078674, baseEnd_4078674] using wordTrace_append hprefix tailTrace_4078674
  have hstable : (prefixWord ++ tailWord_4078674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078674).length < 2 ^ (prefixWord ++ tailWord_4078674).sum := by decide
  have hdescent : baseEnd_4078674 < baseStart_4078674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078689 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_4078689 : Nat := 118140960795 + 4078689 * 2 ^ 59
def prefixEnd_4078689 : Nat := 4983230072969 + 3 ^ 40 * 4078689 * 2
def baseEnd_4078689 : Nat := 1396218598137398562819971

theorem tailTrace_4078689 : CollatzResearch.WordTrace tailWord_4078689 prefixEnd_4078689 1396218598137398562819971 := by
  unfold tailWord_4078689
  simp only [CollatzResearch.WordTrace]
  refine ⟨148762009120613812468375121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99174672747075874978916747 148762009120613812468375121)
  ·
    refine ⟨111571506840460359351281341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148762009120613812468375121 111571506840460359351281341)
    ·
      refine ⟨41839315065172634756730503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111571506840460359351281341 41839315065172634756730503)
      ·
        refine ⟨62758972597758952135095755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41839315065172634756730503 62758972597758952135095755)
        ·
          refine ⟨94138458896638428202643633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62758972597758952135095755 94138458896638428202643633)
          ·
            refine ⟨70603844172478821151982725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94138458896638428202643633 70603844172478821151982725)
            ·
              refine ⟨13238220782339778965996761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70603844172478821151982725 13238220782339778965996761)
              ·
                refine ⟨9928665586754834224497571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13238220782339778965996761 9928665586754834224497571)
                ·
                  refine ⟨14892998380132251336746357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928665586754834224497571 14892998380132251336746357)
                  ·
                    refine ⟨1396218598137398562819971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14892998380132251336746357 1396218598137398562819971)
                    ·
                      rfl

theorem cell22_4078689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_4078689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078689 prefixEnd_4078689 := by exact prefixLift 4078689
  have htrace : WordTrace (prefixWord ++ tailWord_4078689) baseStart_4078689 baseEnd_4078689 := by
    simpa [prefixWord, tailWord_4078689, baseEnd_4078689] using wordTrace_append hprefix tailTrace_4078689
  have hstable : (prefixWord ++ tailWord_4078689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078689).length < 2 ^ (prefixWord ++ tailWord_4078689).sum := by decide
  have hdescent : baseEnd_4078689 < baseStart_4078689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078704 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_4078704 : Nat := 118140960795 + 4078704 * 2 ^ 59
def prefixEnd_4078704 : Nat := 4983230072969 + 3 ^ 40 * 4078704 * 2
def baseEnd_4078704 : Nat := 1396223732943943523694925

theorem tailTrace_4078704 : CollatzResearch.WordTrace tailWord_4078704 prefixEnd_4078704 1396223732943943523694925 := by
  unfold tailWord_4078704
  simp only [CollatzResearch.WordTrace]
  refine ⟨74381278107779735015085583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99175037477039646686780777 74381278107779735015085583)
  ·
    refine ⟨111571917161669602522628375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74381278107779735015085583 111571917161669602522628375)
    ·
      refine ⟨167357875742504403783942563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111571917161669602522628375 167357875742504403783942563)
      ·
        refine ⟨251036813613756605675913845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167357875742504403783942563 251036813613756605675913845)
        ·
          refine ⟨23534701276289681782116923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251036813613756605675913845 23534701276289681782116923)
          ·
            refine ⟨35302051914434522673175385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23534701276289681782116923 35302051914434522673175385)
            ·
              refine ⟨26476538935825892004881539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35302051914434522673175385 26476538935825892004881539)
              ·
                refine ⟨39714808403738838007322309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26476538935825892004881539 39714808403738838007322309)
                ·
                  refine ⟨7446526575701032126372933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39714808403738838007322309 7446526575701032126372933)
                  ·
                    refine ⟨1396223732943943523694925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7446526575701032126372933 1396223732943943523694925)
                    ·
                      rfl

theorem cell22_4078704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_4078704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078704 prefixEnd_4078704 := by exact prefixLift 4078704
  have htrace : WordTrace (prefixWord ++ tailWord_4078704) baseStart_4078704 baseEnd_4078704 := by
    simpa [prefixWord, tailWord_4078704, baseEnd_4078704] using wordTrace_append hprefix tailTrace_4078704
  have hstable : (prefixWord ++ tailWord_4078704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078704).length < 2 ^ (prefixWord ++ tailWord_4078704).sum := by decide
  have hdescent : baseEnd_4078704 < baseStart_4078704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078706 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_4078706 : Nat := 118140960795 + 4078706 * 2 ^ 59
def prefixEnd_4078706 : Nat := 4983230072969 + 3 ^ 40 * 4078706 * 2
def baseEnd_4078706 : Nat := 1396224417584816185144919

theorem tailTrace_4078706 : CollatzResearch.WordTrace tailWord_4078706 prefixEnd_4078706 1396224417584816185144919 := by
  unfold tailWord_4078706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37190657290388056092935993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99175086107701482914495981 37190657290388056092935993)
  ·
    refine ⟨27892992967791042069701995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37190657290388056092935993 27892992967791042069701995)
    ·
      refine ⟨41839489451686563104552993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27892992967791042069701995 41839489451686563104552993)
      ·
        refine ⟨31379617088764922328414745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41839489451686563104552993 31379617088764922328414745)
        ·
          refine ⟨23534712816573691746311059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31379617088764922328414745 23534712816573691746311059)
          ·
            refine ⟨35302069224860537619466589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23534712816573691746311059 35302069224860537619466589)
            ·
              refine ⟨13238275959322701607299971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35302069224860537619466589 13238275959322701607299971)
              ·
                refine ⟨19857413938984052410949957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13238275959322701607299971 19857413938984052410949957)
                ·
                  refine ⟨3723265113559509827053117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19857413938984052410949957 3723265113559509827053117)
                  ·
                    refine ⟨1396224417584816185144919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723265113559509827053117 1396224417584816185144919)
                    ·
                      rfl

theorem cell22_4078706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_4078706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078706 prefixEnd_4078706 := by exact prefixLift 4078706
  have htrace : WordTrace (prefixWord ++ tailWord_4078706) baseStart_4078706 baseEnd_4078706 := by
    simpa [prefixWord, tailWord_4078706, baseEnd_4078706] using wordTrace_append hprefix tailTrace_4078706
  have hstable : (prefixWord ++ tailWord_4078706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078706).length < 2 ^ (prefixWord ++ tailWord_4078706).sum := by decide
  have hdescent : baseEnd_4078706 < baseStart_4078706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078723 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 2, 3]
def baseStart_4078723 : Nat := 118140960795 + 4078723 * 2 ^ 59
def prefixEnd_4078723 : Nat := 4983230072969 + 3 ^ 40 * 4078723 * 2
def baseEnd_4078723 : Nat := 1396230237032233807469867

theorem tailTrace_4078723 : CollatzResearch.WordTrace tailWord_4078723 prefixEnd_4078723 1396230237032233807469867 := by
  unfold tailWord_4078723
  simp only [CollatzResearch.WordTrace]
  refine ⟨148763249202490636275112823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99175499468327090850075215 148763249202490636275112823)
  ·
    refine ⟨223144873803735954412669235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148763249202490636275112823 223144873803735954412669235)
    ·
      refine ⟨334717310705603931619003853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223144873803735954412669235 334717310705603931619003853)
      ·
        refine ⟨125518991514601474357126445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334717310705603931619003853 125518991514601474357126445)
        ·
          refine ⟨47069621817975552883922417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125518991514601474357126445 47069621817975552883922417)
          ·
            refine ⟨35302216363481664662941813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47069621817975552883922417 35302216363481664662941813)
            ·
              refine ⟨3309582784076406062150795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35302216363481664662941813 3309582784076406062150795)
              ·
                refine ⟨4964374176114609093226193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309582784076406062150795 4964374176114609093226193)
                ·
                  refine ⟨3723280632085956819919645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964374176114609093226193 3723280632085956819919645)
                  ·
                    refine ⟨1396230237032233807469867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723280632085956819919645 1396230237032233807469867)
                    ·
                      rfl

theorem cell22_4078723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 3].length) (baseStart_4078723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078723 prefixEnd_4078723 := by exact prefixLift 4078723
  have htrace : WordTrace (prefixWord ++ tailWord_4078723) baseStart_4078723 baseEnd_4078723 := by
    simpa [prefixWord, tailWord_4078723, baseEnd_4078723] using wordTrace_append hprefix tailTrace_4078723
  have hstable : (prefixWord ++ tailWord_4078723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078723).length < 2 ^ (prefixWord ++ tailWord_4078723).sum := by decide
  have hdescent : baseEnd_4078723 < baseStart_4078723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078839 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4078839 : Nat := 118140960795 + 4078839 * 2 ^ 59
def prefixEnd_4078839 : Nat := 4983230072969 + 3 ^ 40 * 4078839 * 2
def baseEnd_4078839 : Nat := 1396269946202848171569511

theorem tailTrace_4078839 : CollatzResearch.WordTrace tailWord_4078839 prefixEnd_4078839 1396269946202848171569511 := by
  unfold tailWord_4078839
  simp only [CollatzResearch.WordTrace]
  refine ⟨148767480070070388086335571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99178320046713592057557047 148767480070070388086335571)
  ·
    refine ⟨223151220105105582129503357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148767480070070388086335571 223151220105105582129503357)
    ·
      refine ⟨83681707539414593298563759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223151220105105582129503357 83681707539414593298563759)
      ·
        refine ⟨125522561309121889947845639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83681707539414593298563759 125522561309121889947845639)
        ·
          refine ⟨188283841963682834921768459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125522561309121889947845639 188283841963682834921768459)
          ·
            refine ⟨282425762945524252382652689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188283841963682834921768459 282425762945524252382652689)
            ·
              refine ⟨211819322209143189286989517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282425762945524252382652689 211819322209143189286989517)
              ·
                refine ⟨79432245828428695982621069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211819322209143189286989517 79432245828428695982621069)
                ·
                  refine ⟨29787092185660760993482901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79432245828428695982621069 29787092185660760993482901)
                  ·
                    refine ⟨1396269946202848171569511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29787092185660760993482901 1396269946202848171569511)
                    ·
                      rfl

theorem cell22_4078839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4078839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078839 prefixEnd_4078839 := by exact prefixLift 4078839
  have htrace : WordTrace (prefixWord ++ tailWord_4078839) baseStart_4078839 baseEnd_4078839 := by
    simpa [prefixWord, tailWord_4078839, baseEnd_4078839] using wordTrace_append hprefix tailTrace_4078839
  have hstable : (prefixWord ++ tailWord_4078839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078839).length < 2 ^ (prefixWord ++ tailWord_4078839).sum := by decide
  have hdescent : baseEnd_4078839 < baseStart_4078839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078841 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_4078841 : Nat := 118140960795 + 4078841 * 2 ^ 59
def prefixEnd_4078841 : Nat := 4983230072969 + 3 ^ 40 * 4078841 * 2
def baseEnd_4078841 : Nat := 1396270630843720833019505

theorem tailTrace_4078841 : CollatzResearch.WordTrace tailWord_4078841 prefixEnd_4078841 1396270630843720833019505 := by
  unfold tailWord_4078841
  simp only [CollatzResearch.WordTrace]
  refine ⟨148767553016063142427908377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99178368677375428285272251 148767553016063142427908377)
  ·
    refine ⟨111575664762047356820931283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148767553016063142427908377 111575664762047356820931283)
    ·
      refine ⟨167363497143071035231396925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111575664762047356820931283 167363497143071035231396925)
      ·
        refine ⟨62761311428651638211773847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167363497143071035231396925 62761311428651638211773847)
        ·
          refine ⟨94141967142977457317660771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62761311428651638211773847 94141967142977457317660771)
          ·
            refine ⟨141212950714466185976491157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94141967142977457317660771 141212950714466185976491157)
            ·
              refine ⟨6619357064740602467648023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141212950714466185976491157 6619357064740602467648023)
              ·
                refine ⟨9929035597110903701472035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619357064740602467648023 9929035597110903701472035)
                ·
                  refine ⟨14893553395666355552208053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9929035597110903701472035 14893553395666355552208053)
                  ·
                    refine ⟨1396270630843720833019505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14893553395666355552208053 1396270630843720833019505)
                    ·
                      rfl

theorem cell22_4078841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_4078841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078841 prefixEnd_4078841 := by exact prefixLift 4078841
  have htrace : WordTrace (prefixWord ++ tailWord_4078841) baseStart_4078841 baseEnd_4078841 := by
    simpa [prefixWord, tailWord_4078841, baseEnd_4078841] using wordTrace_append hprefix tailTrace_4078841
  have hstable : (prefixWord ++ tailWord_4078841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078841).length < 2 ^ (prefixWord ++ tailWord_4078841).sum := by decide
  have hdescent : baseEnd_4078841 < baseStart_4078841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078905 : List Nat := [1, 2, 1, 6, 2, 2, 2, 6]
def baseStart_4078905 : Nat := 118140960795 + 4078905 * 2 ^ 59
def prefixEnd_4078905 : Nat := 4983230072969 + 3 ^ 40 * 4078905 * 2
def baseEnd_4078905 : Nat := 155143615483516222157701

theorem tailTrace_4078905 : CollatzResearch.WordTrace tailWord_4078905 prefixEnd_4078905 155143615483516222157701 := by
  unfold tailWord_4078905
  simp only [CollatzResearch.WordTrace]
  refine ⟨148769887287831281358238169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99179924858554187572158779 148769887287831281358238169)
  ·
    refine ⟨111577415465873461018678627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148769887287831281358238169 111577415465873461018678627)
    ·
      refine ⟨167366123198810191528017941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111577415465873461018678627 167366123198810191528017941)
      ·
        refine ⟨7845287024944227727875841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167366123198810191528017941 7845287024944227727875841)
        ·
          refine ⟨5883965268708170795906881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845287024944227727875841 5883965268708170795906881)
          ·
            refine ⟨4412973951531128096930161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5883965268708170795906881 4412973951531128096930161)
            ·
              refine ⟨3309730463648346072697621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4412973951531128096930161 3309730463648346072697621)
              ·
                refine ⟨155143615483516222157701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3309730463648346072697621 155143615483516222157701)
                ·
                  rfl

theorem cell22_4078905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 6].length) (baseStart_4078905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078905 prefixEnd_4078905 := by exact prefixLift 4078905
  have htrace : WordTrace (prefixWord ++ tailWord_4078905) baseStart_4078905 baseEnd_4078905 := by
    simpa [prefixWord, tailWord_4078905, baseEnd_4078905] using wordTrace_append hprefix tailTrace_4078905
  have hstable : (prefixWord ++ tailWord_4078905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078905).length < 2 ^ (prefixWord ++ tailWord_4078905).sum := by decide
  have hdescent : baseEnd_4078905 < baseStart_4078905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078961 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 6]
def baseStart_4078961 : Nat := 118140960795 + 4078961 * 2 ^ 59
def prefixEnd_4078961 : Nat := 4983230072969 + 3 ^ 40 * 4078961 * 2
def baseEnd_4078961 : Nat := 465437236432026840006379

theorem tailTrace_4078961 : CollatzResearch.WordTrace tailWord_4078961 prefixEnd_4078961 465437236432026840006379 := by
  unfold tailWord_4078961
  simp only [CollatzResearch.WordTrace]
  refine ⟨148771929775628402922276737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99181286517085601948184491 148771929775628402922276737)
  ·
    refine ⟨111578947331721302191707553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148771929775628402922276737 111578947331721302191707553)
    ·
      refine ⟨83684210498790976643780665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111578947331721302191707553 83684210498790976643780665)
      ·
        refine ⟨62763157874093232482835499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83684210498790976643780665 62763157874093232482835499)
        ·
          refine ⟨94144736811139848724253249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62763157874093232482835499 94144736811139848724253249)
          ·
            refine ⟨70608552608354886543189937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94144736811139848724253249 70608552608354886543189937)
            ·
              refine ⟨52956414456266164907392453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70608552608354886543189937 52956414456266164907392453)
              ·
                refine ⟨9929327710549905920136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52956414456266164907392453 9929327710549905920136085)
                ·
                  refine ⟨465437236432026840006379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9929327710549905920136085 465437236432026840006379)
                  ·
                    rfl

theorem cell22_4078961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_4078961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4078961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4078961 prefixEnd_4078961 := by exact prefixLift 4078961
  have htrace : WordTrace (prefixWord ++ tailWord_4078961) baseStart_4078961 baseEnd_4078961 := by
    simpa [prefixWord, tailWord_4078961, baseEnd_4078961] using wordTrace_append hprefix tailTrace_4078961
  have hstable : (prefixWord ++ tailWord_4078961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078961).length < 2 ^ (prefixWord ++ tailWord_4078961).sum := by decide
  have hdescent : baseEnd_4078961 < baseStart_4078961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079010 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_4079010 : Nat := 118140960795 + 4079010 * 2 ^ 59
def prefixEnd_4079010 : Nat := 4983230072969 + 3 ^ 40 * 4079010 * 2
def baseEnd_4079010 : Nat := 1396328482997460725543987

theorem tailTrace_4079010 : CollatzResearch.WordTrace tailWord_4079010 prefixEnd_4079010 1396328482997460725543987 := by
  unfold tailWord_4079010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37193429238112721072702621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99182477968300589527206989 37193429238112721072702621)
  ·
    refine ⟨13947535964292270402263483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37193429238112721072702621 13947535964292270402263483)
    ·
      refine ⟨20921303946438405603395225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947535964292270402263483 20921303946438405603395225)
      ·
        refine ⟨15690977959828804202546419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20921303946438405603395225 15690977959828804202546419)
        ·
          refine ⟨23536466939743206303819629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15690977959828804202546419 23536466939743206303819629)
          ·
            refine ⟨8826175102403702363932361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23536466939743206303819629 8826175102403702363932361)
            ·
              refine ⟨6619631326802776772949271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826175102403702363932361 6619631326802776772949271)
              ·
                refine ⟨9929446990204165159423907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6619631326802776772949271 9929446990204165159423907)
                ·
                  refine ⟨14894170485306247739135861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9929446990204165159423907 14894170485306247739135861)
                  ·
                    refine ⟨1396328482997460725543987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14894170485306247739135861 1396328482997460725543987)
                    ·
                      rfl

theorem cell22_4079010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_4079010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079010 prefixEnd_4079010 := by exact prefixLift 4079010
  have htrace : WordTrace (prefixWord ++ tailWord_4079010) baseStart_4079010 baseEnd_4079010 := by
    simpa [prefixWord, tailWord_4079010, baseEnd_4079010] using wordTrace_append hprefix tailTrace_4079010
  have hstable : (prefixWord ++ tailWord_4079010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079010).length < 2 ^ (prefixWord ++ tailWord_4079010).sum := by decide
  have hdescent : baseEnd_4079010 < baseStart_4079010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079044 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4079044 : Nat := 118140960795 + 4079044 * 2 ^ 59
def prefixEnd_4079044 : Nat := 4983230072969 + 3 ^ 40 * 4079044 * 2
def baseEnd_4079044 : Nat := 1396340121892295970193883

theorem tailTrace_4079044 : CollatzResearch.WordTrace tailWord_4079044 prefixEnd_4079044 1396340121892295970193883 := by
  unfold tailWord_4079044
  simp only [CollatzResearch.WordTrace]
  refine ⟨74387478517163854048774093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99183304689551805398365457 74387478517163854048774093)
  ·
    refine ⟨27895304443936445268290285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74387478517163854048774093 27895304443936445268290285)
    ·
      refine ⟨10460739166476166975608857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27895304443936445268290285 10460739166476166975608857)
      ·
        refine ⟨7845554374857125231706643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10460739166476166975608857 7845554374857125231706643)
        ·
          refine ⟨11768331562285687847559965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845554374857125231706643 11768331562285687847559965)
          ·
            refine ⟨4413124335857132942834987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11768331562285687847559965 4413124335857132942834987)
            ·
              refine ⟨6619686503785699414252481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413124335857132942834987 6619686503785699414252481)
              ·
                refine ⟨4964764877839274560689361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619686503785699414252481 4964764877839274560689361)
                ·
                  refine ⟨3723573658379455920517021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964764877839274560689361 3723573658379455920517021)
                  ·
                    refine ⟨1396340121892295970193883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723573658379455920517021 1396340121892295970193883)
                    ·
                      rfl

theorem cell22_4079044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4079044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079044 prefixEnd_4079044 := by exact prefixLift 4079044
  have htrace : WordTrace (prefixWord ++ tailWord_4079044) baseStart_4079044 baseEnd_4079044 := by
    simpa [prefixWord, tailWord_4079044, baseEnd_4079044] using wordTrace_append hprefix tailTrace_4079044
  have hstable : (prefixWord ++ tailWord_4079044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079044).length < 2 ^ (prefixWord ++ tailWord_4079044).sum := by decide
  have hdescent : baseEnd_4079044 < baseStart_4079044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079089 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 1, 3]
def baseStart_4079089 : Nat := 118140960795 + 4079089 * 2 ^ 59
def prefixEnd_4079089 : Nat := 4983230072969 + 3 ^ 40 * 4079089 * 2
def baseEnd_4079089 : Nat := 1396355526311930852818745

theorem tailTrace_4079089 : CollatzResearch.WordTrace tailWord_4079089 prefixEnd_4079089 1396355526311930852818745 := by
  unfold tailWord_4079089
  simp only [CollatzResearch.WordTrace]
  refine ⟨148776598319164680782936321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99184398879443120521957547 148776598319164680782936321)
  ·
    refine ⟨111582448739373510587202241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148776598319164680782936321 111582448739373510587202241)
    ·
      refine ⟨83686836554530132940401681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111582448739373510587202241 83686836554530132940401681)
      ·
        refine ⟨62765127415897599705301261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83686836554530132940401681 62765127415897599705301261)
        ·
          refine ⟨23536922780961599889487973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62765127415897599705301261 23536922780961599889487973)
          ·
            refine ⟨4413173021430299979278995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23536922780961599889487973 4413173021430299979278995)
            ·
              refine ⟨6619759532145449968918493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413173021430299979278995 6619759532145449968918493)
              ·
                refine ⟨2482409824554543738344435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6619759532145449968918493 2482409824554543738344435)
                ·
                  refine ⟨3723614736831815607516653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482409824554543738344435 3723614736831815607516653)
                  ·
                    refine ⟨1396355526311930852818745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723614736831815607516653 1396355526311930852818745)
                    ·
                      rfl

theorem cell22_4079089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_4079089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079089 prefixEnd_4079089 := by exact prefixLift 4079089
  have htrace : WordTrace (prefixWord ++ tailWord_4079089) baseStart_4079089 baseEnd_4079089 := by
    simpa [prefixWord, tailWord_4079089, baseEnd_4079089] using wordTrace_append hprefix tailTrace_4079089
  have hstable : (prefixWord ++ tailWord_4079089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079089).length < 2 ^ (prefixWord ++ tailWord_4079089).sum := by decide
  have hdescent : baseEnd_4079089 < baseStart_4079089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079160 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_4079160 : Nat := 118140960795 + 4079160 * 2 ^ 59
def prefixEnd_4079160 : Nat := 4983230072969 + 3 ^ 40 * 4079160 * 2
def baseEnd_4079160 : Nat := 1396379831062910334293527

theorem tailTrace_4079160 : CollatzResearch.WordTrace tailWord_4079160 prefixEnd_4079160 1396379831062910334293527 := by
  unfold tailWord_4079160
  simp only [CollatzResearch.WordTrace]
  refine ⟨74389593950953729954385467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99186125267938306605847289 74389593950953729954385467)
  ·
    refine ⟨111584390926430594931578201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74389593950953729954385467 111584390926430594931578201)
    ·
      refine ⟨83688293194822946198683651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111584390926430594931578201 83688293194822946198683651)
      ·
        refine ⟨125532439792234419298025477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83688293194822946198683651 125532439792234419298025477)
        ·
          refine ⟨23537332461043953618379777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125532439792234419298025477 23537332461043953618379777)
          ·
            refine ⟨17652999345782965213784833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23537332461043953618379777 17652999345782965213784833)
            ·
              refine ⟨13239749509337223910338625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17652999345782965213784833 13239749509337223910338625)
              ·
                refine ⟨9929812132002917932753969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13239749509337223910338625 9929812132002917932753969)
                ·
                  refine ⟨7447359099002188449565477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9929812132002917932753969 7447359099002188449565477)
                  ·
                    refine ⟨1396379831062910334293527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447359099002188449565477 1396379831062910334293527)
                    ·
                      rfl

theorem cell22_4079160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_4079160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079160 prefixEnd_4079160 := by exact prefixLift 4079160
  have htrace : WordTrace (prefixWord ++ tailWord_4079160) baseStart_4079160 baseEnd_4079160 := by
    simpa [prefixWord, tailWord_4079160, baseEnd_4079160] using wordTrace_append hprefix tailTrace_4079160
  have hstable : (prefixWord ++ tailWord_4079160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079160).length < 2 ^ (prefixWord ++ tailWord_4079160).sum := by decide
  have hdescent : baseEnd_4079160 < baseStart_4079160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079162 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_4079162 : Nat := 118140960795 + 4079162 * 2 ^ 59
def prefixEnd_4079162 : Nat := 4983230072969 + 3 ^ 40 * 4079162 * 2
def baseEnd_4079162 : Nat := 1396380515703782995743521

theorem tailTrace_4079162 : CollatzResearch.WordTrace tailWord_4079162 prefixEnd_4079162 1396380515703782995743521 := by
  unfold tailWord_4079162
  simp only [CollatzResearch.WordTrace]
  refine ⟨37194815211975053562585935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99186173898600142833562493 37194815211975053562585935)
  ·
    refine ⟨55792222817962580343878903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37194815211975053562585935 55792222817962580343878903)
    ·
      refine ⟨83688334226943870515818355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55792222817962580343878903 83688334226943870515818355)
      ·
        refine ⟨125532501340415805773727533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83688334226943870515818355 125532501340415805773727533)
        ·
          refine ⟨47074688002655927165147825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125532501340415805773727533 47074688002655927165147825)
          ·
            refine ⟨35306016001991945373860869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47074688002655927165147825 35306016001991945373860869)
            ·
              refine ⟨6619878000373489757598913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35306016001991945373860869 6619878000373489757598913)
              ·
                refine ⟨4964908500280117318199185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619878000373489757598913 4964908500280117318199185)
                ·
                  refine ⟨3723681375210087988649389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964908500280117318199185 3723681375210087988649389)
                  ·
                    refine ⟨1396380515703782995743521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723681375210087988649389 1396380515703782995743521)
                    ·
                      rfl

theorem cell22_4079162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_4079162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079162 prefixEnd_4079162 := by exact prefixLift 4079162
  have htrace : WordTrace (prefixWord ++ tailWord_4079162) baseStart_4079162 baseEnd_4079162 := by
    simpa [prefixWord, tailWord_4079162, baseEnd_4079162] using wordTrace_append hprefix tailTrace_4079162
  have hstable : (prefixWord ++ tailWord_4079162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079162).length < 2 ^ (prefixWord ++ tailWord_4079162).sum := by decide
  have hdescent : baseEnd_4079162 < baseStart_4079162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079237 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 5]
def baseStart_4079237 : Nat := 118140960795 + 4079237 * 2 ^ 59
def prefixEnd_4079237 : Nat := 4983230072969 + 3 ^ 40 * 4079237 * 2
def baseEnd_4079237 : Nat := 465468729912169266706097

theorem tailTrace_4079237 : CollatzResearch.WordTrace tailWord_4079237 prefixEnd_4079237 465468729912169266706097 := by
  unfold tailWord_4079237
  simp only [CollatzResearch.WordTrace]
  refine ⟨148781996322628502059323965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99187997548419001372882643 148781996322628502059323965)
  ·
    refine ⟨55793248620985688272246487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148781996322628502059323965 55793248620985688272246487)
    ·
      refine ⟨83689872931478532408369731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55793248620985688272246487 83689872931478532408369731)
      ·
        refine ⟨125534809397217798612554597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83689872931478532408369731 125534809397217798612554597)
        ·
          refine ⟨23537776761978337239853987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125534809397217798612554597 23537776761978337239853987)
          ·
            refine ⟨35306665142967505859780981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23537776761978337239853987 35306665142967505859780981)
            ·
              refine ⟨3309999857153203674354467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35306665142967505859780981 3309999857153203674354467)
              ·
                refine ⟨4964999785729805511531701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309999857153203674354467 4964999785729805511531701)
                ·
                  refine ⟨465468729912169266706097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4964999785729805511531701 465468729912169266706097)
                  ·
                    rfl

theorem cell22_4079237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_4079237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079237 prefixEnd_4079237 := by exact prefixLift 4079237
  have htrace : WordTrace (prefixWord ++ tailWord_4079237) baseStart_4079237 baseEnd_4079237 := by
    simpa [prefixWord, tailWord_4079237, baseEnd_4079237] using wordTrace_append hprefix tailTrace_4079237
  have hstable : (prefixWord ++ tailWord_4079237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079237).length < 2 ^ (prefixWord ++ tailWord_4079237).sum := by decide
  have hdescent : baseEnd_4079237 < baseStart_4079237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079282 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_4079282 : Nat := 118140960795 + 4079282 * 2 ^ 59
def prefixEnd_4079282 : Nat := 4983230072969 + 3 ^ 40 * 4079282 * 2
def baseEnd_4079282 : Nat := 465473864718714227581051

theorem tailTrace_4079282 : CollatzResearch.WordTrace tailWord_4079282 prefixEnd_4079282 465473864718714227581051 := by
  unfold tailWord_4079282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37195909401866368686178025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99189091738310316496474733 37195909401866368686178025)
  ·
    refine ⟨27896932051399776514633519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37195909401866368686178025 27896932051399776514633519)
    ·
      refine ⟨41845398077099664771950279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27896932051399776514633519 41845398077099664771950279)
      ·
        refine ⟨62768097115649497157925419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41845398077099664771950279 62768097115649497157925419)
        ·
          refine ⟨94152145673474245736888129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62768097115649497157925419 94152145673474245736888129)
          ·
            refine ⟨70614109255105684302666097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94152145673474245736888129 70614109255105684302666097)
            ·
              refine ⟨52960581941329263226999573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70614109255105684302666097 52960581941329263226999573)
              ·
                refine ⟨2482527278499809213765605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52960581941329263226999573 2482527278499809213765605)
                ·
                  refine ⟨465473864718714227581051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482527278499809213765605 465473864718714227581051)
                  ·
                    rfl

theorem cell22_4079282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_4079282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079282 prefixEnd_4079282 := by exact prefixLift 4079282
  have htrace : WordTrace (prefixWord ++ tailWord_4079282) baseStart_4079282 baseEnd_4079282 := by
    simpa [prefixWord, tailWord_4079282, baseEnd_4079282] using wordTrace_append hprefix tailTrace_4079282
  have hstable : (prefixWord ++ tailWord_4079282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079282).length < 2 ^ (prefixWord ++ tailWord_4079282).sum := by decide
  have hdescent : baseEnd_4079282 < baseStart_4079282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079295 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_4079295 : Nat := 118140960795 + 4079295 * 2 ^ 59
def prefixEnd_4079295 : Nat := 4983230072969 + 3 ^ 40 * 4079295 * 2
def baseEnd_4079295 : Nat := 1396426044321814982168113

theorem tailTrace_4079295 : CollatzResearch.WordTrace tailWord_4079295 prefixEnd_4079295 1396426044321814982168113 := by
  unfold tailWord_4079295
  simp only [CollatzResearch.WordTrace]
  refine ⟨148784111756418377964935339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99189407837612251976623559 148784111756418377964935339)
  ·
    refine ⟨223176167634627566947403009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148784111756418377964935339 223176167634627566947403009)
    ·
      refine ⟨167382125725970675210552257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223176167634627566947403009 167382125725970675210552257)
      ·
        refine ⟨125536594294478006407914193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167382125725970675210552257 125536594294478006407914193)
        ·
          refine ⟨94152445720858504805935645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125536594294478006407914193 94152445720858504805935645)
          ·
            refine ⟨35307167145321939302225867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94152445720858504805935645 35307167145321939302225867)
            ·
              refine ⟨52960750717982908953338801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35307167145321939302225867 52960750717982908953338801)
              ·
                refine ⟨39720563038487181715004101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52960750717982908953338801 39720563038487181715004101)
                ·
                  refine ⟨7447605569716346571563269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39720563038487181715004101 7447605569716346571563269)
                  ·
                    refine ⟨1396426044321814982168113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447605569716346571563269 1396426044321814982168113)
                    ·
                      rfl

theorem cell22_4079295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_4079295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079295 prefixEnd_4079295 := by exact prefixLift 4079295
  have htrace : WordTrace (prefixWord ++ tailWord_4079295) baseStart_4079295 baseEnd_4079295 := by
    simpa [prefixWord, tailWord_4079295, baseEnd_4079295] using wordTrace_append hprefix tailTrace_4079295
  have hstable : (prefixWord ++ tailWord_4079295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079295).length < 2 ^ (prefixWord ++ tailWord_4079295).sum := by decide
  have hdescent : baseEnd_4079295 < baseStart_4079295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079310 : List Nat := [4, 1, 1, 1, 3, 1, 1, 10]
def baseStart_4079310 : Nat := 118140960795 + 4079310 * 2 ^ 59
def prefixEnd_4079310 : Nat := 4983230072969 + 3 ^ 40 * 4079310 * 2
def baseEnd_4079310 : Nat := 155159019903151104782563

theorem tailTrace_4079310 : CollatzResearch.WordTrace tailWord_4079310 prefixEnd_4079310 155159019903151104782563 := by
  unfold tailWord_4079310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598082356420504440841423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99189772567576023684487589 18598082356420504440841423)
  ·
    refine ⟨27897123534630756661262135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598082356420504440841423 27897123534630756661262135)
    ·
      refine ⟨41845685301946134991893203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27897123534630756661262135 41845685301946134991893203)
      ·
        refine ⟨62768527952919202487839805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41845685301946134991893203 62768527952919202487839805)
        ·
          refine ⟨23538197982344700932939927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62768527952919202487839805 23538197982344700932939927)
          ·
            refine ⟨35307296973517051399409891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23538197982344700932939927 35307296973517051399409891)
            ·
              refine ⟨52960945460275577099114837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35307296973517051399409891 52960945460275577099114837)
              ·
                refine ⟨155159019903151104782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52960945460275577099114837 155159019903151104782563)
                ·
                  rfl

theorem cell22_4079310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_4079310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079310 prefixEnd_4079310 := by exact prefixLift 4079310
  have htrace : WordTrace (prefixWord ++ tailWord_4079310) baseStart_4079310 baseEnd_4079310 := by
    simpa [prefixWord, tailWord_4079310, baseEnd_4079310] using wordTrace_append hprefix tailTrace_4079310
  have hstable : (prefixWord ++ tailWord_4079310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079310).length < 2 ^ (prefixWord ++ tailWord_4079310).sum := by decide
  have hdescent : baseEnd_4079310 < baseStart_4079310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079331 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 2, 3]
def baseStart_4079331 : Nat := 118140960795 + 4079331 * 2 ^ 59
def prefixEnd_4079331 : Nat := 4983230072969 + 3 ^ 40 * 4079331 * 2
def baseEnd_4079331 : Nat := 1396438367857522888268003

theorem tailTrace_4079331 : CollatzResearch.WordTrace tailWord_4079331 prefixEnd_4079331 1396438367857522888268003 := by
  unfold tailWord_4079331
  simp only [CollatzResearch.WordTrace]
  refine ⟨148785424784287956113245847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99190283189525304075497231 148785424784287956113245847)
  ·
    refine ⟨223178137176431934169868771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148785424784287956113245847 223178137176431934169868771)
    ·
      refine ⟨334767205764647901254803157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223178137176431934169868771 334767205764647901254803157)
      ·
        refine ⟨7846106385108935185659449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 334767205764647901254803157 7846106385108935185659449)
        ·
          refine ⟨5884579788831701389244587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846106385108935185659449 5884579788831701389244587)
          ·
            refine ⟨8826869683247552083866881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884579788831701389244587 8826869683247552083866881)
            ·
              refine ⟨6620152262435664062900161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826869683247552083866881 6620152262435664062900161)
              ·
                refine ⟨4965114196826748047175121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6620152262435664062900161 4965114196826748047175121)
                ·
                  refine ⟨3723835647620061035381341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965114196826748047175121 3723835647620061035381341)
                  ·
                    refine ⟨1396438367857522888268003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723835647620061035381341 1396438367857522888268003)
                    ·
                      rfl

theorem cell22_4079331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3].length) (baseStart_4079331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079331 prefixEnd_4079331 := by exact prefixLift 4079331
  have htrace : WordTrace (prefixWord ++ tailWord_4079331) baseStart_4079331 baseEnd_4079331 := by
    simpa [prefixWord, tailWord_4079331, baseEnd_4079331] using wordTrace_append hprefix tailTrace_4079331
  have hstable : (prefixWord ++ tailWord_4079331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079331).length < 2 ^ (prefixWord ++ tailWord_4079331).sum := by decide
  have hdescent : baseEnd_4079331 < baseStart_4079331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079340 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_4079340 : Nat := 118140960795 + 4079340 * 2 ^ 59
def prefixEnd_4079340 : Nat := 4983230072969 + 3 ^ 40 * 4079340 * 2
def baseEnd_4079340 : Nat := 1396441448741449864792975

theorem tailTrace_4079340 : CollatzResearch.WordTrace tailWord_4079340 prefixEnd_4079340 1396441448741449864792975 := by
  unfold tailWord_4079340
  simp only [CollatzResearch.WordTrace]
  refine ⟨74392876520627675325161737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99190502027503567100215649 74392876520627675325161737)
  ·
    refine ⟨55794657390470756493871303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74392876520627675325161737 55794657390470756493871303)
    ·
      refine ⟨83691986085706134740806955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55794657390470756493871303 83691986085706134740806955)
      ·
        refine ⟨125537979128559202111210433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83691986085706134740806955 125537979128559202111210433)
        ·
          refine ⟨94153484346419401583407825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125537979128559202111210433 94153484346419401583407825)
          ·
            refine ⟨70615113259814551187555869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94153484346419401583407825 70615113259814551187555869)
            ·
              refine ⟨26480667472430456695333451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70615113259814551187555869 26480667472430456695333451)
              ·
                refine ⟨39721001208645685043000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26480667472430456695333451 39721001208645685043000177)
                ·
                  refine ⟨29790750906484263782250133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39721001208645685043000177 29790750906484263782250133)
                  ·
                    refine ⟨1396441448741449864792975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29790750906484263782250133 1396441448741449864792975)
                    ·
                      rfl

theorem cell22_4079340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_4079340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079340 prefixEnd_4079340 := by exact prefixLift 4079340
  have htrace : WordTrace (prefixWord ++ tailWord_4079340) baseStart_4079340 baseEnd_4079340 := by
    simpa [prefixWord, tailWord_4079340, baseEnd_4079340] using wordTrace_append hprefix tailTrace_4079340
  have hstable : (prefixWord ++ tailWord_4079340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079340).length < 2 ^ (prefixWord ++ tailWord_4079340).sum := by decide
  have hdescent : baseEnd_4079340 < baseStart_4079340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079348 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4079348 : Nat := 118140960795 + 4079348 * 2 ^ 59
def prefixEnd_4079348 : Nat := 4983230072969 + 3 ^ 40 * 4079348 * 2
def baseEnd_4079348 : Nat := 1396444187304940510592951

theorem tailTrace_4079348 : CollatzResearch.WordTrace tailWord_4079348 prefixEnd_4079348 1396444187304940510592951 := by
  unfold tailWord_4079348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74393022412613184008307349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99190696550150912011076465 74393022412613184008307349)
  ·
    refine ⟨3487172925591243000389407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74393022412613184008307349 3487172925591243000389407)
    ·
      refine ⟨5230759388386864500584111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487172925591243000389407 5230759388386864500584111)
      ·
        refine ⟨7846139082580296750876167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230759388386864500584111 7846139082580296750876167)
        ·
          refine ⟨11769208623870445126314251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846139082580296750876167 11769208623870445126314251)
          ·
            refine ⟨17653812935805667689471377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769208623870445126314251 17653812935805667689471377)
            ·
              refine ⟨13240359701854250767103533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17653812935805667689471377 13240359701854250767103533)
              ·
                refine ⟨4965134888195344037663825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13240359701854250767103533 4965134888195344037663825)
                ·
                  refine ⟨3723851166146508028247869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965134888195344037663825 3723851166146508028247869)
                  ·
                    refine ⟨1396444187304940510592951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723851166146508028247869 1396444187304940510592951)
                    ·
                      rfl

theorem cell22_4079348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4079348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079348 prefixEnd_4079348 := by exact prefixLift 4079348
  have htrace : WordTrace (prefixWord ++ tailWord_4079348) baseStart_4079348 baseEnd_4079348 := by
    simpa [prefixWord, tailWord_4079348, baseEnd_4079348] using wordTrace_append hprefix tailTrace_4079348
  have hstable : (prefixWord ++ tailWord_4079348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079348).length < 2 ^ (prefixWord ++ tailWord_4079348).sum := by decide
  have hdescent : baseEnd_4079348 < baseStart_4079348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079449 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_4079449 : Nat := 118140960795 + 4079449 * 2 ^ 59
def prefixEnd_4079449 : Nat := 4983230072969 + 3 ^ 40 * 4079449 * 2
def baseEnd_4079449 : Nat := 1396478761669009913817641

theorem tailTrace_4079449 : CollatzResearch.WordTrace tailWord_4079449 prefixEnd_4079449 1396478761669009913817641 := by
  unfold tailWord_4079449
  simp only [CollatzResearch.WordTrace]
  refine ⟨148789728597860462266041401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99193152398573641510694267 148789728597860462266041401)
  ·
    refine ⟨111592296448395346699531051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148789728597860462266041401 111592296448395346699531051)
    ·
      refine ⟨167388444672593020049296577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111592296448395346699531051 167388444672593020049296577)
      ·
        refine ⟨125541333504444765036972433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167388444672593020049296577 125541333504444765036972433)
        ·
          refine ⟨94156000128333573777729325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125541333504444765036972433 94156000128333573777729325)
          ·
            refine ⟨35308500048125090166648497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94156000128333573777729325 35308500048125090166648497)
            ·
              refine ⟨26481375036093817624986373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35308500048125090166648497 26481375036093817624986373)
              ·
                refine ⟨4965257819267590804684945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26481375036093817624986373 4965257819267590804684945)
                ·
                  refine ⟨3723943364450693103513709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965257819267590804684945 3723943364450693103513709)
                  ·
                    refine ⟨1396478761669009913817641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723943364450693103513709 1396478761669009913817641)
                    ·
                      rfl

theorem cell22_4079449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_4079449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079449 prefixEnd_4079449 := by exact prefixLift 4079449
  have htrace : WordTrace (prefixWord ++ tailWord_4079449) baseStart_4079449 baseEnd_4079449 := by
    simpa [prefixWord, tailWord_4079449, baseEnd_4079449] using wordTrace_append hprefix tailTrace_4079449
  have hstable : (prefixWord ++ tailWord_4079449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079449).length < 2 ^ (prefixWord ++ tailWord_4079449).sum := by decide
  have hdescent : baseEnd_4079449 < baseStart_4079449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079502 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_4079502 : Nat := 118140960795 + 4079502 * 2 ^ 59
def prefixEnd_4079502 : Nat := 4983230072969 + 3 ^ 40 * 4079502 * 2
def baseEnd_4079502 : Nat := 465498968217378480747493

theorem tailTrace_4079502 : CollatzResearch.WordTrace tailWord_4079502 prefixEnd_4079502 465498968217378480747493 := by
  unfold tailWord_4079502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598957708333556539715095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99194441111112301545147173 18598957708333556539715095)
  ·
    refine ⟨27898436562500334809572643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598957708333556539715095 27898436562500334809572643)
    ·
      refine ⟨41847654843750502214358965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27898436562500334809572643 41847654843750502214358965)
      ·
        refine ⟨3923217641601609582596153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41847654843750502214358965 3923217641601609582596153)
        ·
          refine ⟨2942413231201207186947115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923217641601609582596153 2942413231201207186947115)
          ·
            refine ⟨4413619846801810780420673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942413231201207186947115 4413619846801810780420673)
            ·
              refine ⟨3310214885101358085315505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413619846801810780420673 3310214885101358085315505)
              ·
                refine ⟨2482661163826018563986629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310214885101358085315505 2482661163826018563986629)
                ·
                  refine ⟨465498968217378480747493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482661163826018563986629 465498968217378480747493)
                  ·
                    rfl

theorem cell22_4079502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_4079502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079502 prefixEnd_4079502 := by exact prefixLift 4079502
  have htrace : WordTrace (prefixWord ++ tailWord_4079502) baseStart_4079502 baseEnd_4079502 := by
    simpa [prefixWord, tailWord_4079502, baseEnd_4079502] using wordTrace_append hprefix tailTrace_4079502
  have hstable : (prefixWord ++ tailWord_4079502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079502).length < 2 ^ (prefixWord ++ tailWord_4079502).sum := by decide
  have hdescent : baseEnd_4079502 < baseStart_4079502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079524 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_4079524 : Nat := 118140960795 + 4079524 * 2 ^ 59
def prefixEnd_4079524 : Nat := 4983230072969 + 3 ^ 40 * 4079524 * 2
def baseEnd_4079524 : Nat := 465501478567244906064137

theorem tailTrace_4079524 : CollatzResearch.WordTrace tailWord_4079524 prefixEnd_4079524 465501478567244906064137 := by
  unfold tailWord_4079524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74396232036294375037510813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99194976048392500050014417 74396232036294375037510813)
  ·
    refine ⟨27898587013610390639066555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74396232036294375037510813 27898587013610390639066555)
    ·
      refine ⟨41847880520415585958599833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27898587013610390639066555 41847880520415585958599833)
      ·
        refine ⟨31385910390311689468949875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41847880520415585958599833 31385910390311689468949875)
        ·
          refine ⟨47078865585467534203424813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31385910390311689468949875 47078865585467534203424813)
          ·
            refine ⟨17654574594550325326284305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47078865585467534203424813 17654574594550325326284305)
            ·
              refine ⟨13240930945912743994713229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17654574594550325326284305 13240930945912743994713229)
              ·
                refine ⟨4965349104717278998017461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13240930945912743994713229 4965349104717278998017461)
                ·
                  refine ⟨465501478567244906064137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4965349104717278998017461 465501478567244906064137)
                  ·
                    rfl

theorem cell22_4079524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_4079524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079524 prefixEnd_4079524 := by exact prefixLift 4079524
  have htrace : WordTrace (prefixWord ++ tailWord_4079524) baseStart_4079524 baseEnd_4079524 := by
    simpa [prefixWord, tailWord_4079524, baseEnd_4079524] using wordTrace_append hprefix tailTrace_4079524
  have hstable : (prefixWord ++ tailWord_4079524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079524).length < 2 ^ (prefixWord ++ tailWord_4079524).sum := by decide
  have hdescent : baseEnd_4079524 < baseStart_4079524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079552 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_4079552 : Nat := 118140960795 + 4079552 * 2 ^ 59
def prefixEnd_4079552 : Nat := 4983230072969 + 3 ^ 40 * 4079552 * 2
def baseEnd_4079552 : Nat := 465504673557983992830775

theorem tailTrace_4079552 : CollatzResearch.WordTrace tailWord_4079552 prefixEnd_4079552 465504673557983992830775 := by
  unfold tailWord_4079552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74396742658243655428520455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99195656877658207238027273 74396742658243655428520455)
  ·
    refine ⟨111595113987365483142780683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74396742658243655428520455 111595113987365483142780683)
    ·
      refine ⟨167392670981048224714171025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111595113987365483142780683 167392670981048224714171025)
      ·
        refine ⟨125544503235786168535628269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167392670981048224714171025 125544503235786168535628269)
        ·
          refine ⟨47079188713419813200860601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125544503235786168535628269 47079188713419813200860601)
          ·
            refine ⟨35309391535064859900645451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47079188713419813200860601 35309391535064859900645451)
            ·
              refine ⟨52964087302597289850968177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35309391535064859900645451 52964087302597289850968177)
              ·
                refine ⟨39723065476947967388226133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52964087302597289850968177 39723065476947967388226133)
                ·
                  refine ⟨465504673557983992830775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39723065476947967388226133 465504673557983992830775)
                  ·
                    rfl

theorem cell22_4079552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_4079552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079552 prefixEnd_4079552 := by exact prefixLift 4079552
  have htrace : WordTrace (prefixWord ++ tailWord_4079552) baseStart_4079552 baseEnd_4079552 := by
    simpa [prefixWord, tailWord_4079552, baseEnd_4079552] using wordTrace_append hprefix tailTrace_4079552
  have hstable : (prefixWord ++ tailWord_4079552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079552).length < 2 ^ (prefixWord ++ tailWord_4079552).sum := by decide
  have hdescent : baseEnd_4079552 < baseStart_4079552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079599 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_4079599 : Nat := 118140960795 + 4079599 * 2 ^ 59
def prefixEnd_4079599 : Nat := 4983230072969 + 3 ^ 40 * 4079599 * 2
def baseEnd_4079599 : Nat := 1396530109734459522567181

theorem tailTrace_4079599 : CollatzResearch.WordTrace tailWord_4079599 prefixEnd_4079599 1396530109734459522567181 := by
  unfold tailWord_4079599
  simp only [CollatzResearch.WordTrace]
  refine ⟨148795199547317037884001851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99196799698211358589334567 148795199547317037884001851)
  ·
    refine ⟨223192799320975556826002777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148795199547317037884001851 223192799320975556826002777)
    ·
      refine ⟨167394599490731667619502083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223192799320975556826002777 167394599490731667619502083)
      ·
        refine ⟨251091899236097501429253125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167394599490731667619502083 251091899236097501429253125)
        ·
          refine ⟨47079731106768281517984961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251091899236097501429253125 47079731106768281517984961)
          ·
            refine ⟨35309798330076211138488721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47079731106768281517984961 35309798330076211138488721)
            ·
              refine ⟨26482348747557158353866541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35309798330076211138488721 26482348747557158353866541)
              ·
                refine ⟨9930880780333934382699953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26482348747557158353866541 9930880780333934382699953)
                ·
                  refine ⟨7448160585250450787024965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9930880780333934382699953 7448160585250450787024965)
                  ·
                    refine ⟨1396530109734459522567181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448160585250450787024965 1396530109734459522567181)
                    ·
                      rfl

theorem cell22_4079599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_4079599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079599 prefixEnd_4079599 := by exact prefixLift 4079599
  have htrace : WordTrace (prefixWord ++ tailWord_4079599) baseStart_4079599 baseEnd_4079599 := by
    simpa [prefixWord, tailWord_4079599, baseEnd_4079599] using wordTrace_append hprefix tailTrace_4079599
  have hstable : (prefixWord ++ tailWord_4079599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079599).length < 2 ^ (prefixWord ++ tailWord_4079599).sum := by decide
  have hdescent : baseEnd_4079599 < baseStart_4079599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079620 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_4079620 : Nat := 118140960795 + 4079620 * 2 ^ 59
def prefixEnd_4079620 : Nat := 4983230072969 + 3 ^ 40 * 4079620 * 2
def baseEnd_4079620 : Nat := 465512432821207489264039

theorem tailTrace_4079620 : CollatzResearch.WordTrace tailWord_4079620 prefixEnd_4079620 465512432821207489264039 := by
  unfold tailWord_4079620
  simp only [CollatzResearch.WordTrace]
  refine ⟨74397982740120479235258157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99197310320160638980344209 74397982740120479235258157)
  ·
    refine ⟨27899243527545179713221809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74397982740120479235258157 27899243527545179713221809)
    ·
      refine ⟨20924432645658884784916357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27899243527545179713221809 20924432645658884784916357)
      ·
        refine ⟨3923331121061040897171817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20924432645658884784916357 3923331121061040897171817)
        ·
          refine ⟨2942498340795780672878863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923331121061040897171817 2942498340795780672878863)
          ·
            refine ⟨4413747511193671009318295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942498340795780672878863 4413747511193671009318295)
            ·
              refine ⟨6620621266790506513977443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413747511193671009318295 6620621266790506513977443)
              ·
                refine ⟨9930931900185759770966165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620621266790506513977443 9930931900185759770966165)
                ·
                  refine ⟨465512432821207489264039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9930931900185759770966165 465512432821207489264039)
                  ·
                    rfl

theorem cell22_4079620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_4079620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079620 prefixEnd_4079620 := by exact prefixLift 4079620
  have htrace : WordTrace (prefixWord ++ tailWord_4079620) baseStart_4079620 baseEnd_4079620 := by
    simpa [prefixWord, tailWord_4079620, baseEnd_4079620] using wordTrace_append hprefix tailTrace_4079620
  have hstable : (prefixWord ++ tailWord_4079620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079620).length < 2 ^ (prefixWord ++ tailWord_4079620).sum := by decide
  have hdescent : baseEnd_4079620 < baseStart_4079620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079674 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_4079674 : Nat := 118140960795 + 4079674 * 2 ^ 59
def prefixEnd_4079674 : Nat := 4983230072969 + 3 ^ 40 * 4079674 * 2
def baseEnd_4079674 : Nat := 1396555783767184326941951

theorem tailTrace_4079674 : CollatzResearch.WordTrace tailWord_4079674 prefixEnd_4079674 1396555783767184326941951 := by
  unfold tailWord_4079674
  simp only [CollatzResearch.WordTrace]
  refine ⟨37199483755511331423245519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99198623348030217128654717 37199483755511331423245519)
  ·
    refine ⟨55799225633266997134868279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37199483755511331423245519 55799225633266997134868279)
    ·
      refine ⟨83698838449900495702302419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55799225633266997134868279 83698838449900495702302419)
      ·
        refine ⟨125548257674850743553453629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83698838449900495702302419 125548257674850743553453629)
        ·
          refine ⟨47080596628069028832545111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125548257674850743553453629 47080596628069028832545111)
          ·
            refine ⟨70620894942103543248817667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47080596628069028832545111 70620894942103543248817667)
            ·
              refine ⟨105931342413155314873226501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70620894942103543248817667 105931342413155314873226501)
              ·
                refine ⟨19862126702466621538729969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105931342413155314873226501 19862126702466621538729969)
                ·
                  refine ⟨14896595026849966154047477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19862126702466621538729969 14896595026849966154047477)
                  ·
                    refine ⟨1396555783767184326941951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14896595026849966154047477 1396555783767184326941951)
                    ·
                      rfl

theorem cell22_4079674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_4079674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079674 prefixEnd_4079674 := by exact prefixLift 4079674
  have htrace : WordTrace (prefixWord ++ tailWord_4079674) baseStart_4079674 baseEnd_4079674 := by
    simpa [prefixWord, tailWord_4079674, baseEnd_4079674] using wordTrace_append hprefix tailTrace_4079674
  have hstable : (prefixWord ++ tailWord_4079674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079674).length < 2 ^ (prefixWord ++ tailWord_4079674).sum := by decide
  have hdescent : baseEnd_4079674 < baseStart_4079674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079676 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_4079676 : Nat := 118140960795 + 4079676 * 2 ^ 59
def prefixEnd_4079676 : Nat := 4983230072969 + 3 ^ 40 * 4079676 * 2
def baseEnd_4079676 : Nat := 465518822802685662797315

theorem tailTrace_4079676 : CollatzResearch.WordTrace tailWord_4079676 prefixEnd_4079676 465518822802685662797315 := by
  unfold tailWord_4079676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399003984019040017277441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99198671978692053356369921 74399003984019040017277441)
  ·
    refine ⟨55799252988014280012958081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74399003984019040017277441 55799252988014280012958081)
    ·
      refine ⟨41849439741010710009718561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55799252988014280012958081 41849439741010710009718561)
      ·
        refine ⟨31387079805758032507288921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41849439741010710009718561 31387079805758032507288921)
        ·
          refine ⟨23540309854318524380466691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31387079805758032507288921 23540309854318524380466691)
          ·
            refine ⟨35310464781477786570700037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23540309854318524380466691 35310464781477786570700037)
            ·
              refine ⟨6620712146527084982006257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35310464781477786570700037 6620712146527084982006257)
              ·
                refine ⟨4965534109895313736504693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6620712146527084982006257 4965534109895313736504693)
                ·
                  refine ⟨465518822802685662797315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4965534109895313736504693 465518822802685662797315)
                  ·
                    rfl

theorem cell22_4079676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_4079676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079676 prefixEnd_4079676 := by exact prefixLift 4079676
  have htrace : WordTrace (prefixWord ++ tailWord_4079676) baseStart_4079676 baseEnd_4079676 := by
    simpa [prefixWord, tailWord_4079676, baseEnd_4079676] using wordTrace_append hprefix tailTrace_4079676
  have hstable : (prefixWord ++ tailWord_4079676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079676).length < 2 ^ (prefixWord ++ tailWord_4079676).sum := by decide
  have hdescent : baseEnd_4079676 < baseStart_4079676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079680 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 1, 3]
def baseStart_4079680 : Nat := 118140960795 + 4079680 * 2 ^ 59
def prefixEnd_4079680 : Nat := 4983230072969 + 3 ^ 40 * 4079680 * 2
def baseEnd_4079680 : Nat := 1396557837689802311291933

theorem tailTrace_4079680 : CollatzResearch.WordTrace tailWord_4079680 prefixEnd_4079680 1396557837689802311291933 := by
  unfold tailWord_4079680
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399076930011794358850247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99198769240015725811800329 74399076930011794358850247)
  ·
    refine ⟨111598615395017691538275371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74399076930011794358850247 111598615395017691538275371)
    ·
      refine ⟨167397923092526537307413057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111598615395017691538275371 167397923092526537307413057)
      ·
        refine ⟨125548442319394902980559793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167397923092526537307413057 125548442319394902980559793)
        ·
          refine ⟨94161331739546177235419845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125548442319394902980559793 94161331739546177235419845)
          ·
            refine ⟨17655249701164908231641221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94161331739546177235419845 17655249701164908231641221)
            ·
              refine ⟨3310359318968420293432729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17655249701164908231641221 3310359318968420293432729)
              ·
                refine ⟨2482769489226315220074547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310359318968420293432729 2482769489226315220074547)
                ·
                  refine ⟨3724154233839472830111821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482769489226315220074547 3724154233839472830111821)
                  ·
                    refine ⟨1396557837689802311291933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724154233839472830111821 1396557837689802311291933)
                    ·
                      rfl

theorem cell22_4079680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_4079680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079680 prefixEnd_4079680 := by exact prefixLift 4079680
  have htrace : WordTrace (prefixWord ++ tailWord_4079680) baseStart_4079680 baseEnd_4079680 := by
    simpa [prefixWord, tailWord_4079680, baseEnd_4079680] using wordTrace_append hprefix tailTrace_4079680
  have hstable : (prefixWord ++ tailWord_4079680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079680).length < 2 ^ (prefixWord ++ tailWord_4079680).sum := by decide
  have hdescent : baseEnd_4079680 < baseStart_4079680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079689 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_4079689 : Nat := 118140960795 + 4079689 * 2 ^ 59
def prefixEnd_4079689 : Nat := 4983230072969 + 3 ^ 40 * 4079689 * 2
def baseEnd_4079689 : Nat := 1396560918573729287816905

theorem tailTrace_4079689 : CollatzResearch.WordTrace tailWord_4079689 prefixEnd_4079689 1396560918573729287816905 := by
  unfold tailWord_4079689
  simp only [CollatzResearch.WordTrace]
  refine ⟨148798482116990983254778121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99198988077993988836518747 148798482116990983254778121)
  ·
    refine ⟨111598861587743237441083591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148798482116990983254778121 111598861587743237441083591)
    ·
      refine ⟨167398292381614856161625387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111598861587743237441083591 167398292381614856161625387)
      ·
        refine ⟨251097438572422284242438081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167398292381614856161625387 251097438572422284242438081)
        ·
          refine ⟨188323078929316713181828561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251097438572422284242438081 188323078929316713181828561)
          ·
            refine ⟨141242309196987534886371421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188323078929316713181828561 141242309196987534886371421)
            ·
              refine ⟨52965865948870325582389283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141242309196987534886371421 52965865948870325582389283)
              ·
                refine ⟨79448798923305488373583925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52965865948870325582389283 79448798923305488373583925)
                ·
                  refine ⟨7448324899059889535023493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79448798923305488373583925 7448324899059889535023493)
                  ·
                    refine ⟨1396560918573729287816905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448324899059889535023493 1396560918573729287816905)
                    ·
                      rfl

theorem cell22_4079689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_4079689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079689 prefixEnd_4079689 := by exact prefixLift 4079689
  have htrace : WordTrace (prefixWord ++ tailWord_4079689) baseStart_4079689 baseEnd_4079689 := by
    simpa [prefixWord, tailWord_4079689, baseEnd_4079689] using wordTrace_append hprefix tailTrace_4079689
  have hstable : (prefixWord ++ tailWord_4079689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079689).length < 2 ^ (prefixWord ++ tailWord_4079689).sum := by decide
  have hdescent : baseEnd_4079689 < baseStart_4079689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079704 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_4079704 : Nat := 118140960795 + 4079704 * 2 ^ 59
def prefixEnd_4079704 : Nat := 4983230072969 + 3 ^ 40 * 4079704 * 2
def baseEnd_4079704 : Nat := 465522017793424749563953

theorem tailTrace_4079704 : CollatzResearch.WordTrace tailWord_4079704 prefixEnd_4079704 465522017793424749563953 := by
  unfold tailWord_4079704
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399514605968320408287083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99199352807957760544382777 74399514605968320408287083)
  ·
    refine ⟨111599271908952480612430625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74399514605968320408287083 111599271908952480612430625)
    ·
      refine ⟨83699453931714360459322969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111599271908952480612430625 83699453931714360459322969)
      ·
        refine ⟨62774590448785770344492227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83699453931714360459322969 62774590448785770344492227)
        ·
          refine ⟨94161885673178655516738341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62774590448785770344492227 94161885673178655516738341)
          ·
            refine ⟨17655353563720997909388439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94161885673178655516738341 17655353563720997909388439)
            ·
              refine ⟨26483030345581496864082659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17655353563720997909388439 26483030345581496864082659)
              ·
                refine ⟨39724545518372245296123989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26483030345581496864082659 39724545518372245296123989)
                ·
                  refine ⟨465522017793424749563953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39724545518372245296123989 465522017793424749563953)
                  ·
                    rfl

theorem cell22_4079704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_4079704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079704 prefixEnd_4079704 := by exact prefixLift 4079704
  have htrace : WordTrace (prefixWord ++ tailWord_4079704) baseStart_4079704 baseEnd_4079704 := by
    simpa [prefixWord, tailWord_4079704, baseEnd_4079704] using wordTrace_append hprefix tailTrace_4079704
  have hstable : (prefixWord ++ tailWord_4079704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079704).length < 2 ^ (prefixWord ++ tailWord_4079704).sum := by decide
  have hdescent : baseEnd_4079704 < baseStart_4079704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079706 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_4079706 : Nat := 118140960795 + 4079706 * 2 ^ 59
def prefixEnd_4079706 : Nat := 4983230072969 + 3 ^ 40 * 4079706 * 2
def baseEnd_4079706 : Nat := 1396566738021146910141853

theorem tailTrace_4079706 : CollatzResearch.WordTrace tailWord_4079706 prefixEnd_4079706 1396566738021146910141853 := by
  unfold tailWord_4079706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37199775539482348789536743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99199401438619596772097981 37199775539482348789536743)
  ·
    refine ⟨55799663309223523184305115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37199775539482348789536743 55799663309223523184305115)
    ·
      refine ⟨83699494963835284776457673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55799663309223523184305115 83699494963835284776457673)
      ·
        refine ⟨62774621222876463582343255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83699494963835284776457673 62774621222876463582343255)
        ·
          refine ⟨94161931834314695373514883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62774621222876463582343255 94161931834314695373514883)
          ·
            refine ⟨141242897751472043060272325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94161931834314695373514883 141242897751472043060272325)
            ·
              refine ⟨26483043328401008073801061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141242897751472043060272325 26483043328401008073801061)
              ·
                refine ⟨4965570624075189013837699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26483043328401008073801061 4965570624075189013837699)
                ·
                  refine ⟨7448355936112783520756549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965570624075189013837699 7448355936112783520756549)
                  ·
                    refine ⟨1396566738021146910141853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448355936112783520756549 1396566738021146910141853)
                    ·
                      rfl

theorem cell22_4079706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_4079706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079706 prefixEnd_4079706 := by exact prefixLift 4079706
  have htrace : WordTrace (prefixWord ++ tailWord_4079706) baseStart_4079706 baseEnd_4079706 := by
    simpa [prefixWord, tailWord_4079706, baseEnd_4079706] using wordTrace_append hprefix tailTrace_4079706
  have hstable : (prefixWord ++ tailWord_4079706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079706).length < 2 ^ (prefixWord ++ tailWord_4079706).sum := by decide
  have hdescent : baseEnd_4079706 < baseStart_4079706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079779 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_4079779 : Nat := 118140960795 + 4079779 * 2 ^ 59
def prefixEnd_4079779 : Nat := 4983230072969 + 3 ^ 40 * 4079779 * 2
def baseEnd_4079779 : Nat := 1396591727412999053066629

theorem tailTrace_4079779 : CollatzResearch.WordTrace tailWord_4079779 prefixEnd_4079779 1396591727412999053066629 := by
  unfold tailWord_4079779
  simp only [CollatzResearch.WordTrace]
  refine ⟨148801764686664928625554391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99201176457776619083702927 148801764686664928625554391)
  ·
    refine ⟨223202647029997392938331587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148801764686664928625554391 223202647029997392938331587)
    ·
      refine ⟨334803970544996089407497381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223202647029997392938331587 334803970544996089407497381)
      ·
        refine ⟨62775744477186766763905759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334803970544996089407497381 62775744477186766763905759)
        ·
          refine ⟨94163616715780150145858639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62775744477186766763905759 94163616715780150145858639)
          ·
            refine ⟨141245425073670225218787959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94163616715780150145858639 141245425073670225218787959)
            ·
              refine ⟨211868137610505337828181939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141245425073670225218787959 211868137610505337828181939)
              ·
                refine ⟨317802206415758006742272909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211868137610505337828181939 317802206415758006742272909)
                ·
                  refine ⟨119175827405909252528352341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317802206415758006742272909 119175827405909252528352341)
                  ·
                    refine ⟨1396591727412999053066629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119175827405909252528352341 1396591727412999053066629)
                    ·
                      rfl

theorem cell22_4079779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_4079779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079779 prefixEnd_4079779 := by exact prefixLift 4079779
  have htrace : WordTrace (prefixWord ++ tailWord_4079779) baseStart_4079779 baseEnd_4079779 := by
    simpa [prefixWord, tailWord_4079779, baseEnd_4079779] using wordTrace_append hprefix tailTrace_4079779
  have hstable : (prefixWord ++ tailWord_4079779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079779).length < 2 ^ (prefixWord ++ tailWord_4079779).sum := by decide
  have hdescent : baseEnd_4079779 < baseStart_4079779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079783 : List Nat := [1, 1, 6, 2, 2, 2, 8]
def baseStart_4079783 : Nat := 118140960795 + 4079783 * 2 ^ 59
def prefixEnd_4079783 : Nat := 4983230072969 + 3 ^ 40 * 4079783 * 2
def baseEnd_4079783 : Nat := 51725670247953495406171

theorem tailTrace_4079783 : CollatzResearch.WordTrace tailWord_4079783 prefixEnd_4079783 51725670247953495406171 := by
  unfold tailWord_4079783
  simp only [CollatzResearch.WordTrace]
  refine ⟨148801910578650437308700003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99201273719100291539133335 148801910578650437308700003)
  ·
    refine ⟨223202865867975655963050005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148801910578650437308700003 223202865867975655963050005)
    ·
      refine ⟨10462634337561358873267969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223202865867975655963050005 10462634337561358873267969)
      ·
        refine ⟨7846975753171019154950977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10462634337561358873267969 7846975753171019154950977)
        ·
          refine ⟨5885231814878264366213233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846975753171019154950977 5885231814878264366213233)
          ·
            refine ⟨4413923861158698274659925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5885231814878264366213233 4413923861158698274659925)
            ·
              refine ⟨51725670247953495406171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4413923861158698274659925 51725670247953495406171)
              ·
                rfl

theorem cell22_4079783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 8].length) (baseStart_4079783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079783 prefixEnd_4079783 := by exact prefixLift 4079783
  have htrace : WordTrace (prefixWord ++ tailWord_4079783) baseStart_4079783 baseEnd_4079783 := by
    simpa [prefixWord, tailWord_4079783, baseEnd_4079783] using wordTrace_append hprefix tailTrace_4079783
  have hstable : (prefixWord ++ tailWord_4079783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079783).length < 2 ^ (prefixWord ++ tailWord_4079783).sum := by decide
  have hdescent : baseEnd_4079783 < baseStart_4079783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079804 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_4079804 : Nat := 118140960795 + 4079804 * 2 ^ 59
def prefixEnd_4079804 : Nat := 4983230072969 + 3 ^ 40 * 4079804 * 2
def baseEnd_4079804 : Nat := 1396600285423907321191553

theorem tailTrace_4079804 : CollatzResearch.WordTrace tailWord_4079804 prefixEnd_4079804 1396600285423907321191553 := by
  unfold tailWord_4079804
  simp only [CollatzResearch.WordTrace]
  refine ⟨74401338255787178947607233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99201784341049571930142977 74401338255787178947607233)
  ·
    refine ⟨55801003691840384210705425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74401338255787178947607233 55801003691840384210705425)
    ·
      refine ⟨41850752768880288158029069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55801003691840384210705425 41850752768880288158029069)
      ·
        refine ⟨15694032288330108059260901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41850752768880288158029069 15694032288330108059260901)
        ·
          refine ⟨2942631054061895261111419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15694032288330108059260901 2942631054061895261111419)
          ·
            refine ⟨4413946581092842891667129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942631054061895261111419 4413946581092842891667129)
            ·
              refine ⟨3310459935819632168750347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413946581092842891667129 3310459935819632168750347)
              ·
                refine ⟨4965689903729448253125521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310459935819632168750347 4965689903729448253125521)
                ·
                  refine ⟨3724267427797086189844141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965689903729448253125521 3724267427797086189844141)
                  ·
                    refine ⟨1396600285423907321191553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724267427797086189844141 1396600285423907321191553)
                    ·
                      rfl

theorem cell22_4079804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_4079804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079804 prefixEnd_4079804 := by exact prefixLift 4079804
  have htrace : WordTrace (prefixWord ++ tailWord_4079804) baseStart_4079804 baseEnd_4079804 := by
    simpa [prefixWord, tailWord_4079804, baseEnd_4079804] using wordTrace_append hprefix tailTrace_4079804
  have hstable : (prefixWord ++ tailWord_4079804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079804).length < 2 ^ (prefixWord ++ tailWord_4079804).sum := by decide
  have hdescent : baseEnd_4079804 < baseStart_4079804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079858 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_4079858 : Nat := 118140960795 + 4079858 * 2 ^ 59
def prefixEnd_4079858 : Nat := 4983230072969 + 3 ^ 40 * 4079858 * 2
def baseEnd_4079858 : Nat := 1396618770727469180341387

theorem tailTrace_4079858 : CollatzResearch.WordTrace tailWord_4079858 prefixEnd_4079858 1396618770727469180341387 := by
  unfold tailWord_4079858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37201161513344681279420057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99203097368919150078453485 37201161513344681279420057)
  ·
    refine ⟨27900871135008510959565043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37201161513344681279420057 27900871135008510959565043)
    ·
      refine ⟨41851306702512766439347565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27900871135008510959565043 41851306702512766439347565)
      ·
        refine ⟨15694240013442287414755337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41851306702512766439347565 15694240013442287414755337)
        ·
          refine ⟨11770680010081715561066503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15694240013442287414755337 11770680010081715561066503)
          ·
            refine ⟨17656020015122573341599755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770680010081715561066503 17656020015122573341599755)
            ·
              refine ⟨26484030022683860012399633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656020015122573341599755 26484030022683860012399633)
              ·
                refine ⟨19863022517012895009299725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26484030022683860012399633 19863022517012895009299725)
                ·
                  refine ⟨7448633443879835628487397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19863022517012895009299725 7448633443879835628487397)
                  ·
                    refine ⟨1396618770727469180341387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448633443879835628487397 1396618770727469180341387)
                    ·
                      rfl

theorem cell22_4079858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_4079858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079858 prefixEnd_4079858 := by exact prefixLift 4079858
  have htrace : WordTrace (prefixWord ++ tailWord_4079858) baseStart_4079858 baseEnd_4079858 := by
    simpa [prefixWord, tailWord_4079858, baseEnd_4079858] using wordTrace_append hprefix tailTrace_4079858
  have hstable : (prefixWord ++ tailWord_4079858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079858).length < 2 ^ (prefixWord ++ tailWord_4079858).sum := by decide
  have hdescent : baseEnd_4079858 < baseStart_4079858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079905 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_4079905 : Nat := 118140960795 + 4079905 * 2 ^ 59
def prefixEnd_4079905 : Nat := 4983230072969 + 3 ^ 40 * 4079905 * 2
def baseEnd_4079905 : Nat := 1396634859787976724416243

theorem tailTrace_4079905 : CollatzResearch.WordTrace tailWord_4079905 prefixEnd_4079905 1396634859787976724416243 := by
  unfold tailWord_4079905
  simp only [CollatzResearch.WordTrace]
  refine ⟨148806360284208452144641169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99204240189472301429760779 148806360284208452144641169)
  ·
    refine ⟨111604770213156339108480877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148806360284208452144641169 111604770213156339108480877)
    ·
      refine ⟨41851788829933627165680329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111604770213156339108480877 41851788829933627165680329)
      ·
        refine ⟨31388841622450220374260247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41851788829933627165680329 31388841622450220374260247)
        ·
          refine ⟨47083262433675330561390371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31388841622450220374260247 47083262433675330561390371)
          ·
            refine ⟨70624893650512995842085557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47083262433675330561390371 70624893650512995842085557)
            ·
              refine ⟨6621083779735593360195521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70624893650512995842085557 6621083779735593360195521)
              ·
                refine ⟨4965812834801695020146641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621083779735593360195521 4965812834801695020146641)
                ·
                  refine ⟨3724359626101271265109981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965812834801695020146641 3724359626101271265109981)
                  ·
                    refine ⟨1396634859787976724416243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724359626101271265109981 1396634859787976724416243)
                    ·
                      rfl

theorem cell22_4079905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_4079905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079905 prefixEnd_4079905 := by exact prefixLift 4079905
  have htrace : WordTrace (prefixWord ++ tailWord_4079905) baseStart_4079905 baseEnd_4079905 := by
    simpa [prefixWord, tailWord_4079905, baseEnd_4079905] using wordTrace_append hprefix tailTrace_4079905
  have hstable : (prefixWord ++ tailWord_4079905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079905).length < 2 ^ (prefixWord ++ tailWord_4079905).sum := by decide
  have hdescent : baseEnd_4079905 < baseStart_4079905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079922 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_4079922 : Nat := 118140960795 + 4079922 * 2 ^ 59
def prefixEnd_4079922 : Nat := 4983230072969 + 3 ^ 40 * 4079922 * 2
def baseEnd_4079922 : Nat := 1396640679235394346741191

theorem tailTrace_4079922 : CollatzResearch.WordTrace tailWord_4079922 prefixEnd_4079922 1396640679235394346741191 := by
  unfold tailWord_4079922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37201745081286716012002505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99204653550097909365340013 37201745081286716012002505)
  ·
    refine ⟨27901308810965037009001879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37201745081286716012002505 27901308810965037009001879)
    ·
      refine ⟨41851963216447555513502819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27901308810965037009001879 41851963216447555513502819)
      ·
        refine ⟨62777944824671333270254229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41851963216447555513502819 62777944824671333270254229)
        ·
          refine ⟨2942716163656468747043167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62777944824671333270254229 2942716163656468747043167)
          ·
            refine ⟨4414074245484703120564751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942716163656468747043167 4414074245484703120564751)
            ·
              refine ⟨6621111368227054680847127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414074245484703120564751 6621111368227054680847127)
              ·
                refine ⟨9931667052340582021270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621111368227054680847127 9931667052340582021270691)
                ·
                  refine ⟨14897500578510873031906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931667052340582021270691 14897500578510873031906037)
                  ·
                    refine ⟨1396640679235394346741191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14897500578510873031906037 1396640679235394346741191)
                    ·
                      rfl

theorem cell22_4079922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_4079922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079922 prefixEnd_4079922 := by exact prefixLift 4079922
  have htrace : WordTrace (prefixWord ++ tailWord_4079922) baseStart_4079922 baseEnd_4079922 := by
    simpa [prefixWord, tailWord_4079922, baseEnd_4079922] using wordTrace_append hprefix tailTrace_4079922
  have hstable : (prefixWord ++ tailWord_4079922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079922).length < 2 ^ (prefixWord ++ tailWord_4079922).sum := by decide
  have hdescent : baseEnd_4079922 < baseStart_4079922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079980 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_4079980 : Nat := 118140960795 + 4079980 * 2 ^ 59
def prefixEnd_4079980 : Nat := 4983230072969 + 3 ^ 40 * 4079980 * 2
def baseEnd_4079980 : Nat := 465553511273567176263671

theorem tailTrace_4079980 : CollatzResearch.WordTrace tailWord_4079980 prefixEnd_4079980 465553511273567176263671 := by
  unfold tailWord_4079980
  simp only [CollatzResearch.WordTrace]
  refine ⟨74404547879468369976810697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99206063839291159969080929 74404547879468369976810697)
  ·
    refine ⟨55803410909601277482608023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74404547879468369976810697 55803410909601277482608023)
    ·
      refine ⟨83705116364401916223912035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55803410909601277482608023 83705116364401916223912035)
      ·
        refine ⟨125557674546602874335868053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83705116364401916223912035 125557674546602874335868053)
        ·
          refine ⟨5885515994372009734493815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125557674546602874335868053 5885515994372009734493815)
          ·
            refine ⟨8828273991558014601740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885515994372009734493815 8828273991558014601740723)
            ·
              refine ⟨13242410987337021902611085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828273991558014601740723 13242410987337021902611085)
              ·
                refine ⟨4965904120251383213479157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13242410987337021902611085 4965904120251383213479157)
                ·
                  refine ⟨465553511273567176263671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4965904120251383213479157 465553511273567176263671)
                  ·
                    rfl

theorem cell22_4079980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_4079980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4079980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4079980 prefixEnd_4079980 := by exact prefixLift 4079980
  have htrace : WordTrace (prefixWord ++ tailWord_4079980) baseStart_4079980 baseEnd_4079980 := by
    simpa [prefixWord, tailWord_4079980, baseEnd_4079980] using wordTrace_append hprefix tailTrace_4079980
  have hstable : (prefixWord ++ tailWord_4079980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079980).length < 2 ^ (prefixWord ++ tailWord_4079980).sum := by decide
  have hdescent : baseEnd_4079980 < baseStart_4079980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080025 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 4]
def baseStart_4080025 : Nat := 118140960795 + 4080025 * 2 ^ 59
def prefixEnd_4080025 : Nat := 4983230072969 + 3 ^ 40 * 4080025 * 2
def baseEnd_4080025 : Nat := 465558646080112137138625

theorem tailTrace_4080025 : CollatzResearch.WordTrace tailWord_4080025 prefixEnd_4080025 465558646080112137138625 := by
  unfold tailWord_4080025
  simp only [CollatzResearch.WordTrace]
  refine ⟨148810737043773712639009529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99207158029182475092673019 148810737043773712639009529)
  ·
    refine ⟨111608052782830284479257147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148810737043773712639009529 111608052782830284479257147)
    ·
      refine ⟨167412079174245426718885721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111608052782830284479257147 167412079174245426718885721)
      ·
        refine ⟨125559059380684070039164291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167412079174245426718885721 125559059380684070039164291)
        ·
          refine ⟨188338589071026105058746437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125559059380684070039164291 188338589071026105058746437)
          ·
            refine ⟨35313485450817394698514957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188338589071026105058746437 35313485450817394698514957)
            ·
              refine ⟨13242557044056523011943109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35313485450817394698514957 13242557044056523011943109)
              ·
                refine ⟨2482979445760598064739333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13242557044056523011943109 2482979445760598064739333)
                ·
                  refine ⟨465558646080112137138625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482979445760598064739333 465558646080112137138625)
                  ·
                    rfl

theorem cell22_4080025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_4080025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080025 prefixEnd_4080025 := by exact prefixLift 4080025
  have htrace : WordTrace (prefixWord ++ tailWord_4080025) baseStart_4080025 baseEnd_4080025 := by
    simpa [prefixWord, tailWord_4080025, baseEnd_4080025] using wordTrace_append hprefix tailTrace_4080025
  have hstable : (prefixWord ++ tailWord_4080025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080025).length < 2 ^ (prefixWord ++ tailWord_4080025).sum := by decide
  have hdescent : baseEnd_4080025 < baseStart_4080025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080055 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 2, 4]
def baseStart_4080055 : Nat := 118140960795 + 4080055 * 2 ^ 59
def prefixEnd_4080055 : Nat := 4983230072969 + 3 ^ 40 * 4080055 * 2
def baseEnd_4080055 : Nat := 1396686207853426333165783

theorem tailTrace_4080055 : CollatzResearch.WordTrace tailWord_4080055 prefixEnd_4080055 1396686207853426333165783 := by
  unfold tailWord_4080055
  simp only [CollatzResearch.WordTrace]
  refine ⟨148811831233665027762601619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99207887489110018508401079 148811831233665027762601619)
  ·
    refine ⟨223217746850497541643902429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148811831233665027762601619 223217746850497541643902429)
    ·
      refine ⟨83706655068936578116463411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223217746850497541643902429 83706655068936578116463411)
      ·
        refine ⟨125559982603404867174695117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83706655068936578116463411 125559982603404867174695117)
        ·
          refine ⟨47084993476276825190510669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125559982603404867174695117 47084993476276825190510669)
          ·
            refine ⟨17656872553603809446441501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47084993476276825190510669 17656872553603809446441501)
            ·
              refine ⟨6621327207601428542415563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17656872553603809446441501 6621327207601428542415563)
              ·
                refine ⟨9931990811402142813623345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621327207601428542415563 9931990811402142813623345)
                ·
                  refine ⟨7448993108551607110217509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9931990811402142813623345 7448993108551607110217509)
                  ·
                    refine ⟨1396686207853426333165783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7448993108551607110217509 1396686207853426333165783)
                    ·
                      rfl

theorem cell22_4080055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_4080055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080055 prefixEnd_4080055 := by exact prefixLift 4080055
  have htrace : WordTrace (prefixWord ++ tailWord_4080055) baseStart_4080055 baseEnd_4080055 := by
    simpa [prefixWord, tailWord_4080055, baseEnd_4080055] using wordTrace_append hprefix tailTrace_4080055
  have hstable : (prefixWord ++ tailWord_4080055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080055).length < 2 ^ (prefixWord ++ tailWord_4080055).sum := by decide
  have hdescent : baseEnd_4080055 < baseStart_4080055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080192 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_4080192 : Nat := 118140960795 + 4080192 * 2 ^ 59
def prefixEnd_4080192 : Nat := 4983230072969 + 3 ^ 40 * 4080192 * 2
def baseEnd_4080192 : Nat := 1396733105753203642490363

theorem tailTrace_4080192 : CollatzResearch.WordTrace tailWord_4080192 prefixEnd_4080192 1396733105753203642490363 := by
  unfold tailWord_4080192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74408414017084350080169415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99211218689445800106892553 74408414017084350080169415)
  ·
    refine ⟨111612621025626525120254123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74408414017084350080169415 111612621025626525120254123)
    ·
      refine ⟨167418931538439787680381185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111612621025626525120254123 167418931538439787680381185)
      ·
        refine ⟨125564198653829840760285889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167418931538439787680381185 125564198653829840760285889)
        ·
          refine ⟨94173148990372380570214417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125564198653829840760285889 94173148990372380570214417)
          ·
            refine ⟨70629861742779285427660813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94173148990372380570214417 70629861742779285427660813)
            ·
              refine ⟨26486198153542232035372805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70629861742779285427660813 26486198153542232035372805)
              ·
                refine ⟨4966162153789168506632401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26486198153542232035372805 4966162153789168506632401)
                ·
                  refine ⟨3724621615341876379974301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966162153789168506632401 3724621615341876379974301)
                  ·
                    refine ⟨1396733105753203642490363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724621615341876379974301 1396733105753203642490363)
                    ·
                      rfl

theorem cell22_4080192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_4080192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080192 prefixEnd_4080192 := by exact prefixLift 4080192
  have htrace : WordTrace (prefixWord ++ tailWord_4080192) baseStart_4080192 baseEnd_4080192 := by
    simpa [prefixWord, tailWord_4080192, baseEnd_4080192] using wordTrace_append hprefix tailTrace_4080192
  have hstable : (prefixWord ++ tailWord_4080192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080192).length < 2 ^ (prefixWord ++ tailWord_4080192).sum := by decide
  have hdescent : baseEnd_4080192 < baseStart_4080192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080288 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 1, 3]
def baseStart_4080288 : Nat := 118140960795 + 4080288 * 2 ^ 59
def prefixEnd_4080288 : Nat := 4983230072969 + 3 ^ 40 * 4080288 * 2
def baseEnd_4080288 : Nat := 1396765968515091392090069

theorem tailTrace_4080288 : CollatzResearch.WordTrace tailWord_4080288 prefixEnd_4080288 1396765968515091392090069 := by
  unfold tailWord_4080288
  simp only [CollatzResearch.WordTrace]
  refine ⟨74410164720910454277916759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99213552961213939037222345 74410164720910454277916759)
  ·
    refine ⟨111615247081365681416875139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74410164720910454277916759 111615247081365681416875139)
    ·
      refine ⟨167422870622048522125312709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111615247081365681416875139 167422870622048522125312709)
      ·
        refine ⟨31391788241634097898496133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167422870622048522125312709 31391788241634097898496133)
        ·
          refine ⟨5885960295306393355968025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31391788241634097898496133 5885960295306393355968025)
          ·
            refine ⟨4414470221479795016976019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5885960295306393355968025 4414470221479795016976019)
            ·
              refine ⟨6621705332219692525464029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414470221479795016976019 6621705332219692525464029)
              ·
                refine ⟨2483139499582384697049011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6621705332219692525464029 2483139499582384697049011)
                ·
                  refine ⟨3724709249373577045573517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483139499582384697049011 3724709249373577045573517)
                  ·
                    refine ⟨1396765968515091392090069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724709249373577045573517 1396765968515091392090069)
                    ·
                      rfl

theorem cell22_4080288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_4080288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080288 prefixEnd_4080288 := by exact prefixLift 4080288
  have htrace : WordTrace (prefixWord ++ tailWord_4080288) baseStart_4080288 baseEnd_4080288 := by
    simpa [prefixWord, tailWord_4080288, baseEnd_4080288] using wordTrace_append hprefix tailTrace_4080288
  have hstable : (prefixWord ++ tailWord_4080288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080288).length < 2 ^ (prefixWord ++ tailWord_4080288).sum := by decide
  have hdescent : baseEnd_4080288 < baseStart_4080288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080305 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 1, 3]
def baseStart_4080305 : Nat := 118140960795 + 4080305 * 2 ^ 59
def prefixEnd_4080305 : Nat := 4983230072969 + 3 ^ 40 * 4080305 * 2
def baseEnd_4080305 : Nat := 1396771787962509014415017

theorem tailTrace_4080305 : CollatzResearch.WordTrace tailWord_4080305 prefixEnd_4080305 1396771787962509014415017 := by
  unfold tailWord_4080305
  simp only [CollatzResearch.WordTrace]
  refine ⟨148820949482759320459202369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99213966321839546972801579 148820949482759320459202369)
  ·
    refine ⟨111615712112069490344401777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148820949482759320459202369 111615712112069490344401777)
    ·
      refine ⟨83711784084052117758301333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111615712112069490344401777 83711784084052117758301333)
      ·
        refine ⟨3923989878939943019920375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83711784084052117758301333 3923989878939943019920375)
        ·
          refine ⟨5885984818409914529880563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3923989878939943019920375 5885984818409914529880563)
          ·
            refine ⟨8828977227614871794820845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885984818409914529880563 8828977227614871794820845)
            ·
              refine ⟨3310866460355576923057817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8828977227614871794820845 3310866460355576923057817)
              ·
                refine ⟨2483149845266682692293363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310866460355576923057817 2483149845266682692293363)
                ·
                  refine ⟨3724724767900024038440045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483149845266682692293363 3724724767900024038440045)
                  ·
                    refine ⟨1396771787962509014415017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724724767900024038440045 1396771787962509014415017)
                    ·
                      rfl

theorem cell22_4080305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_4080305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080305 prefixEnd_4080305 := by exact prefixLift 4080305
  have htrace : WordTrace (prefixWord ++ tailWord_4080305) baseStart_4080305 baseEnd_4080305 := by
    simpa [prefixWord, tailWord_4080305, baseEnd_4080305] using wordTrace_append hprefix tailTrace_4080305
  have hstable : (prefixWord ++ tailWord_4080305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080305).length < 2 ^ (prefixWord ++ tailWord_4080305).sum := by decide
  have hdescent : baseEnd_4080305 < baseStart_4080305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080327 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 6, 3]
def baseStart_4080327 : Nat := 118140960795 + 4080327 * 2 ^ 59
def prefixEnd_4080327 : Nat := 4983230072969 + 3 ^ 40 * 4080327 * 2
def baseEnd_4080327 : Nat := 1396779319012108290364949

theorem tailTrace_4080327 : CollatzResearch.WordTrace tailWord_4080327 prefixEnd_4080327 1396779319012108290364949 := by
  unfold tailWord_4080327
  simp only [CollatzResearch.WordTrace]
  refine ⟨148821751888679618216503235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99214501259119745477668823 148821751888679618216503235)
  ·
    refine ⟨223232627833019427324754853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148821751888679618216503235 223232627833019427324754853)
    ·
      refine ⟨41856117718691142623391535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223232627833019427324754853 41856117718691142623391535)
      ·
        refine ⟨62784176578036713935087303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41856117718691142623391535 62784176578036713935087303)
        ·
          refine ⟨94176264867055070902630955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62784176578036713935087303 94176264867055070902630955)
          ·
            refine ⟨141264397300582606353946433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94176264867055070902630955 141264397300582606353946433)
            ·
              refine ⟨105948297975436954765459825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141264397300582606353946433 105948297975436954765459825)
              ·
                refine ⟨79461223481577716074094869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105948297975436954765459825 79461223481577716074094869)
                ·
                  refine ⟨3724744850698955440973197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79461223481577716074094869 3724744850698955440973197)
                  ·
                    refine ⟨1396779319012108290364949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724744850698955440973197 1396779319012108290364949)
                    ·
                      rfl

theorem cell22_4080327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_4080327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080327 prefixEnd_4080327 := by exact prefixLift 4080327
  have htrace : WordTrace (prefixWord ++ tailWord_4080327) baseStart_4080327 baseEnd_4080327 := by
    simpa [prefixWord, tailWord_4080327, baseEnd_4080327] using wordTrace_append hprefix tailTrace_4080327
  have hstable : (prefixWord ++ tailWord_4080327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080327).length < 2 ^ (prefixWord ++ tailWord_4080327).sum := by decide
  have hdescent : baseEnd_4080327 < baseStart_4080327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080348 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4080348 : Nat := 118140960795 + 4080348 * 2 ^ 59
def prefixEnd_4080348 : Nat := 4983230072969 + 3 ^ 40 * 4080348 * 2
def baseEnd_4080348 : Nat := 1396786507741271235589885

theorem tailTrace_4080348 : CollatzResearch.WordTrace tailWord_4080348 prefixEnd_4080348 1396786507741271235589885 := by
  unfold tailWord_4080348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74411258910801769401508849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99215011881069025868678465 74411258910801769401508849)
  ·
    refine ⟨55808444183101327051131637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74411258910801769401508849 55808444183101327051131637)
    ·
      refine ⟨5232041642165749411043591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55808444183101327051131637 5232041642165749411043591)
      ·
        refine ⟨7848062463248624116565387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232041642165749411043591 7848062463248624116565387)
        ·
          refine ⟨11772093694872936174848081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848062463248624116565387 11772093694872936174848081)
          ·
            refine ⟨8829070271154702131136061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11772093694872936174848081 8829070271154702131136061)
            ·
              refine ⟨3310901351683013299176023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8829070271154702131136061 3310901351683013299176023)
              ·
                refine ⟨4966352027524519948764035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310901351683013299176023 4966352027524519948764035)
                ·
                  refine ⟨7449528041286779923146053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966352027524519948764035 7449528041286779923146053)
                  ·
                    refine ⟨1396786507741271235589885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449528041286779923146053 1396786507741271235589885)
                    ·
                      rfl

theorem cell22_4080348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4080348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080348 prefixEnd_4080348 := by exact prefixLift 4080348
  have htrace : WordTrace (prefixWord ++ tailWord_4080348) baseStart_4080348 baseEnd_4080348 := by
    simpa [prefixWord, tailWord_4080348, baseEnd_4080348] using wordTrace_append hprefix tailTrace_4080348
  have hstable : (prefixWord ++ tailWord_4080348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080348).length < 2 ^ (prefixWord ++ tailWord_4080348).sum := by decide
  have hdescent : baseEnd_4080348 < baseStart_4080348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080417 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_4080417 : Nat := 118140960795 + 4080417 * 2 ^ 59
def prefixEnd_4080417 : Nat := 4983230072969 + 3 ^ 40 * 4080417 * 2
def baseEnd_4080417 : Nat := 1396810127851378055614673

theorem tailTrace_4080417 : CollatzResearch.WordTrace tailWord_4080417 prefixEnd_4080417 1396810127851378055614673 := by
  unfold tailWord_4080417
  simp only [CollatzResearch.WordTrace]
  refine ⟨148825034458353563587279505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99216689638902375724853003 148825034458353563587279505)
  ·
    refine ⟨111618775843765172690459629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148825034458353563587279505 111618775843765172690459629)
    ·
      refine ⟨41857040941411939758922361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111618775843765172690459629 41857040941411939758922361)
      ·
        refine ⟨31392780706058954819191771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41857040941411939758922361 31392780706058954819191771)
        ·
          refine ⟨47089171059088432228787657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31392780706058954819191771 47089171059088432228787657)
          ·
            refine ⟨35316878294316324171590743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47089171059088432228787657 35316878294316324171590743)
            ·
              refine ⟨52975317441474486257386115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35316878294316324171590743 52975317441474486257386115)
              ·
                refine ⟨79462976162211729386079173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52975317441474486257386115 79462976162211729386079173)
                ·
                  refine ⟨14899308030414699259889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79462976162211729386079173 14899308030414699259889845)
                  ·
                    refine ⟨1396810127851378055614673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14899308030414699259889845 1396810127851378055614673)
                    ·
                      rfl

theorem cell22_4080417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_4080417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080417 prefixEnd_4080417 := by exact prefixLift 4080417
  have htrace : WordTrace (prefixWord ++ tailWord_4080417) baseStart_4080417 baseEnd_4080417 := by
    simpa [prefixWord, tailWord_4080417, baseEnd_4080417] using wordTrace_append hprefix tailTrace_4080417
  have hstable : (prefixWord ++ tailWord_4080417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080417).length < 2 ^ (prefixWord ++ tailWord_4080417).sum := by decide
  have hdescent : baseEnd_4080417 < baseStart_4080417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080432 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_4080432 : Nat := 118140960795 + 4080432 * 2 ^ 59
def prefixEnd_4080432 : Nat := 4983230072969 + 3 ^ 40 * 4080432 * 2
def baseEnd_4080432 : Nat := 1396815262657923016489627

theorem tailTrace_4080432 : CollatzResearch.WordTrace tailWord_4080432 prefixEnd_4080432 1396815262657923016489627 := by
  unfold tailWord_4080432
  simp only [CollatzResearch.WordTrace]
  refine ⟨74412790776649610574537775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99217054368866147432717033 74412790776649610574537775)
  ·
    refine ⟨111619186164974415861806663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74412790776649610574537775 111619186164974415861806663)
    ·
      refine ⟨167428779247461623792709995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111619186164974415861806663 167428779247461623792709995)
      ·
        refine ⟨251143168871192435689064993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167428779247461623792709995 251143168871192435689064993)
        ·
          refine ⟨188357376653394326766798745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251143168871192435689064993 188357376653394326766798745)
          ·
            refine ⟨141268032490045745075099059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188357376653394326766798745 141268032490045745075099059)
            ·
              refine ⟨211902048735068617612648589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141268032490045745075099059 211902048735068617612648589)
              ·
                refine ⟨79463268275650731604743221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211902048735068617612648589 79463268275650731604743221)
                ·
                  refine ⟨7449681400842256087944677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79463268275650731604743221 7449681400842256087944677)
                  ·
                    refine ⟨1396815262657923016489627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449681400842256087944677 1396815262657923016489627)
                    ·
                      rfl

theorem cell22_4080432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_4080432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080432 prefixEnd_4080432 := by exact prefixLift 4080432
  have htrace : WordTrace (prefixWord ++ tailWord_4080432) baseStart_4080432 baseEnd_4080432 := by
    simpa [prefixWord, tailWord_4080432, baseEnd_4080432] using wordTrace_append hprefix tailTrace_4080432
  have hstable : (prefixWord ++ tailWord_4080432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080432).length < 2 ^ (prefixWord ++ tailWord_4080432).sum := by decide
  have hdescent : baseEnd_4080432 < baseStart_4080432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080479 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 4, 3]
def baseStart_4080479 : Nat := 118140960795 + 4080479 * 2 ^ 59
def prefixEnd_4080479 : Nat := 4983230072969 + 3 ^ 40 * 4080479 * 2
def baseEnd_4080479 : Nat := 1396831351718430560564483

theorem tailTrace_4080479 : CollatzResearch.WordTrace tailWord_4080479 prefixEnd_4080479 1396831351718430560564483 := by
  unfold tailWord_4080479
  simp only [CollatzResearch.WordTrace]
  refine ⟨148827295784128948176036491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99218197189419298784024327 148827295784128948176036491)
  ·
    refine ⟨223240943676193422264054737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148827295784128948176036491 223240943676193422264054737)
    ·
      refine ⟨167430707757145066698041053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223240943676193422264054737 167430707757145066698041053)
      ·
        refine ⟨62786515408929400011765395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167430707757145066698041053 62786515408929400011765395)
        ·
          refine ⟨94179773113394100017648093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62786515408929400011765395 94179773113394100017648093)
          ·
            refine ⟨35317414917522787506618035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94179773113394100017648093 35317414917522787506618035)
            ·
              refine ⟨52976122376284181259927053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35317414917522787506618035 52976122376284181259927053)
              ·
                refine ⟨19866045891106567972472645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52976122376284181259927053 19866045891106567972472645)
                ·
                  refine ⟨3724883604582481494838621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19866045891106567972472645 3724883604582481494838621)
                  ·
                    refine ⟨1396831351718430560564483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724883604582481494838621 1396831351718430560564483)
                    ·
                      rfl

theorem cell22_4080479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_4080479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080479 prefixEnd_4080479 := by exact prefixLift 4080479
  have htrace : WordTrace (prefixWord ++ tailWord_4080479) baseStart_4080479 baseEnd_4080479 := by
    simpa [prefixWord, tailWord_4080479, baseEnd_4080479] using wordTrace_append hprefix tailTrace_4080479
  have hstable : (prefixWord ++ tailWord_4080479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080479).length < 2 ^ (prefixWord ++ tailWord_4080479).sum := by decide
  have hdescent : baseEnd_4080479 < baseStart_4080479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080507 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_4080507 : Nat := 118140960795 + 4080507 * 2 ^ 59
def prefixEnd_4080507 : Nat := 4983230072969 + 3 ^ 40 * 4080507 * 2
def baseEnd_4080507 : Nat := 1396840936690647820864397

theorem tailTrace_4080507 : CollatzResearch.WordTrace tailWord_4080507 prefixEnd_4080507 1396840936690647820864397 := by
  unfold tailWord_4080507
  simp only [CollatzResearch.WordTrace]
  refine ⟨148828317028027508958055775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99218878018685005972037183 148828317028027508958055775)
  ·
    refine ⟨223242475542041263437083663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148828317028027508958055775 223242475542041263437083663)
    ·
      refine ⟨334863713313061895155625495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223242475542041263437083663 334863713313061895155625495)
      ·
        refine ⟨502295569969592842733438243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334863713313061895155625495 502295569969592842733438243)
        ·
          refine ⟨753443354954389264100157365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502295569969592842733438243 753443354954389264100157365)
          ·
            refine ⟨70635314526973993509389753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 753443354954389264100157365 70635314526973993509389753)
            ·
              refine ⟨52976485895230495132042315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70635314526973993509389753 52976485895230495132042315)
              ·
                refine ⟨79464728842845742698063473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52976485895230495132042315 79464728842845742698063473)
                ·
                  refine ⟨59598546632134307023547605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79464728842845742698063473 59598546632134307023547605)
                  ·
                    refine ⟨1396840936690647820864397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59598546632134307023547605 1396840936690647820864397)
                    ·
                      rfl

theorem cell22_4080507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_4080507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080507 prefixEnd_4080507 := by exact prefixLift 4080507
  have htrace : WordTrace (prefixWord ++ tailWord_4080507) baseStart_4080507 baseEnd_4080507 := by
    simpa [prefixWord, tailWord_4080507, baseEnd_4080507] using wordTrace_append hprefix tailTrace_4080507
  have hstable : (prefixWord ++ tailWord_4080507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080507).length < 2 ^ (prefixWord ++ tailWord_4080507).sum := by decide
  have hdescent : baseEnd_4080507 < baseStart_4080507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080530 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4080530 : Nat := 118140960795 + 4080530 * 2 ^ 59
def prefixEnd_4080530 : Nat := 4983230072969 + 3 ^ 40 * 4080530 * 2
def baseEnd_4080530 : Nat := 1396848810060683427539327

theorem tailTrace_4080530 : CollatzResearch.WordTrace tailWord_4080530 prefixEnd_4080530 1396848810060683427539327 := by
  unfold tailWord_4080530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207288976736045971535761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99219437271296122590762029 37207288976736045971535761)
  ·
    refine ⟨27905466732552034478651821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37207288976736045971535761 27905466732552034478651821)
    ·
      refine ⟨10464550024707012929494433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27905466732552034478651821 10464550024707012929494433)
      ·
        refine ⟨7848412518530259697120825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10464550024707012929494433 7848412518530259697120825)
        ·
          refine ⟨5886309388897694772840619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7848412518530259697120825 5886309388897694772840619)
          ·
            refine ⟨8829464083346542159260929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886309388897694772840619 8829464083346542159260929)
            ·
              refine ⟨6622098062509906619445697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829464083346542159260929 6622098062509906619445697)
              ·
                refine ⟨4966573546882429964584273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622098062509906619445697 4966573546882429964584273)
                ·
                  refine ⟨3724930160161822473438205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966573546882429964584273 3724930160161822473438205)
                  ·
                    refine ⟨1396848810060683427539327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724930160161822473438205 1396848810060683427539327)
                    ·
                      rfl

theorem cell22_4080530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4080530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080530 prefixEnd_4080530 := by exact prefixLift 4080530
  have htrace : WordTrace (prefixWord ++ tailWord_4080530) baseStart_4080530 baseEnd_4080530 := by
    simpa [prefixWord, tailWord_4080530, baseEnd_4080530] using wordTrace_append hprefix tailTrace_4080530
  have hstable : (prefixWord ++ tailWord_4080530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080530).length < 2 ^ (prefixWord ++ tailWord_4080530).sum := by decide
  have hdescent : baseEnd_4080530 < baseStart_4080530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080541 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_4080541 : Nat := 118140960795 + 4080541 * 2 ^ 59
def prefixEnd_4080541 : Nat := 4983230072969 + 3 ^ 40 * 4080541 * 2
def baseEnd_4080541 : Nat := 1396852575585483065514293

theorem tailTrace_4080541 : CollatzResearch.WordTrace tailWord_4080541 prefixEnd_4080541 1396852575585483065514293 := by
  unfold tailWord_4080541
  simp only [CollatzResearch.WordTrace]
  refine ⟨148829557109904332764793477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99219704739936221843195651 148829557109904332764793477)
  ·
    refine ⟨27905541958107062393398777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148829557109904332764793477 27905541958107062393398777)
    ·
      refine ⟨20929156468580296795049083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27905541958107062393398777 20929156468580296795049083)
      ·
        refine ⟨31393734702870445192573625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20929156468580296795049083 31393734702870445192573625)
        ·
          refine ⟨23545301027152833894430219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31393734702870445192573625 23545301027152833894430219)
          ·
            refine ⟨35317951540729250841645329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23545301027152833894430219 35317951540729250841645329)
            ·
              refine ⟨26488463655546938131233997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35317951540729250841645329 26488463655546938131233997)
              ·
                refine ⟨9933173870830101799212749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26488463655546938131233997 9933173870830101799212749)
                ·
                  refine ⟨3724940201561288174704781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9933173870830101799212749 3724940201561288174704781)
                  ·
                    refine ⟨1396852575585483065514293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724940201561288174704781 1396852575585483065514293)
                    ·
                      rfl

theorem cell22_4080541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_4080541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080541 prefixEnd_4080541 := by exact prefixLift 4080541
  have htrace : WordTrace (prefixWord ++ tailWord_4080541) baseStart_4080541 baseEnd_4080541 := by
    simpa [prefixWord, tailWord_4080541, baseEnd_4080541] using wordTrace_append hprefix tailTrace_4080541
  have hstable : (prefixWord ++ tailWord_4080541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080541).length < 2 ^ (prefixWord ++ tailWord_4080541).sum := by decide
  have hdescent : baseEnd_4080541 < baseStart_4080541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080618 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_4080618 : Nat := 118140960795 + 4080618 * 2 ^ 59
def prefixEnd_4080618 : Nat := 4983230072969 + 3 ^ 40 * 4080618 * 2
def baseEnd_4080618 : Nat := 1396878934259080531339057

theorem tailTrace_4080618 : CollatzResearch.WordTrace tailWord_4080618 prefixEnd_4080618 1396878934259080531339057 := by
  unfold tailWord_4080618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37208091382656343728836627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99221577020416916610231005 37208091382656343728836627)
  ·
    refine ⟨55812137073984515593254941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37208091382656343728836627 55812137073984515593254941)
    ·
      refine ⟨20929551402744193347470603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55812137073984515593254941 20929551402744193347470603)
      ·
        refine ⟨31394327104116290021205905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20929551402744193347470603 31394327104116290021205905)
        ·
          refine ⟨23545745328087217515904429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31394327104116290021205905 23545745328087217515904429)
          ·
            refine ⟨8829654498032706568464161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23545745328087217515904429 8829654498032706568464161)
            ·
              refine ⟨6622240873524529926348121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829654498032706568464161 6622240873524529926348121)
              ·
                refine ⟨4966680655143397444761091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622240873524529926348121 4966680655143397444761091)
                ·
                  refine ⟨7450020982715096167141637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966680655143397444761091 7450020982715096167141637)
                  ·
                    refine ⟨1396878934259080531339057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7450020982715096167141637 1396878934259080531339057)
                    ·
                      rfl

theorem cell22_4080618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_4080618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080618 prefixEnd_4080618 := by exact prefixLift 4080618
  have htrace : WordTrace (prefixWord ++ tailWord_4080618) baseStart_4080618 baseEnd_4080618 := by
    simpa [prefixWord, tailWord_4080618, baseEnd_4080618] using wordTrace_append hprefix tailTrace_4080618
  have hstable : (prefixWord ++ tailWord_4080618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080618).length < 2 ^ (prefixWord ++ tailWord_4080618).sum := by decide
  have hdescent : baseEnd_4080618 < baseStart_4080618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080650 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_4080650 : Nat := 118140960795 + 4080650 * 2 ^ 59
def prefixEnd_4080650 : Nat := 4983230072969 + 3 ^ 40 * 4080650 * 2
def baseEnd_4080650 : Nat := 465629962837681038179653

theorem tailTrace_4080650 : CollatzResearch.WordTrace tailWord_4080650 prefixEnd_4080650 465629962837681038179653 := by
  unfold tailWord_4080650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37208383166627361095127851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99222355111006296253674269 37208383166627361095127851)
  ·
    refine ⟨55812574749941041642691777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37208383166627361095127851 55812574749941041642691777)
    ·
      refine ⟨41859431062455781232018833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55812574749941041642691777 41859431062455781232018833)
      ·
        refine ⟨31394573296841835924014125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41859431062455781232018833 31394573296841835924014125)
        ·
          refine ⟨11772964986315688471505297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31394573296841835924014125 11772964986315688471505297)
          ·
            refine ⟨8829723739736766353628973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11772964986315688471505297 8829723739736766353628973)
            ·
              refine ⟨3311146402401287382610865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8829723739736766353628973 3311146402401287382610865)
              ·
                refine ⟨2483359801800965536958149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311146402401287382610865 2483359801800965536958149)
                ·
                  refine ⟨465629962837681038179653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483359801800965536958149 465629962837681038179653)
                  ·
                    rfl

theorem cell22_4080650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_4080650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080650 prefixEnd_4080650 := by exact prefixLift 4080650
  have htrace : WordTrace (prefixWord ++ tailWord_4080650) baseStart_4080650 baseEnd_4080650 := by
    simpa [prefixWord, tailWord_4080650, baseEnd_4080650] using wordTrace_append hprefix tailTrace_4080650
  have hstable : (prefixWord ++ tailWord_4080650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080650).length < 2 ^ (prefixWord ++ tailWord_4080650).sum := by decide
  have hdescent : baseEnd_4080650 < baseStart_4080650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080661 : List Nat := [1, 3, 2, 1, 4, 2, 2, 7]
def baseStart_4080661 : Nat := 118140960795 + 4080661 * 2 ^ 59
def prefixEnd_4080661 : Nat := 4983230072969 + 3 ^ 40 * 4080661 * 2
def baseEnd_4080661 : Nat := 155210406004204750279325

theorem tailTrace_4080661 : CollatzResearch.WordTrace tailWord_4080661 prefixEnd_4080661 155210406004204750279325 := by
  unfold tailWord_4080661
  simp only [CollatzResearch.WordTrace]
  refine ⟨148833933869469593259161837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99222622579646395506107891 148833933869469593259161837)
  ·
    refine ⟨55812725201051097472185689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148833933869469593259161837 55812725201051097472185689)
    ·
      refine ⟨41859543900788323104139267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55812725201051097472185689 41859543900788323104139267)
      ·
        refine ⟨62789315851182484656208901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41859543900788323104139267 62789315851182484656208901)
        ·
          refine ⟨11772996722096715873039169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62789315851182484656208901 11772996722096715873039169)
          ·
            refine ⟨8829747541572536904779377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11772996722096715873039169 8829747541572536904779377)
            ·
              refine ⟨6622310656179402678584533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829747541572536904779377 6622310656179402678584533)
              ·
                refine ⟨155210406004204750279325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6622310656179402678584533 155210406004204750279325)
                ·
                  rfl

theorem cell22_4080661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 7].length) (baseStart_4080661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080661 prefixEnd_4080661 := by exact prefixLift 4080661
  have htrace : WordTrace (prefixWord ++ tailWord_4080661) baseStart_4080661 baseEnd_4080661 := by
    simpa [prefixWord, tailWord_4080661, baseEnd_4080661] using wordTrace_append hprefix tailTrace_4080661
  have hstable : (prefixWord ++ tailWord_4080661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080661).length < 2 ^ (prefixWord ++ tailWord_4080661).sum := by decide
  have hdescent : baseEnd_4080661 < baseStart_4080661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080719 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_4080719 : Nat := 118140960795 + 4080719 * 2 ^ 59
def prefixEnd_4080719 : Nat := 4983230072969 + 3 ^ 40 * 4080719 * 2
def baseEnd_4080719 : Nat := 1396913508623149934563747

theorem tailTrace_4080719 : CollatzResearch.WordTrace tailWord_4080719 prefixEnd_4080719 1396913508623149934563747 := by
  unfold tailWord_4080719
  simp only [CollatzResearch.WordTrace]
  refine ⟨148836049303259469164773211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99224032868839646109848807 148836049303259469164773211)
  ·
    refine ⟨223254073954889203747159817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148836049303259469164773211 223254073954889203747159817)
    ·
      refine ⟨167440555466166902810369863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223254073954889203747159817 167440555466166902810369863)
      ·
        refine ⟨251160833199250354215554795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167440555466166902810369863 251160833199250354215554795)
        ·
          refine ⟨376741249798875531323332193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251160833199250354215554795 376741249798875531323332193)
          ·
            refine ⟨282555937349156648492499145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376741249798875531323332193 282555937349156648492499145)
            ·
              refine ⟨211916953011867486369374359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282555937349156648492499145 211916953011867486369374359)
              ·
                refine ⟨317875429517801229554061539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211916953011867486369374359 317875429517801229554061539)
                ·
                  refine ⟨476813144276701844331092309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317875429517801229554061539 476813144276701844331092309)
                  ·
                    refine ⟨1396913508623149934563747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 476813144276701844331092309 1396913508623149934563747)
                    ·
                      rfl

theorem cell22_4080719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_4080719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080719 prefixEnd_4080719 := by exact prefixLift 4080719
  have htrace : WordTrace (prefixWord ++ tailWord_4080719) baseStart_4080719 baseEnd_4080719 := by
    simpa [prefixWord, tailWord_4080719, baseEnd_4080719] using wordTrace_append hprefix tailTrace_4080719
  have hstable : (prefixWord ++ tailWord_4080719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080719).length < 2 ^ (prefixWord ++ tailWord_4080719).sum := by decide
  have hdescent : baseEnd_4080719 < baseStart_4080719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080736 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_4080736 : Nat := 118140960795 + 4080736 * 2 ^ 59
def prefixEnd_4080736 : Nat := 4983230072969 + 3 ^ 40 * 4080736 * 2
def baseEnd_4080736 : Nat := 1396919328070567556888695

theorem tailTrace_4080736 : CollatzResearch.WordTrace tailWord_4080736 prefixEnd_4080736 1396919328070567556888695 := by
  unfold tailWord_4080736
  simp only [CollatzResearch.WordTrace]
  refine ⟨74418334672098940534071031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99224446229465254045428041 74418334672098940534071031)
  ·
    refine ⟨111627502008148410801106547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74418334672098940534071031 111627502008148410801106547)
    ·
      refine ⟨167441253012222616201659821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111627502008148410801106547 167441253012222616201659821)
      ·
        refine ⟨62790469879583481075622433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167441253012222616201659821 62790469879583481075622433)
        ·
          refine ⟨47092852409687610806716825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62790469879583481075622433 47092852409687610806716825)
          ·
            refine ⟨35319639307265708105037619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47092852409687610806716825 35319639307265708105037619)
            ·
              refine ⟨52979458960898562157556429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35319639307265708105037619 52979458960898562157556429)
              ·
                refine ⟨19867297110336960809083661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52979458960898562157556429 19867297110336960809083661)
                ·
                  refine ⟨7450236416376360303406373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19867297110336960809083661 7450236416376360303406373)
                  ·
                    refine ⟨1396919328070567556888695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7450236416376360303406373 1396919328070567556888695)
                    ·
                      rfl

theorem cell22_4080736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_4080736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080736 prefixEnd_4080736 := by exact prefixLift 4080736
  have htrace : WordTrace (prefixWord ++ tailWord_4080736) baseStart_4080736 baseEnd_4080736 := by
    simpa [prefixWord, tailWord_4080736, baseEnd_4080736] using wordTrace_append hprefix tailTrace_4080736
  have hstable : (prefixWord ++ tailWord_4080736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080736).length < 2 ^ (prefixWord ++ tailWord_4080736).sum := by decide
  have hdescent : baseEnd_4080736 < baseStart_4080736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080744 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 1, 3]
def baseStart_4080744 : Nat := 118140960795 + 4080744 * 2 ^ 59
def prefixEnd_4080744 : Nat := 4983230072969 + 3 ^ 40 * 4080744 * 2
def baseEnd_4080744 : Nat := 1396922066634058202688671

theorem tailTrace_4080744 : CollatzResearch.WordTrace tailWord_4080744 prefixEnd_4080744 1396922066634058202688671 := by
  unfold tailWord_4080744
  simp only [CollatzResearch.WordTrace]
  refine ⟨74418480564084449217216643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99224640752112598956288857 74418480564084449217216643)
  ·
    refine ⟨111627720846126673825824965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74418480564084449217216643 111627720846126673825824965)
    ·
      refine ⟨20930197658648751342342181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111627720846126673825824965 20930197658648751342342181)
      ·
        refine ⟨3924412060996640876689159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20930197658648751342342181 3924412060996640876689159)
        ·
          refine ⟨5886618091494961315033739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924412060996640876689159 5886618091494961315033739)
          ·
            refine ⟨8829927137242441972550609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886618091494961315033739 8829927137242441972550609)
            ·
              refine ⟨6622445352931831479412957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829927137242441972550609 6622445352931831479412957)
              ·
                refine ⟨2483417007349436804779859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6622445352931831479412957 2483417007349436804779859)
                ·
                  refine ⟨3725125511024155207169789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483417007349436804779859 3725125511024155207169789)
                  ·
                    refine ⟨1396922066634058202688671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725125511024155207169789 1396922066634058202688671)
                    ·
                      rfl

theorem cell22_4080744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_4080744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080744 prefixEnd_4080744 := by exact prefixLift 4080744
  have htrace : WordTrace (prefixWord ++ tailWord_4080744) baseStart_4080744 baseEnd_4080744 := by
    simpa [prefixWord, tailWord_4080744, baseEnd_4080744] using wordTrace_append hprefix tailTrace_4080744
  have hstable : (prefixWord ++ tailWord_4080744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080744).length < 2 ^ (prefixWord ++ tailWord_4080744).sum := by decide
  have hdescent : baseEnd_4080744 < baseStart_4080744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080757 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 5]
def baseStart_4080757 : Nat := 118140960795 + 4080757 * 2 ^ 59
def prefixEnd_4080757 : Nat := 4983230072969 + 3 ^ 40 * 4080757 * 2
def baseEnd_4080757 : Nat := 465642172266576834037877

theorem tailTrace_4080757 : CollatzResearch.WordTrace tailWord_4080757 prefixEnd_4080757 465642172266576834037877 := by
  unfold tailWord_4080757
  simp only [CollatzResearch.WordTrace]
  refine ⟨148837435277121801654656525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99224956851414534436437683 148837435277121801654656525)
  ·
    refine ⟨55814038228920675620496197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148837435277121801654656525 55814038228920675620496197)
    ·
      refine ⟨10465132167922626678843037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55814038228920675620496197 10465132167922626678843037)
      ·
        refine ⟨3924424562970985004566139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10465132167922626678843037 3924424562970985004566139)
        ·
          refine ⟨5886636844456477506849209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924424562970985004566139 5886636844456477506849209)
          ·
            refine ⟨4414977633342358130136907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5886636844456477506849209 4414977633342358130136907)
            ·
              refine ⟨6622466450013537195205361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414977633342358130136907 6622466450013537195205361)
              ·
                refine ⟨4966849837510152896404021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622466450013537195205361 4966849837510152896404021)
                ·
                  refine ⟨465642172266576834037877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966849837510152896404021 465642172266576834037877)
                  ·
                    rfl

theorem cell22_4080757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_4080757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080757 prefixEnd_4080757 := by exact prefixLift 4080757
  have htrace : WordTrace (prefixWord ++ tailWord_4080757) baseStart_4080757 baseEnd_4080757 := by
    simpa [prefixWord, tailWord_4080757, baseEnd_4080757] using wordTrace_append hprefix tailTrace_4080757
  have hstable : (prefixWord ++ tailWord_4080757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080757).length < 2 ^ (prefixWord ++ tailWord_4080757).sum := by decide
  have hdescent : baseEnd_4080757 < baseStart_4080757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080768 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_4080768 : Nat := 118140960795 + 4080768 * 2 ^ 59
def prefixEnd_4080768 : Nat := 4983230072969 + 3 ^ 40 * 4080768 * 2
def baseEnd_4080768 : Nat := 465643427441510046696199

theorem tailTrace_4080768 : CollatzResearch.WordTrace tailWord_4080768 prefixEnd_4080768 465643427441510046696199 := by
  unfold tailWord_4080768
  simp only [CollatzResearch.WordTrace]
  refine ⟨74418918240040975266653479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99225224320054633688871305 74418918240040975266653479)
  ·
    refine ⟨111628377360061462899980219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74418918240040975266653479 111628377360061462899980219)
    ·
      refine ⟨167442566040092194349970329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111628377360061462899980219 167442566040092194349970329)
      ·
        refine ⟨125581924530069145762477747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167442566040092194349970329 125581924530069145762477747)
        ·
          refine ⟨188372886795103718643716621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125581924530069145762477747 188372886795103718643716621)
          ·
            refine ⟨70639832548163894491393733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188372886795103718643716621 70639832548163894491393733)
            ·
              refine ⟨13244968602780730217136325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70639832548163894491393733 13244968602780730217136325)
              ·
                refine ⟨2483431613021386915713061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13244968602780730217136325 2483431613021386915713061)
                ·
                  refine ⟨465643427441510046696199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483431613021386915713061 465643427441510046696199)
                  ·
                    rfl

theorem cell22_4080768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_4080768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080768 prefixEnd_4080768 := by exact prefixLift 4080768
  have htrace : WordTrace (prefixWord ++ tailWord_4080768) baseStart_4080768 baseEnd_4080768 := by
    simpa [prefixWord, tailWord_4080768, baseEnd_4080768] using wordTrace_append hprefix tailTrace_4080768
  have hstable : (prefixWord ++ tailWord_4080768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080768).length < 2 ^ (prefixWord ++ tailWord_4080768).sum := by decide
  have hdescent : baseEnd_4080768 < baseStart_4080768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080826 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_4080826 : Nat := 118140960795 + 4080826 * 2 ^ 59
def prefixEnd_4080826 : Nat := 4983230072969 + 3 ^ 40 * 4080826 * 2
def baseEnd_4080826 : Nat := 1396950136909837322138419

theorem tailTrace_4080826 : CollatzResearch.WordTrace tailWord_4080826 prefixEnd_4080826 1396950136909837322138419 := by
  unfold tailWord_4080826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37209987978467956609729583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99226634609247884292612221 37209987978467956609729583)
  ·
    refine ⟨55814981967701934914594375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37209987978467956609729583 55814981967701934914594375)
    ·
      refine ⟨83722472951552902371891563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55814981967701934914594375 83722472951552902371891563)
      ·
        refine ⟨125583709427329353557837345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83722472951552902371891563 125583709427329353557837345)
        ·
          refine ⟨94187782070497015168378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125583709427329353557837345 94187782070497015168378009)
          ·
            refine ⟨70640836552872761376283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94187782070497015168378009 70640836552872761376283507)
            ·
              refine ⟨105961254829309142064425261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70640836552872761376283507 105961254829309142064425261)
              ·
                refine ⟨39735470560990928274159473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105961254829309142064425261 39735470560990928274159473)
                ·
                  refine ⟨29801602920743196205619605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39735470560990928274159473 29801602920743196205619605)
                  ·
                    refine ⟨1396950136909837322138419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29801602920743196205619605 1396950136909837322138419)
                    ·
                      rfl

theorem cell22_4080826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_4080826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080826 prefixEnd_4080826 := by exact prefixLift 4080826
  have htrace : WordTrace (prefixWord ++ tailWord_4080826) baseStart_4080826 baseEnd_4080826 := by
    simpa [prefixWord, tailWord_4080826, baseEnd_4080826] using wordTrace_append hprefix tailTrace_4080826
  have hstable : (prefixWord ++ tailWord_4080826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080826).length < 2 ^ (prefixWord ++ tailWord_4080826).sum := by decide
  have hdescent : baseEnd_4080826 < baseStart_4080826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080838 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4080838 : Nat := 118140960795 + 4080838 * 2 ^ 59
def prefixEnd_4080838 : Nat := 4983230072969 + 3 ^ 40 * 4080838 * 2
def baseEnd_4080838 : Nat := 1396954244755073290838383

theorem tailTrace_4080838 : CollatzResearch.WordTrace tailWord_4080838 prefixEnd_4080838 1396954244755073290838383 := by
  unfold tailWord_4080838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651262174682136015261099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99226926393218901658903445 4651262174682136015261099)
  ·
    refine ⟨6976893262023204022891649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4651262174682136015261099 6976893262023204022891649)
    ·
      refine ⟨5232669946517403017168737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6976893262023204022891649 5232669946517403017168737)
      ·
        refine ⟨3924502459888052262876553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5232669946517403017168737 3924502459888052262876553)
        ·
          refine ⟨2943376844916039197157415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3924502459888052262876553 2943376844916039197157415)
          ·
            refine ⟨4415065267374058795736123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943376844916039197157415 4415065267374058795736123)
            ·
              refine ⟨6622597901061088193604185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415065267374058795736123 6622597901061088193604185)
              ·
                refine ⟨4966948425795816145203139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622597901061088193604185 4966948425795816145203139)
                ·
                  refine ⟨7450422638693724217804709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966948425795816145203139 7450422638693724217804709)
                  ·
                    refine ⟨1396954244755073290838383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7450422638693724217804709 1396954244755073290838383)
                    ·
                      rfl

theorem cell22_4080838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4080838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080838 prefixEnd_4080838 := by exact prefixLift 4080838
  have htrace : WordTrace (prefixWord ++ tailWord_4080838) baseStart_4080838 baseEnd_4080838 := by
    simpa [prefixWord, tailWord_4080838, baseEnd_4080838] using wordTrace_append hprefix tailTrace_4080838
  have hstable : (prefixWord ++ tailWord_4080838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080838).length < 2 ^ (prefixWord ++ tailWord_4080838).sum := by decide
  have hdescent : baseEnd_4080838 < baseStart_4080838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080920 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_4080920 : Nat := 118140960795 + 4080920 * 2 ^ 59
def prefixEnd_4080920 : Nat := 4983230072969 + 3 ^ 40 * 4080920 * 2
def baseEnd_4080920 : Nat := 465660771676950803429377

theorem tailTrace_4080920 : CollatzResearch.WordTrace tailWord_4080920 prefixEnd_4080920 465660771676950803429377 := by
  unfold tailWord_4080920
  simp only [CollatzResearch.WordTrace]
  refine ⟨74421690187765640246420107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99228920250354186995226809 74421690187765640246420107)
  ·
    refine ⟨111632535281648460369630161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74421690187765640246420107 111632535281648460369630161)
    ·
      refine ⟨83724401461236345277222621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111632535281648460369630161 83724401461236345277222621)
      ·
        refine ⟨31396650547963629478958483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83724401461236345277222621 31396650547963629478958483)
        ·
          refine ⟨47094975821945444218437725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31396650547963629478958483 47094975821945444218437725)
          ·
            refine ⟨17660615933229541581914147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47094975821945444218437725 17660615933229541581914147)
            ·
              refine ⟨26490923899844312372871221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17660615933229541581914147 26490923899844312372871221)
              ·
                refine ⟨2483524115610404284956677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26490923899844312372871221 2483524115610404284956677)
                ·
                  refine ⟨465660771676950803429377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483524115610404284956677 465660771676950803429377)
                  ·
                    rfl

theorem cell22_4080920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_4080920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080920 prefixEnd_4080920 := by exact prefixLift 4080920
  have htrace : WordTrace (prefixWord ++ tailWord_4080920) baseStart_4080920 baseEnd_4080920 := by
    simpa [prefixWord, tailWord_4080920, baseEnd_4080920] using wordTrace_append hprefix tailTrace_4080920
  have hstable : (prefixWord ++ tailWord_4080920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080920).length < 2 ^ (prefixWord ++ tailWord_4080920).sum := by decide
  have hdescent : baseEnd_4080920 < baseStart_4080920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080922 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_4080922 : Nat := 118140960795 + 4080922 * 2 ^ 59
def prefixEnd_4080922 : Nat := 4983230072969 + 3 ^ 40 * 4080922 * 2
def baseEnd_4080922 : Nat := 1396982999671725071738125

theorem tailTrace_4080922 : CollatzResearch.WordTrace tailWord_4080922 prefixEnd_4080922 1396982999671725071738125 := by
  unfold tailWord_4080922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37210863330381008708603255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99228968881016023222942013 37210863330381008708603255)
  ·
    refine ⟨55816294995571513062904883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37210863330381008708603255 55816294995571513062904883)
    ·
      refine ⟨83724442493357269594357325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55816294995571513062904883 83724442493357269594357325)
      ·
        refine ⟨31396665935008976097883997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83724442493357269594357325 31396665935008976097883997)
        ·
          refine ⟨11773749725628366036706499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31396665935008976097883997 11773749725628366036706499)
          ·
            refine ⟨17660624588442549055059749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773749725628366036706499 17660624588442549055059749)
            ·
              refine ⟨3311367110332977947823703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17660624588442549055059749 3311367110332977947823703)
              ·
                refine ⟨4967050665499466921735555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311367110332977947823703 4967050665499466921735555)
                ·
                  refine ⟨7450575998249200382603333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967050665499466921735555 7450575998249200382603333)
                  ·
                    refine ⟨1396982999671725071738125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7450575998249200382603333 1396982999671725071738125)
                    ·
                      rfl

theorem cell22_4080922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_4080922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080922 prefixEnd_4080922 := by exact prefixLift 4080922
  have htrace : WordTrace (prefixWord ++ tailWord_4080922) baseStart_4080922 baseEnd_4080922 := by
    simpa [prefixWord, tailWord_4080922, baseEnd_4080922] using wordTrace_append hprefix tailTrace_4080922
  have hstable : (prefixWord ++ tailWord_4080922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080922).length < 2 ^ (prefixWord ++ tailWord_4080922).sum := by decide
  have hdescent : baseEnd_4080922 < baseStart_4080922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080926 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4080926 : Nat := 118140960795 + 4080926 * 2 ^ 59
def prefixEnd_4080926 : Nat := 4983230072969 + 3 ^ 40 * 4080926 * 2
def baseEnd_4080926 : Nat := 465661456317823464879371

theorem tailTrace_4080926 : CollatzResearch.WordTrace tailWord_4080926 prefixEnd_4080926 465661456317823464879371 := by
  unfold tailWord_4080926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605449901688692939694829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99229066142339695678372421 18605449901688692939694829)
  ·
    refine ⟨6977043713133259852385561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18605449901688692939694829 6977043713133259852385561)
    ·
      refine ⟨5232782784849944889289171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6977043713133259852385561 5232782784849944889289171)
      ·
        refine ⟨7849174177274917333933757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232782784849944889289171 7849174177274917333933757)
        ·
          refine ⟨2943440316478094000225159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7849174177274917333933757 2943440316478094000225159)
          ·
            refine ⟨4415160474717141000337739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943440316478094000225159 4415160474717141000337739)
            ·
              refine ⟨6622740712075711500506609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415160474717141000337739 6622740712075711500506609)
              ·
                refine ⟨4967055534056783625379957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622740712075711500506609 4967055534056783625379957)
                ·
                  refine ⟨465661456317823464879371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4967055534056783625379957 465661456317823464879371)
                  ·
                    rfl

theorem cell22_4080926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4080926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080926 prefixEnd_4080926 := by exact prefixLift 4080926
  have htrace : WordTrace (prefixWord ++ tailWord_4080926) baseStart_4080926 baseEnd_4080926 := by
    simpa [prefixWord, tailWord_4080926, baseEnd_4080926] using wordTrace_append hprefix tailTrace_4080926
  have hstable : (prefixWord ++ tailWord_4080926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080926).length < 2 ^ (prefixWord ++ tailWord_4080926).sum := by decide
  have hdescent : baseEnd_4080926 < baseStart_4080926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080978 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4080978 : Nat := 118140960795 + 4080978 * 2 ^ 59
def prefixEnd_4080978 : Nat := 4983230072969 + 3 ^ 40 * 4080978 * 2
def baseEnd_4080978 : Nat := 1397002169616159592337953

theorem tailTrace_4080978 : CollatzResearch.WordTrace tailWord_4080978 prefixEnd_4080978 1397002169616159592337953 := by
  unfold tailWord_4080978
  simp only [CollatzResearch.WordTrace]
  refine ⟨37211373952330289099612897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99230330539547437598967725 37211373952330289099612897)
  ·
    refine ⟨27908530464247716824709673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37211373952330289099612897 27908530464247716824709673)
    ·
      refine ⟨20931397848185787618532255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27908530464247716824709673 20931397848185787618532255)
      ·
        refine ⟨31397096772278681427798383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20931397848185787618532255 31397096772278681427798383)
        ·
          refine ⟨47095645158418022141697575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31397096772278681427798383 47095645158418022141697575)
          ·
            refine ⟨70643467737627033212546363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47095645158418022141697575 70643467737627033212546363)
            ·
              refine ⟨105965201606440549818819545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70643467737627033212546363 105965201606440549818819545)
              ·
                refine ⟨79473901204830412364114659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105965201606440549818819545 79473901204830412364114659)
                ·
                  refine ⟨119210851807245618546171989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79473901204830412364114659 119210851807245618546171989)
                  ·
                    refine ⟨1397002169616159592337953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119210851807245618546171989 1397002169616159592337953)
                    ·
                      rfl

theorem cell22_4080978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4080978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4080978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4080978 prefixEnd_4080978 := by exact prefixLift 4080978
  have htrace : WordTrace (prefixWord ++ tailWord_4080978) baseStart_4080978 baseEnd_4080978 := by
    simpa [prefixWord, tailWord_4080978, baseEnd_4080978] using wordTrace_append hprefix tailTrace_4080978
  have hstable : (prefixWord ++ tailWord_4080978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080978).length < 2 ^ (prefixWord ++ tailWord_4080978).sum := by decide
  have hdescent : baseEnd_4080978 < baseStart_4080978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081008 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_4081008 : Nat := 118140960795 + 4081008 * 2 ^ 59
def prefixEnd_4081008 : Nat := 4983230072969 + 3 ^ 40 * 4081008 * 2
def baseEnd_4081008 : Nat := 1397012439229249514087861

theorem tailTrace_4081008 : CollatzResearch.WordTrace tailWord_4081008 prefixEnd_4081008 1397012439229249514087861 := by
  unfold tailWord_4081008
  simp only [CollatzResearch.WordTrace]
  refine ⟨74423294999606235761021839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99231059999474981014695785 74423294999606235761021839)
  ·
    refine ⟨111634942499409353641532759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74423294999606235761021839 111634942499409353641532759)
    ·
      refine ⟨167452413749114030462299139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111634942499409353641532759 167452413749114030462299139)
      ·
        refine ⟨251178620623671045693448709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167452413749114030462299139 251178620623671045693448709)
        ·
          refine ⟨47095991366938321067521633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251178620623671045693448709 47095991366938321067521633)
          ·
            refine ⟨35321993525203740800641225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47095991366938321067521633 35321993525203740800641225)
            ·
              refine ⟨26491495143902805600480919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35321993525203740800641225 26491495143902805600480919)
              ·
                refine ⟨39737242715854208400721379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26491495143902805600480919 39737242715854208400721379)
                ·
                  refine ⟨59605864073781312601082069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39737242715854208400721379 59605864073781312601082069)
                  ·
                    refine ⟨1397012439229249514087861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59605864073781312601082069 1397012439229249514087861)
                    ·
                      rfl

theorem cell22_4081008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_4081008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081008 prefixEnd_4081008 := by exact prefixLift 4081008
  have htrace : WordTrace (prefixWord ++ tailWord_4081008) baseStart_4081008 baseEnd_4081008 := by
    simpa [prefixWord, tailWord_4081008, baseEnd_4081008] using wordTrace_append hprefix tailTrace_4081008
  have hstable : (prefixWord ++ tailWord_4081008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081008).length < 2 ^ (prefixWord ++ tailWord_4081008).sum := by decide
  have hdescent : baseEnd_4081008 < baseStart_4081008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081010 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_4081010 : Nat := 118140960795 + 4081010 * 2 ^ 59
def prefixEnd_4081010 : Nat := 4983230072969 + 3 ^ 40 * 4081010 * 2
def baseEnd_4081010 : Nat := 465671041290040725179285

theorem tailTrace_4081010 : CollatzResearch.WordTrace tailWord_4081010 prefixEnd_4081010 465671041290040725179285 := by
  unfold tailWord_4081010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37211665736301306465904121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99231108630136817242410989 37211665736301306465904121)
  ·
    refine ⟨27908749302225979849428091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37211665736301306465904121 27908749302225979849428091)
    ·
      refine ⟨41863123953338969774142137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27908749302225979849428091 41863123953338969774142137)
      ·
        refine ⟨31397342965004227330606603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41863123953338969774142137 31397342965004227330606603)
        ·
          refine ⟨47096014447506340995909905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31397342965004227330606603 47096014447506340995909905)
          ·
            refine ⟨35322010835629755746932429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47096014447506340995909905 35322010835629755746932429)
            ·
              refine ⟨13245754063361158405099661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35322010835629755746932429 13245754063361158405099661)
              ·
                refine ⟨4967157773760434401912373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13245754063361158405099661 4967157773760434401912373)
                ·
                  refine ⟨465671041290040725179285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4967157773760434401912373 465671041290040725179285)
                  ·
                    rfl

theorem cell22_4081010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_4081010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081010 prefixEnd_4081010 := by exact prefixLift 4081010
  have htrace : WordTrace (prefixWord ++ tailWord_4081010) baseStart_4081010 baseEnd_4081010 := by
    simpa [prefixWord, tailWord_4081010, baseEnd_4081010] using wordTrace_append hprefix tailTrace_4081010
  have hstable : (prefixWord ++ tailWord_4081010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081010).length < 2 ^ (prefixWord ++ tailWord_4081010).sum := by decide
  have hdescent : baseEnd_4081010 < baseStart_4081010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081048 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 1, 3]
def baseStart_4081048 : Nat := 118140960795 + 4081048 * 2 ^ 59
def prefixEnd_4081048 : Nat := 4983230072969 + 3 ^ 40 * 4081048 * 2
def baseEnd_4081048 : Nat := 1397026132046702743087739

theorem tailTrace_4081048 : CollatzResearch.WordTrace tailWord_4081048 prefixEnd_4081048 1397026132046702743087739 := by
  unfold tailWord_4081048
  simp only [CollatzResearch.WordTrace]
  refine ⟨74424024459533779176749899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99232032612711705568999865 74424024459533779176749899)
  ·
    refine ⟨111636036689300668765124849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74424024459533779176749899 111636036689300668765124849)
    ·
      refine ⟨83727027516975501573843637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111636036689300668765124849 83727027516975501573843637)
      ·
        refine ⟨7849408829716453272547841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83727027516975501573843637 7849408829716453272547841)
        ·
          refine ⟨5887056622287339954410881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7849408829716453272547841 5887056622287339954410881)
          ·
            refine ⟨4415292466715504965808161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5887056622287339954410881 4415292466715504965808161)
            ·
              refine ⟨3311469350036628724356121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415292466715504965808161 3311469350036628724356121)
              ·
                refine ⟨2483602012527471543267091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311469350036628724356121 2483602012527471543267091)
                ·
                  refine ⟨3725403018791207314900637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483602012527471543267091 3725403018791207314900637)
                  ·
                    refine ⟨1397026132046702743087739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725403018791207314900637 1397026132046702743087739)
                    ·
                      rfl

theorem cell22_4081048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_4081048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081048 prefixEnd_4081048 := by exact prefixLift 4081048
  have htrace : WordTrace (prefixWord ++ tailWord_4081048) baseStart_4081048 baseEnd_4081048 := by
    simpa [prefixWord, tailWord_4081048, baseEnd_4081048] using wordTrace_append hprefix tailTrace_4081048
  have hstable : (prefixWord ++ tailWord_4081048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081048).length < 2 ^ (prefixWord ++ tailWord_4081048).sum := by decide
  have hdescent : baseEnd_4081048 < baseStart_4081048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081085 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_4081085 : Nat := 118140960795 + 4081085 * 2 ^ 59
def prefixEnd_4081085 : Nat := 4983230072969 + 3 ^ 40 * 4081085 * 2
def baseEnd_4081085 : Nat := 1397038797902846979912625

theorem tailTrace_4081085 : CollatzResearch.WordTrace tailWord_4081085 prefixEnd_4081085 1397038797902846979912625 := by
  unfold tailWord_4081085
  simp only [CollatzResearch.WordTrace]
  refine ⟨148849398419933513672596709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99232932279955675781731139 148849398419933513672596709)
  ·
    refine ⟨27909262203737533813611883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148849398419933513672596709 27909262203737533813611883)
    ·
      refine ⟨41863893305606300720417825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909262203737533813611883 41863893305606300720417825)
      ·
        refine ⟨31397919979204725540313369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41863893305606300720417825 31397919979204725540313369)
        ·
          refine ⟨23548439984403544155235027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31397919979204725540313369 23548439984403544155235027)
          ·
            refine ⟨35322659976605316232852541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23548439984403544155235027 35322659976605316232852541)
            ·
              refine ⟨13245997491226993587319703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35322659976605316232852541 13245997491226993587319703)
              ·
                refine ⟨19868996236840490380979555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13245997491226993587319703 19868996236840490380979555)
                ·
                  refine ⟨29803494355260735571469333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19868996236840490380979555 29803494355260735571469333)
                  ·
                    refine ⟨1397038797902846979912625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29803494355260735571469333 1397038797902846979912625)
                    ·
                      rfl

theorem cell22_4081085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_4081085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081085 prefixEnd_4081085 := by exact prefixLift 4081085
  have htrace : WordTrace (prefixWord ++ tailWord_4081085) baseStart_4081085 baseEnd_4081085 := by
    simpa [prefixWord, tailWord_4081085, baseEnd_4081085] using wordTrace_append hprefix tailTrace_4081085
  have hstable : (prefixWord ++ tailWord_4081085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081085).length < 2 ^ (prefixWord ++ tailWord_4081085).sum := by decide
  have hdescent : baseEnd_4081085 < baseStart_4081085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081100 : List Nat := [2, 2, 1, 4, 2, 2, 9]
def baseStart_4081100 : Nat := 118140960795 + 4081100 * 2 ^ 59
def prefixEnd_4081100 : Nat := 4983230072969 + 3 ^ 40 * 4081100 * 2
def baseEnd_4081100 : Nat := 51742367878125627436577

theorem tailTrace_4081100 : CollatzResearch.WordTrace tailWord_4081100 prefixEnd_4081100 51742367878125627436577 := by
  unfold tailWord_4081100
  simp only [CollatzResearch.WordTrace]
  refine ⟨74424972757439585617196377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99233297009919447489595169 74424972757439585617196377)
  ·
    refine ⟨55818729568079689212897283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74424972757439585617196377 55818729568079689212897283)
    ·
      refine ⟨83728094352119533819345925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55818729568079689212897283 83728094352119533819345925)
      ·
        refine ⟨15699017691022412591127361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83728094352119533819345925 15699017691022412591127361)
        ·
          refine ⟨11774263268266809443345521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15699017691022412591127361 11774263268266809443345521)
          ·
            refine ⟨8830697451200107082509141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11774263268266809443345521 8830697451200107082509141)
            ·
              refine ⟨51742367878125627436577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8830697451200107082509141 51742367878125627436577)
              ·
                rfl

theorem cell22_4081100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 9].length) (baseStart_4081100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081100 prefixEnd_4081100 := by exact prefixLift 4081100
  have htrace : WordTrace (prefixWord ++ tailWord_4081100) baseStart_4081100 baseEnd_4081100 := by
    simpa [prefixWord, tailWord_4081100, baseEnd_4081100] using wordTrace_append hprefix tailTrace_4081100
  have hstable : (prefixWord ++ tailWord_4081100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081100).length < 2 ^ (prefixWord ++ tailWord_4081100).sum := by decide
  have hdescent : baseEnd_4081100 < baseStart_4081100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081160 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_4081160 : Nat := 118140960795 + 4081160 * 2 ^ 59
def prefixEnd_4081160 : Nat := 4983230072969 + 3 ^ 40 * 4081160 * 2
def baseEnd_4081160 : Nat := 1397064471935571784287395

theorem tailTrace_4081160 : CollatzResearch.WordTrace tailWord_4081160 prefixEnd_4081160 1397064471935571784287395 := by
  unfold tailWord_4081160
  simp only [CollatzResearch.WordTrace]
  refine ⟨74426066947330900740788467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99234755929774534321051289 74426066947330900740788467)
  ·
    refine ⟨111639100420996351111182701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74426066947330900740788467 111639100420996351111182701)
    ·
      refine ⟨41864662657873631666693513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111639100420996351111182701 41864662657873631666693513)
      ·
        refine ⟨31398496993405223750020135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41864662657873631666693513 31398496993405223750020135)
        ·
          refine ⟨47097745490107835625030203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31398496993405223750020135 47097745490107835625030203)
          ·
            refine ⟨70646618235161753437545305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47097745490107835625030203 70646618235161753437545305)
            ·
              refine ⟨52984963676371315078158979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70646618235161753437545305 52984963676371315078158979)
              ·
                refine ⟨79477445514556972617238469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52984963676371315078158979 79477445514556972617238469)
                ·
                  refine ⟨14902021033979432365732213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79477445514556972617238469 14902021033979432365732213)
                  ·
                    refine ⟨1397064471935571784287395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14902021033979432365732213 1397064471935571784287395)
                    ·
                      rfl

theorem cell22_4081160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_4081160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081160 prefixEnd_4081160 := by exact prefixLift 4081160
  have htrace : WordTrace (prefixWord ++ tailWord_4081160) baseStart_4081160 baseEnd_4081160 := by
    simpa [prefixWord, tailWord_4081160, baseEnd_4081160] using wordTrace_append hprefix tailTrace_4081160
  have hstable : (prefixWord ++ tailWord_4081160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081160).length < 2 ^ (prefixWord ++ tailWord_4081160).sum := by decide
  have hdescent : baseEnd_4081160 < baseStart_4081160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081166 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_4081166 : Nat := 118140960795 + 4081166 * 2 ^ 59
def prefixEnd_4081166 : Nat := 4983230072969 + 3 ^ 40 * 4081166 * 2
def baseEnd_4081166 : Nat := 1397066525858189768637377

theorem tailTrace_4081166 : CollatzResearch.WordTrace tailWord_4081166 prefixEnd_4081166 1397066525858189768637377 := by
  unfold tailWord_4081166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606544091580008063286919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99234901821760043004196901 18606544091580008063286919)
  ·
    refine ⟨27909816137370012094930379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18606544091580008063286919 27909816137370012094930379)
    ·
      refine ⟨41864724206055018142395569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909816137370012094930379 41864724206055018142395569)
      ·
        refine ⟨31398543154541263606796677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41864724206055018142395569 31398543154541263606796677)
        ·
          refine ⟨5887226841476486926274377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31398543154541263606796677 5887226841476486926274377)
          ·
            refine ⟨4415420131107365194705783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5887226841476486926274377 4415420131107365194705783)
            ·
              refine ⟨6623130196661047792058675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415420131107365194705783 6623130196661047792058675)
              ·
                refine ⟨9934695294991571688088013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623130196661047792058675 9934695294991571688088013)
                ·
                  refine ⟨3725510735621839383033005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9934695294991571688088013 3725510735621839383033005)
                  ·
                    refine ⟨1397066525858189768637377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725510735621839383033005 1397066525858189768637377)
                    ·
                      rfl

theorem cell22_4081166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_4081166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081166 prefixEnd_4081166 := by exact prefixLift 4081166
  have htrace : WordTrace (prefixWord ++ tailWord_4081166) baseStart_4081166 baseEnd_4081166 := by
    simpa [prefixWord, tailWord_4081166, baseEnd_4081166] using wordTrace_append hprefix tailTrace_4081166
  have hstable : (prefixWord ++ tailWord_4081166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081166).length < 2 ^ (prefixWord ++ tailWord_4081166).sum := by decide
  have hdescent : baseEnd_4081166 < baseStart_4081166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081239 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 2, 3]
def baseStart_4081239 : Nat := 118140960795 + 4081239 * 2 ^ 59
def prefixEnd_4081239 : Nat := 4983230072969 + 3 ^ 40 * 4081239 * 2
def baseEnd_4081239 : Nat := 1397091515250041911562153

theorem tailTrace_4081239 : CollatzResearch.WordTrace tailWord_4081239 prefixEnd_4081239 1397091515250041911562153 := by
  unfold tailWord_4081239
  simp only [CollatzResearch.WordTrace]
  refine ⟨148855015261375597973702771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99236676840917065315801847 148855015261375597973702771)
  ·
    refine ⟨223282522892063396960554157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148855015261375597973702771 223282522892063396960554157)
    ·
      refine ⟨83730946084523773860207809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223282522892063396960554157 83730946084523773860207809)
      ·
        refine ⟨62798209563392830395155857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83730946084523773860207809 62798209563392830395155857)
        ·
          refine ⟨47098657172544622796366893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62798209563392830395155857 47098657172544622796366893)
          ·
            refine ⟨17661996439704233548637585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47098657172544622796366893 17661996439704233548637585)
            ·
              refine ⟨13246497329778175161478189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17661996439704233548637585 13246497329778175161478189)
              ·
                refine ⟨4967436498666815685554321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13246497329778175161478189 4967436498666815685554321)
                ·
                  refine ⟨3725577374000111764165741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967436498666815685554321 3725577374000111764165741)
                  ·
                    refine ⟨1397091515250041911562153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725577374000111764165741 1397091515250041911562153)
                    ·
                      rfl

theorem cell22_4081239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_4081239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081239 prefixEnd_4081239 := by exact prefixLift 4081239
  have htrace : WordTrace (prefixWord ++ tailWord_4081239) baseStart_4081239 baseEnd_4081239 := by
    simpa [prefixWord, tailWord_4081239, baseEnd_4081239] using wordTrace_append hprefix tailTrace_4081239
  have hstable : (prefixWord ++ tailWord_4081239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081239).length < 2 ^ (prefixWord ++ tailWord_4081239).sum := by decide
  have hdescent : baseEnd_4081239 < baseStart_4081239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081361 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_4081361 : Nat := 118140960795 + 4081361 * 2 ^ 59
def prefixEnd_4081361 : Nat := 4983230072969 + 3 ^ 40 * 4081361 * 2
def baseEnd_4081361 : Nat := 1397133278343274260011779

theorem tailTrace_4081361 : CollatzResearch.WordTrace tailWord_4081361 prefixEnd_4081361 1397133278343274260011779 := by
  unfold tailWord_4081361
  simp only [CollatzResearch.WordTrace]
  refine ⟨148859464966933612809643937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99239643311289075206429291 148859464966933612809643937)
  ·
    refine ⟨111644598725200209607232953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148859464966933612809643937 111644598725200209607232953)
    ·
      refine ⟨83733449043900157205424715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111644598725200209607232953 83733449043900157205424715)
      ·
        refine ⟨125600173565850235808137073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83733449043900157205424715 125600173565850235808137073)
        ·
          refine ⟨94200130174387676856102805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125600173565850235808137073 94200130174387676856102805)
          ·
            refine ⟨4415631101924422352629819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94200130174387676856102805 4415631101924422352629819)
            ·
              refine ⟨6623446652886633528944729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415631101924422352629819 6623446652886633528944729)
              ·
                refine ⟨4967584989664975146708547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623446652886633528944729 4967584989664975146708547)
                ·
                  refine ⟨7451377484497462720062821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967584989664975146708547 7451377484497462720062821)
                  ·
                    refine ⟨1397133278343274260011779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451377484497462720062821 1397133278343274260011779)
                    ·
                      rfl

theorem cell22_4081361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_4081361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081361 prefixEnd_4081361 := by exact prefixLift 4081361
  have htrace : WordTrace (prefixWord ++ tailWord_4081361) baseStart_4081361 baseEnd_4081361 := by
    simpa [prefixWord, tailWord_4081361, baseEnd_4081361] using wordTrace_append hprefix tailTrace_4081361
  have hstable : (prefixWord ++ tailWord_4081361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081361).length < 2 ^ (prefixWord ++ tailWord_4081361).sum := by decide
  have hdescent : baseEnd_4081361 < baseStart_4081361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081391 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 2, 3]
def baseStart_4081391 : Nat := 118140960795 + 4081391 * 2 ^ 59
def prefixEnd_4081391 : Nat := 4983230072969 + 3 ^ 40 * 4081391 * 2
def baseEnd_4081391 : Nat := 1397143547956364181761687

theorem tailTrace_4081391 : CollatzResearch.WordTrace tailWord_4081391 prefixEnd_4081391 1397143547956364181761687 := by
  unfold tailWord_4081391
  simp only [CollatzResearch.WordTrace]
  refine ⟨148860559156824927933236027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99240372771216618622157351 148860559156824927933236027)
  ·
    refine ⟨223290838735237391899854041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148860559156824927933236027 223290838735237391899854041)
    ·
      refine ⟨167468129051428043924890531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223290838735237391899854041 167468129051428043924890531)
      ·
        refine ⟨251202193577142065887335797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167468129051428043924890531 251202193577142065887335797)
        ·
          refine ⟨23550205647857068676937731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251202193577142065887335797 23550205647857068676937731)
          ·
            refine ⟨35325308471785603015406597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23550205647857068676937731 35325308471785603015406597)
            ·
              refine ⟨6623495338459800565388737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35325308471785603015406597 6623495338459800565388737)
              ·
                refine ⟨4967621503844850424041553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623495338459800565388737 4967621503844850424041553)
                ·
                  refine ⟨3725716127883637818031165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967621503844850424041553 3725716127883637818031165)
                  ·
                    refine ⟨1397143547956364181761687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725716127883637818031165 1397143547956364181761687)
                    ·
                      rfl

theorem cell22_4081391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_4081391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081391 prefixEnd_4081391 := by exact prefixLift 4081391
  have htrace : WordTrace (prefixWord ++ tailWord_4081391) baseStart_4081391 baseEnd_4081391 := by
    simpa [prefixWord, tailWord_4081391, baseEnd_4081391] using wordTrace_append hprefix tailTrace_4081391
  have hstable : (prefixWord ++ tailWord_4081391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081391).length < 2 ^ (prefixWord ++ tailWord_4081391).sum := by decide
  have hdescent : baseEnd_4081391 < baseStart_4081391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081393 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 4]
def baseStart_4081393 : Nat := 118140960795 + 4081393 * 2 ^ 59
def prefixEnd_4081393 : Nat := 4983230072969 + 3 ^ 40 * 4081393 * 2
def baseEnd_4081393 : Nat := 465714744199078947737227

theorem tailTrace_4081393 : CollatzResearch.WordTrace tailWord_4081393 prefixEnd_4081393 465714744199078947737227 := by
  unfold tailWord_4081393
  simp only [CollatzResearch.WordTrace]
  refine ⟨148860632102817682274808833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99240421401878454849872555 148860632102817682274808833)
  ·
    refine ⟨111645474077113261706106625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148860632102817682274808833 111645474077113261706106625)
    ·
      refine ⟨83734105557834946279579969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111645474077113261706106625 83734105557834946279579969)
      ·
        refine ⟨62800579168376209709684977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83734105557834946279579969 62800579168376209709684977)
        ·
          refine ⟨47100434376282157282263733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62800579168376209709684977 47100434376282157282263733)
          ·
            refine ⟨4415665722776452245212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47100434376282157282263733 4415665722776452245212225)
            ·
              refine ⟨3311749292082339183909169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415665722776452245212225 3311749292082339183909169)
              ·
                refine ⟨2483811969061754387931877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311749292082339183909169 2483811969061754387931877)
                ·
                  refine ⟨465714744199078947737227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483811969061754387931877 465714744199078947737227)
                  ·
                    rfl

theorem cell22_4081393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_4081393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081393 prefixEnd_4081393 := by exact prefixLift 4081393
  have htrace : WordTrace (prefixWord ++ tailWord_4081393) baseStart_4081393 baseEnd_4081393 := by
    simpa [prefixWord, tailWord_4081393, baseEnd_4081393] using wordTrace_append hprefix tailTrace_4081393
  have hstable : (prefixWord ++ tailWord_4081393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081393).length < 2 ^ (prefixWord ++ tailWord_4081393).sum := by decide
  have hdescent : baseEnd_4081393 < baseStart_4081393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081402 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_4081402 : Nat := 118140960795 + 4081402 * 2 ^ 59
def prefixEnd_4081402 : Nat := 4983230072969 + 3 ^ 40 * 4081402 * 2
def baseEnd_4081402 : Nat := 1397147313481163819736653

theorem tailTrace_4081402 : CollatzResearch.WordTrace tailWord_4081402 prefixEnd_4081402 1397147313481163819736653 := by
  unfold tailWord_4081402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37215240089946269202971615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99240640239856717874590973 37215240089946269202971615)
  ·
    refine ⟨55822860134919403804457423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37215240089946269202971615 55822860134919403804457423)
    ·
      refine ⟨83734290202379105706686135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55822860134919403804457423 83734290202379105706686135)
      ·
        refine ⟨125601435303568658560029203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83734290202379105706686135 125601435303568658560029203)
        ·
          refine ⟨188402152955352987840043805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125601435303568658560029203 188402152955352987840043805)
          ·
            refine ⟨70650807358257370440016427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188402152955352987840043805 70650807358257370440016427)
            ·
              refine ⟨105976211037386055660024641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70650807358257370440016427 105976211037386055660024641)
              ·
                refine ⟨79482158278039541745018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105976211037386055660024641 79482158278039541745018481)
                ·
                  refine ⟨59611618708529656308763861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79482158278039541745018481 59611618708529656308763861)
                  ·
                    refine ⟨1397147313481163819736653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59611618708529656308763861 1397147313481163819736653)
                    ·
                      rfl

theorem cell22_4081402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_4081402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081402 prefixEnd_4081402 := by exact prefixLift 4081402
  have htrace : WordTrace (prefixWord ++ tailWord_4081402) baseStart_4081402 baseEnd_4081402 := by
    simpa [prefixWord, tailWord_4081402, baseEnd_4081402] using wordTrace_append hprefix tailTrace_4081402
  have hstable : (prefixWord ++ tailWord_4081402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081402).length < 2 ^ (prefixWord ++ tailWord_4081402).sum := by decide
  have hdescent : baseEnd_4081402 < baseStart_4081402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081417 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_4081417 : Nat := 118140960795 + 4081417 * 2 ^ 59
def prefixEnd_4081417 : Nat := 4983230072969 + 3 ^ 40 * 4081417 * 2
def baseEnd_4081417 : Nat := 1397152448287708780611607

theorem tailTrace_4081417 : CollatzResearch.WordTrace tailWord_4081417 prefixEnd_4081417 1397152448287708780611607 := by
  unfold tailWord_4081417
  simp only [CollatzResearch.WordTrace]
  refine ⟨148861507454730734373682505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99241004969820489582455003 148861507454730734373682505)
  ·
    refine ⟨111646130591048050780261879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148861507454730734373682505 111646130591048050780261879)
    ·
      refine ⟨167469195886572076170392819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111646130591048050780261879 167469195886572076170392819)
      ·
        refine ⟨251203793829858114255589229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167469195886572076170392819 251203793829858114255589229)
        ·
          refine ⟨94201422686196792845845961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251203793829858114255589229 94201422686196792845845961)
          ·
            refine ⟨70651067014647594634384471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94201422686196792845845961 70651067014647594634384471)
            ·
              refine ⟨105976600521971391951576707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70651067014647594634384471 105976600521971391951576707)
              ·
                refine ⟨158964900782957087927365061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105976600521971391951576707 158964900782957087927365061)
                ·
                  refine ⟨29805918896804453986380949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158964900782957087927365061 29805918896804453986380949)
                  ·
                    refine ⟨1397152448287708780611607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29805918896804453986380949 1397152448287708780611607)
                    ·
                      rfl

theorem cell22_4081417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_4081417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081417 prefixEnd_4081417 := by exact prefixLift 4081417
  have htrace : WordTrace (prefixWord ++ tailWord_4081417) baseStart_4081417 baseEnd_4081417 := by
    simpa [prefixWord, tailWord_4081417, baseEnd_4081417] using wordTrace_append hprefix tailTrace_4081417
  have hstable : (prefixWord ++ tailWord_4081417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081417).length < 2 ^ (prefixWord ++ tailWord_4081417).sum := by decide
  have hdescent : baseEnd_4081417 < baseStart_4081417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081419 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 5, 3]
def baseStart_4081419 : Nat := 118140960795 + 4081419 * 2 ^ 59
def prefixEnd_4081419 : Nat := 4983230072969 + 3 ^ 40 * 4081419 * 2
def baseEnd_4081419 : Nat := 1397153132928581442061601

theorem tailTrace_4081419 : CollatzResearch.WordTrace tailWord_4081419 prefixEnd_4081419 1397153132928581442061601 := by
  unfold tailWord_4081419
  simp only [CollatzResearch.WordTrace]
  refine ⟨148861580400723488715255311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99241053600482325810170207 148861580400723488715255311)
  ·
    refine ⟨223292370601085233072882967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148861580400723488715255311 223292370601085233072882967)
    ·
      refine ⟨334938555901627849609324451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223292370601085233072882967 334938555901627849609324451)
      ·
        refine ⟨502407833852441774413986677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334938555901627849609324451 502407833852441774413986677)
        ·
          refine ⟨47100734423666416351311251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502407833852441774413986677 47100734423666416351311251)
          ·
            refine ⟨70651101635499624526966877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47100734423666416351311251 70651101635499624526966877)
            ·
              refine ⟨26494163113312359197612579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70651101635499624526966877 26494163113312359197612579)
              ·
                refine ⟨39741244669968538796418869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26494163113312359197612579 39741244669968538796418869)
                ·
                  refine ⟨3725741687809550512164269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39741244669968538796418869 3725741687809550512164269)
                  ·
                    refine ⟨1397153132928581442061601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725741687809550512164269 1397153132928581442061601)
                    ·
                      rfl

theorem cell22_4081419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3].length) (baseStart_4081419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081419 prefixEnd_4081419 := by exact prefixLift 4081419
  have htrace : WordTrace (prefixWord ++ tailWord_4081419) baseStart_4081419 baseEnd_4081419 := by
    simpa [prefixWord, tailWord_4081419, baseEnd_4081419] using wordTrace_append hprefix tailTrace_4081419
  have hstable : (prefixWord ++ tailWord_4081419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081419).length < 2 ^ (prefixWord ++ tailWord_4081419).sum := by decide
  have hdescent : baseEnd_4081419 < baseStart_4081419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081438 : List Nat := [4, 3, 2, 2, 1, 1, 9]
def baseStart_4081438 : Nat := 118140960795 + 4081438 * 2 ^ 59
def prefixEnd_4081438 : Nat := 4983230072969 + 3 ^ 40 * 4081438 * 2
def baseEnd_4081438 : Nat := 51746653222847100956909

theorem tailTrace_4081438 : CollatzResearch.WordTrace tailWord_4081438 prefixEnd_4081438 51746653222847100956909 := by
  unfold tailWord_4081438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607784173456831870024621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99241515591769769973464645 18607784173456831870024621)
  ·
    refine ⟨6977919065046311951259233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18607784173456831870024621 6977919065046311951259233)
    ·
      refine ⟨5233439298784733963444425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6977919065046311951259233 5233439298784733963444425)
      ·
        refine ⟨3925079474088550472583319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5233439298784733963444425 3925079474088550472583319)
        ·
          refine ⟨5887619211132825708874979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925079474088550472583319 5887619211132825708874979)
          ·
            refine ⟨8831428816699238563312469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887619211132825708874979 8831428816699238563312469)
            ·
              refine ⟨51746653222847100956909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8831428816699238563312469 51746653222847100956909)
              ·
                rfl

theorem cell22_4081438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 9].length) (baseStart_4081438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081438 prefixEnd_4081438 := by exact prefixLift 4081438
  have htrace : WordTrace (prefixWord ++ tailWord_4081438) baseStart_4081438 baseEnd_4081438 := by
    simpa [prefixWord, tailWord_4081438, baseEnd_4081438] using wordTrace_append hprefix tailTrace_4081438
  have hstable : (prefixWord ++ tailWord_4081438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081438).length < 2 ^ (prefixWord ++ tailWord_4081438).sum := by decide
  have hdescent : baseEnd_4081438 < baseStart_4081438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081464 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_4081464 : Nat := 118140960795 + 4081464 * 2 ^ 59
def prefixEnd_4081464 : Nat := 4983230072969 + 3 ^ 40 * 4081464 * 2
def baseEnd_4081464 : Nat := 1397168537348216324686463

theorem tailTrace_4081464 : CollatzResearch.WordTrace tailWord_4081464 prefixEnd_4081464 1397168537348216324686463 := by
  unfold tailWord_4081464
  simp only [CollatzResearch.WordTrace]
  refine ⟨74431610842780230700321723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99242147790373640933762297 74431610842780230700321723)
  ·
    refine ⟨111647416264170346050482585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74431610842780230700321723 111647416264170346050482585)
    ·
      refine ⟨83735562198127759537861939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111647416264170346050482585 83735562198127759537861939)
      ·
        refine ⟨125603343297191639306792909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83735562198127759537861939 125603343297191639306792909)
        ·
          refine ⟨47101253736446864740047341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125603343297191639306792909 47101253736446864740047341)
          ·
            refine ⟨17662970151167574277517753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47101253736446864740047341 17662970151167574277517753)
            ·
              refine ⟨13247227613375680708138315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17662970151167574277517753 13247227613375680708138315)
              ·
                refine ⟨19870841420063521062207473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13247227613375680708138315 19870841420063521062207473)
                ·
                  refine ⟨14903131065047640796655605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19870841420063521062207473 14903131065047640796655605)
                  ·
                    refine ⟨1397168537348216324686463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14903131065047640796655605 1397168537348216324686463)
                    ·
                      rfl

theorem cell22_4081464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_4081464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081464 prefixEnd_4081464 := by exact prefixLift 4081464
  have htrace : WordTrace (prefixWord ++ tailWord_4081464) baseStart_4081464 baseEnd_4081464 := by
    simpa [prefixWord, tailWord_4081464, baseEnd_4081464] using wordTrace_append hprefix tailTrace_4081464
  have hstable : (prefixWord ++ tailWord_4081464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081464).length < 2 ^ (prefixWord ++ tailWord_4081464).sum := by decide
  have hdescent : baseEnd_4081464 < baseStart_4081464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081479 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_4081479 : Nat := 118140960795 + 4081479 * 2 ^ 59
def prefixEnd_4081479 : Nat := 4983230072969 + 3 ^ 40 * 4081479 * 2
def baseEnd_4081479 : Nat := 1397173672154761285561417

theorem tailTrace_4081479 : CollatzResearch.WordTrace tailWord_4081479 prefixEnd_4081479 1397173672154761285561417 := by
  unfold tailWord_4081479
  simp only [CollatzResearch.WordTrace]
  refine ⟨148863768780506118962439491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99242512520337412641626327 148863768780506118962439491)
  ·
    refine ⟨223295653170759178443659237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148863768780506118962439491 223295653170759178443659237)
    ·
      refine ⟨41867934969517345958186107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223295653170759178443659237 41867934969517345958186107)
      ·
        refine ⟨62801902454276018937279161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41867934969517345958186107 62801902454276018937279161)
        ·
          refine ⟨47101426840707014202959371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62801902454276018937279161 47101426840707014202959371)
          ·
            refine ⟨70652140261060521304439057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47101426840707014202959371 70652140261060521304439057)
            ·
              refine ⟨52989105195795390978329293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70652140261060521304439057 52989105195795390978329293)
              ·
                refine ⟨19870914448423271616873485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52989105195795390978329293 19870914448423271616873485)
                ·
                  refine ⟨7451592918158726856327557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19870914448423271616873485 7451592918158726856327557)
                  ·
                    refine ⟨1397173672154761285561417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451592918158726856327557 1397173672154761285561417)
                    ·
                      rfl

theorem cell22_4081479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_4081479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081479 prefixEnd_4081479 := by exact prefixLift 4081479
  have htrace : WordTrace (prefixWord ++ tailWord_4081479) baseStart_4081479 baseEnd_4081479 := by
    simpa [prefixWord, tailWord_4081479, baseEnd_4081479] using wordTrace_append hprefix tailTrace_4081479
  have hstable : (prefixWord ++ tailWord_4081479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081479).length < 2 ^ (prefixWord ++ tailWord_4081479).sum := by decide
  have hdescent : baseEnd_4081479 < baseStart_4081479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081539 : List Nat := [1, 1, 1, 3, 4, 2, 2, 8]
def baseStart_4081539 : Nat := 118140960795 + 4081539 * 2 ^ 59
def prefixEnd_4081539 : Nat := 4983230072969 + 3 ^ 40 * 4081539 * 2
def baseEnd_4081539 : Nat := 155243801264549014340137

theorem tailTrace_4081539 : CollatzResearch.WordTrace tailWord_4081539 prefixEnd_4081539 155243801264549014340137 := by
  unfold tailWord_4081539
  simp only [CollatzResearch.WordTrace]
  refine ⟨148865957160288749209623671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99243971440192499473082447 148865957160288749209623671)
  ·
    refine ⟨223298935740433123814435507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148865957160288749209623671 223298935740433123814435507)
    ·
      refine ⟨334948403610649685721653261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223298935740433123814435507 334948403610649685721653261)
      ·
        refine ⟨125605651353993632145619973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334948403610649685721653261 125605651353993632145619973)
        ·
          refine ⟨23551059628873806027303745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125605651353993632145619973 23551059628873806027303745)
          ·
            refine ⟨17663294721655354520477809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23551059628873806027303745 17663294721655354520477809)
            ·
              refine ⟨13247471041241515890358357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17663294721655354520477809 13247471041241515890358357)
              ·
                refine ⟨155243801264549014340137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13247471041241515890358357 155243801264549014340137)
                ·
                  rfl

theorem cell22_4081539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 8].length) (baseStart_4081539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081539 prefixEnd_4081539 := by exact prefixLift 4081539
  have htrace : WordTrace (prefixWord ++ tailWord_4081539) baseStart_4081539 baseEnd_4081539 := by
    simpa [prefixWord, tailWord_4081539, baseEnd_4081539] using wordTrace_append hprefix tailTrace_4081539
  have hstable : (prefixWord ++ tailWord_4081539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081539).length < 2 ^ (prefixWord ++ tailWord_4081539).sum := by decide
  have hdescent : baseEnd_4081539 < baseStart_4081539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081541 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_4081541 : Nat := 118140960795 + 4081541 * 2 ^ 59
def prefixEnd_4081541 : Nat := 4983230072969 + 3 ^ 40 * 4081541 * 2
def baseEnd_4081541 : Nat := 1397194896021813790511227

theorem tailTrace_4081541 : CollatzResearch.WordTrace tailWord_4081541 prefixEnd_4081541 1397194896021813790511227 := by
  unfold tailWord_4081541
  simp only [CollatzResearch.WordTrace]
  refine ⟨148866030106281503551196477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99244020070854335700797651 148866030106281503551196477)
  ·
    refine ⟨55824761289855563831698679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148866030106281503551196477 55824761289855563831698679)
    ·
      refine ⟨83737141934783345747548019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55824761289855563831698679 83737141934783345747548019)
      ·
        refine ⟨125605712902175018621322029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83737141934783345747548019 125605712902175018621322029)
        ·
          refine ⟨47102142338315631982995761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125605712902175018621322029 47102142338315631982995761)
          ·
            refine ⟨35326606753736723987246821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47102142338315631982995761 35326606753736723987246821)
            ·
              refine ⟨6623738766325635747608779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35326606753736723987246821 6623738766325635747608779)
              ·
                refine ⟨9935608149488453621413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623738766325635747608779 9935608149488453621413169)
                ·
                  refine ⟨7451706112116340216059877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9935608149488453621413169 7451706112116340216059877)
                  ·
                    refine ⟨1397194896021813790511227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451706112116340216059877 1397194896021813790511227)
                    ·
                      rfl

theorem cell22_4081541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_4081541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081541 prefixEnd_4081541 := by exact prefixLift 4081541
  have htrace : WordTrace (prefixWord ++ tailWord_4081541) baseStart_4081541 baseEnd_4081541 := by
    simpa [prefixWord, tailWord_4081541, baseEnd_4081541] using wordTrace_append hprefix tailTrace_4081541
  have hstable : (prefixWord ++ tailWord_4081541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081541).length < 2 ^ (prefixWord ++ tailWord_4081541).sum := by decide
  have hdescent : baseEnd_4081541 < baseStart_4081541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081571 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 3, 3]
def baseStart_4081571 : Nat := 118140960795 + 4081571 * 2 ^ 59
def prefixEnd_4081571 : Nat := 4983230072969 + 3 ^ 40 * 4081571 * 2
def baseEnd_4081571 : Nat := 1397205165634903712261135

theorem tailTrace_4081571 : CollatzResearch.WordTrace tailWord_4081571 prefixEnd_4081571 1397205165634903712261135 := by
  unfold tailWord_4081571
  simp only [CollatzResearch.WordTrace]
  refine ⟨148867124296172818674788567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99244749530781879116525711 148867124296172818674788567)
  ·
    refine ⟨223300686444259228012182851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148867124296172818674788567 223300686444259228012182851)
    ·
      refine ⟨334951029666388842018274277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223300686444259228012182851 334951029666388842018274277)
      ·
        refine ⟨62803318062447907878426427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334951029666388842018274277 62803318062447907878426427)
        ·
          refine ⟨94204977093671861817639641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62803318062447907878426427 94204977093671861817639641)
          ·
            refine ⟨70653732820253896363229731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94204977093671861817639641 70653732820253896363229731)
            ·
              refine ⟨105980599230380844544844597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70653732820253896363229731 105980599230380844544844597)
              ·
                refine ⟨9935681177848204176079181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105980599230380844544844597 9935681177848204176079181)
                ·
                  refine ⟨3725880441693076566029693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9935681177848204176079181 3725880441693076566029693)
                  ·
                    refine ⟨1397205165634903712261135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725880441693076566029693 1397205165634903712261135)
                    ·
                      rfl

theorem cell22_4081571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 3].length) (baseStart_4081571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081571 prefixEnd_4081571 := by exact prefixLift 4081571
  have htrace : WordTrace (prefixWord ++ tailWord_4081571) baseStart_4081571 baseEnd_4081571 := by
    simpa [prefixWord, tailWord_4081571, baseEnd_4081571] using wordTrace_append hprefix tailTrace_4081571
  have hstable : (prefixWord ++ tailWord_4081571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081571).length < 2 ^ (prefixWord ++ tailWord_4081571).sum := by decide
  have hdescent : baseEnd_4081571 < baseStart_4081571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081599 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_4081599 : Nat := 118140960795 + 4081599 * 2 ^ 59
def prefixEnd_4081599 : Nat := 4983230072969 + 3 ^ 40 * 4081599 * 2
def baseEnd_4081599 : Nat := 1397214750607120972561049

theorem tailTrace_4081599 : CollatzResearch.WordTrace tailWord_4081599 prefixEnd_4081599 1397214750607120972561049 := by
  unfold tailWord_4081599
  simp only [CollatzResearch.WordTrace]
  refine ⟨148868145540071379456807851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99245430360047586304538567 148868145540071379456807851)
  ·
    refine ⟨223302218310107069185211777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148868145540071379456807851 223302218310107069185211777)
    ·
      refine ⟨167476663732580301888908833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223302218310107069185211777 167476663732580301888908833)
      ·
        refine ⟨125607497799435226416681625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167476663732580301888908833 125607497799435226416681625)
        ·
          refine ⟨94205623349576419812511219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125607497799435226416681625 94205623349576419812511219)
          ·
            refine ⟨141308435024364629718766829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94205623349576419812511219 141308435024364629718766829)
            ·
              refine ⟨52990663134136736144537561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141308435024364629718766829 52990663134136736144537561)
              ·
                refine ⟨39742997350602552108403171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52990663134136736144537561 39742997350602552108403171)
                ·
                  refine ⟨59614496025903828162604757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39742997350602552108403171 59614496025903828162604757)
                  ·
                    refine ⟨1397214750607120972561049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59614496025903828162604757 1397214750607120972561049)
                    ·
                      rfl

theorem cell22_4081599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_4081599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081599 prefixEnd_4081599 := by exact prefixLift 4081599
  have htrace : WordTrace (prefixWord ++ tailWord_4081599) baseStart_4081599 baseEnd_4081599 := by
    simpa [prefixWord, tailWord_4081599, baseEnd_4081599] using wordTrace_append hprefix tailTrace_4081599
  have hstable : (prefixWord ++ tailWord_4081599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081599).length < 2 ^ (prefixWord ++ tailWord_4081599).sum := by decide
  have hdescent : baseEnd_4081599 < baseStart_4081599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081618 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_4081618 : Nat := 118140960795 + 4081618 * 2 ^ 59
def prefixEnd_4081618 : Nat := 4983230072969 + 3 ^ 40 * 4081618 * 2
def baseEnd_4081618 : Nat := 465740418231803752111997

theorem tailTrace_4081618 : CollatzResearch.WordTrace tailWord_4081618 prefixEnd_4081618 465740418231803752111997 := by
  unfold tailWord_4081618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37217209631750636425437377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99245892351335030467833005 37217209631750636425437377)
  ·
    refine ⟨27912907223812977319078033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37217209631750636425437377 27912907223812977319078033)
    ·
      refine ⟨20934680417859732989308525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27912907223812977319078033 20934680417859732989308525)
      ·
        refine ⟨7850505156697399870990697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20934680417859732989308525 7850505156697399870990697)
        ·
          refine ⟨5887878867523049903243023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7850505156697399870990697 5887878867523049903243023)
          ·
            refine ⟨8831818301284574854864535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887878867523049903243023 8831818301284574854864535)
            ·
              refine ⟨13247727451926862282296803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8831818301284574854864535 13247727451926862282296803)
              ·
                refine ⟨19871591177890293423445205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13247727451926862282296803 19871591177890293423445205)
                ·
                  refine ⟨465740418231803752111997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19871591177890293423445205 465740418231803752111997)
                  ·
                    rfl

theorem cell22_4081618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_4081618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081618 prefixEnd_4081618 := by exact prefixLift 4081618
  have htrace : WordTrace (prefixWord ++ tailWord_4081618) baseStart_4081618 baseEnd_4081618 := by
    simpa [prefixWord, tailWord_4081618, baseEnd_4081618] using wordTrace_append hprefix tailTrace_4081618
  have hstable : (prefixWord ++ tailWord_4081618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081618).length < 2 ^ (prefixWord ++ tailWord_4081618).sum := by decide
  have hdescent : baseEnd_4081618 < baseStart_4081618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081622 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4081622 : Nat := 118140960795 + 4081622 * 2 ^ 59
def prefixEnd_4081622 : Nat := 4983230072969 + 3 ^ 40 * 4081622 * 2
def baseEnd_4081622 : Nat := 1397222623977156579235979

theorem tailTrace_4081622 : CollatzResearch.WordTrace tailWord_4081622 prefixEnd_4081622 1397222623977156579235979 := by
  unfold tailWord_4081622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304311526186753399055945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99245989612658702923263413 9304311526186753399055945)
  ·
    refine ⟨6978233644640065049291959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9304311526186753399055945 6978233644640065049291959)
    ·
      refine ⟨10467350466960097573937939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978233644640065049291959 10467350466960097573937939)
      ·
        refine ⟨15701025700440146360906909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467350466960097573937939 15701025700440146360906909)
        ·
          refine ⟨5887884637665054885340091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15701025700440146360906909 5887884637665054885340091)
          ·
            refine ⟨8831826956497582328010137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887884637665054885340091 8831826956497582328010137)
            ·
              refine ⟨6623870217373186746007603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831826956497582328010137 6623870217373186746007603)
              ·
                refine ⟨9935805326059780119011405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623870217373186746007603 9935805326059780119011405)
                ·
                  refine ⟨3725926997272417544629277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9935805326059780119011405 3725926997272417544629277)
                  ·
                    refine ⟨1397222623977156579235979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725926997272417544629277 1397222623977156579235979)
                    ·
                      rfl

theorem cell22_4081622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4081622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081622 prefixEnd_4081622 := by exact prefixLift 4081622
  have htrace : WordTrace (prefixWord ++ tailWord_4081622) baseStart_4081622 baseEnd_4081622 := by
    simpa [prefixWord, tailWord_4081622, baseEnd_4081622] using wordTrace_append hprefix tailTrace_4081622
  have hstable : (prefixWord ++ tailWord_4081622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081622).length < 2 ^ (prefixWord ++ tailWord_4081622).sum := by decide
  have hdescent : baseEnd_4081622 < baseStart_4081622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081661 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_4081661 : Nat := 118140960795 + 4081661 * 2 ^ 59
def prefixEnd_4081661 : Nat := 4983230072969 + 3 ^ 40 * 4081661 * 2
def baseEnd_4081661 : Nat := 1397235974474173477510859

theorem tailTrace_4081661 : CollatzResearch.WordTrace tailWord_4081661 prefixEnd_4081661 1397235974474173477510859 := by
  unfold tailWord_4081661
  simp only [CollatzResearch.WordTrace]
  refine ⟨148870406865846764045564837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99246937910564509363709891 148870406865846764045564837)
  ·
    refine ⟨27913201287346268258543407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148870406865846764045564837 27913201287346268258543407)
    ·
      refine ⟨41869801931019402387815111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27913201287346268258543407 41869801931019402387815111)
      ·
        refine ⟨62804702896529103581722667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41869801931019402387815111 62804702896529103581722667)
        ·
          refine ⟨94207054344793655372584001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62804702896529103581722667 94207054344793655372584001)
          ·
            refine ⟨70655290758595241529438001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94207054344793655372584001 70655290758595241529438001)
            ·
              refine ⟨52991468068946431147078501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70655290758595241529438001 52991468068946431147078501)
              ·
                refine ⟨9935900262927455840077219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52991468068946431147078501 9935900262927455840077219)
                ·
                  refine ⟨14903850394391183760115829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9935900262927455840077219 14903850394391183760115829)
                  ·
                    refine ⟨1397235974474173477510859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14903850394391183760115829 1397235974474173477510859)
                    ·
                      rfl

theorem cell22_4081661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_4081661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4081661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4081661 prefixEnd_4081661 := by exact prefixLift 4081661
  have htrace : WordTrace (prefixWord ++ tailWord_4081661) baseStart_4081661 baseEnd_4081661 := by
    simpa [prefixWord, tailWord_4081661, baseEnd_4081661] using wordTrace_append hprefix tailTrace_4081661
  have hstable : (prefixWord ++ tailWord_4081661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081661).length < 2 ^ (prefixWord ++ tailWord_4081661).sum := by decide
  have hdescent : baseEnd_4081661 < baseStart_4081661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
