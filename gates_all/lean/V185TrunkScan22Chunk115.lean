import V185TrunkScan22Chunk114

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1030294 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1030294 : Nat := 118140960795 + 1030294 * 2 ^ 59
def prefixEnd_1030294 : Nat := 4983230072969 + 3 ^ 40 * 1030294 * 2
def baseEnd_1030294 : Nat := 352690691628998135791181

theorem tailTrace_1030294 : CollatzResearch.WordTrace tailWord_1030294 prefixEnd_1030294 352690691628998135791181 := by
  unfold tailWord_1030294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348619333089267065712621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25051939552952182034267957 2348619333089267065712621)
  ·
    refine ⟨880732249908475149642233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2348619333089267065712621 880732249908475149642233)
    ·
      refine ⟨660549187431356362231675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 880732249908475149642233 660549187431356362231675)
      ·
        refine ⟨990823781147034543347513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660549187431356362231675 990823781147034543347513)
        ·
          refine ⟨743117835860275907510635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990823781147034543347513 743117835860275907510635)
          ·
            refine ⟨1114676753790413861265953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743117835860275907510635 1114676753790413861265953)
            ·
              refine ⟨836007565342810395949465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114676753790413861265953 836007565342810395949465)
              ·
                refine ⟨627005674007107796962099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836007565342810395949465 627005674007107796962099)
                ·
                  refine ⟨940508511010661695443149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627005674007107796962099 940508511010661695443149)
                  ·
                    refine ⟨352690691628998135791181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940508511010661695443149 352690691628998135791181)
                    ·
                      rfl

theorem cell22_1030294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1030294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030294 prefixEnd_1030294 := by exact prefixLift 1030294
  have htrace : WordTrace (prefixWord ++ tailWord_1030294) baseStart_1030294 baseEnd_1030294 := by
    simpa [prefixWord, tailWord_1030294, baseEnd_1030294] using wordTrace_append hprefix tailTrace_1030294
  have hstable : (prefixWord ++ tailWord_1030294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030294).length < 2 ^ (prefixWord ++ tailWord_1030294).sum := by decide
  have hdescent : baseEnd_1030294 < baseStart_1030294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030400 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_1030400 : Nat := 118140960795 + 1030400 * 2 ^ 59
def prefixEnd_1030400 : Nat := 4983230072969 + 3 ^ 40 * 1030400 * 2
def baseEnd_1030400 : Nat := 352726977595249192640855

theorem tailTrace_1030400 : CollatzResearch.WordTrace tailWord_1030400 prefixEnd_1030400 352726977595249192640855 := by
  unfold tailWord_1030400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18790887733522126577380327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25054516978029502103173769 18790887733522126577380327)
  ·
    refine ⟨28186331600283189866070491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18790887733522126577380327 28186331600283189866070491)
    ·
      refine ⟨42279497400424784799105737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28186331600283189866070491 42279497400424784799105737)
      ·
        refine ⟨31709623050318588599329303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42279497400424784799105737 31709623050318588599329303)
        ·
          refine ⟨47564434575477882898993955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31709623050318588599329303 47564434575477882898993955)
          ·
            refine ⟨71346651863216824348490933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47564434575477882898993955 71346651863216824348490933)
            ·
              refine ⟨6688748612176577282671025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71346651863216824348490933 6688748612176577282671025)
              ·
                refine ⟨5016561459132432962003269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6688748612176577282671025 5016561459132432962003269)
                ·
                  refine ⟨940605273587331180375613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5016561459132432962003269 940605273587331180375613)
                  ·
                    refine ⟨352726977595249192640855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940605273587331180375613 352726977595249192640855)
                    ·
                      rfl

theorem cell22_1030400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_1030400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030400 prefixEnd_1030400 := by exact prefixLift 1030400
  have htrace : WordTrace (prefixWord ++ tailWord_1030400) baseStart_1030400 baseEnd_1030400 := by
    simpa [prefixWord, tailWord_1030400, baseEnd_1030400] using wordTrace_append hprefix tailTrace_1030400
  have hstable : (prefixWord ++ tailWord_1030400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030400).length < 2 ^ (prefixWord ++ tailWord_1030400).sum := by decide
  have hdescent : baseEnd_1030400 < baseStart_1030400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030434 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1030434 : Nat := 118140960795 + 1030434 * 2 ^ 59
def prefixEnd_1030434 : Nat := 4983230072969 + 3 ^ 40 * 1030434 * 2
def baseEnd_1030434 : Nat := 352738616490084437290751

theorem tailTrace_1030434 : CollatzResearch.WordTrace tailWord_1030434 prefixEnd_1030434 352738616490084437290751 := by
  unfold tailWord_1030434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395753887230269240374589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25055343699280717974332237 9395753887230269240374589)
  ·
    refine ⟨3523407707711350965140471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9395753887230269240374589 3523407707711350965140471)
    ·
      refine ⟨5285111561567026447710707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523407707711350965140471 5285111561567026447710707)
      ·
        refine ⟨7927667342350539671566061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285111561567026447710707 7927667342350539671566061)
        ·
          refine ⟨2972875253381452376837273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7927667342350539671566061 2972875253381452376837273)
          ·
            refine ⟨2229656440036089282627955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972875253381452376837273 2229656440036089282627955)
            ·
              refine ⟨3344484660054133923941933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229656440036089282627955 3344484660054133923941933)
              ·
                refine ⟨1254181747520300221478225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3344484660054133923941933 1254181747520300221478225)
                ·
                  refine ⟨940636310640225166108669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1254181747520300221478225 940636310640225166108669)
                  ·
                    refine ⟨352738616490084437290751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940636310640225166108669 352738616490084437290751)
                    ·
                      rfl

theorem cell22_1030434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1030434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030434 prefixEnd_1030434 := by exact prefixLift 1030434
  have htrace : WordTrace (prefixWord ++ tailWord_1030434) baseStart_1030434 baseEnd_1030434 := by
    simpa [prefixWord, tailWord_1030434, baseEnd_1030434] using wordTrace_append hprefix tailTrace_1030434
  have hstable : (prefixWord ++ tailWord_1030434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030434).length < 2 ^ (prefixWord ++ tailWord_1030434).sum := by decide
  have hdescent : baseEnd_1030434 < baseStart_1030434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030505 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_1030505 : Nat := 118140960795 + 1030505 * 2 ^ 59
def prefixEnd_1030505 : Nat := 4983230072969 + 3 ^ 40 * 1030505 * 2
def baseEnd_1030505 : Nat := 352762921241063918765533

theorem tailTrace_1030505 : CollatzResearch.WordTrace tailWord_1030505 prefixEnd_1030505 352762921241063918765533 := by
  unfold tailWord_1030505
  simp only [CollatzResearch.WordTrace]
  refine ⟨37585605131663856087332969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057070087775904058221979 37585605131663856087332969)
  ·
    refine ⟨28189203848747892065499727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37585605131663856087332969 28189203848747892065499727)
    ·
      refine ⟨42283805773121838098249591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28189203848747892065499727 42283805773121838098249591)
      ·
        refine ⟨63425708659682757147374387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42283805773121838098249591 63425708659682757147374387)
        ·
          refine ⟨95138562989524135721061581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63425708659682757147374387 95138562989524135721061581)
          ·
            refine ⟨35676961121071550895398093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95138562989524135721061581 35676961121071550895398093)
            ·
              refine ⟨13378860420401831585774285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35676961121071550895398093 13378860420401831585774285)
              ·
                refine ⟨5017072657650686844665357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13378860420401831585774285 5017072657650686844665357)
                ·
                  refine ⟨1881402246619007566749509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5017072657650686844665357 1881402246619007566749509)
                  ·
                    refine ⟨352762921241063918765533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881402246619007566749509 352762921241063918765533)
                    ·
                      rfl

theorem cell22_1030505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_1030505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030505 prefixEnd_1030505 := by exact prefixLift 1030505
  have htrace : WordTrace (prefixWord ++ tailWord_1030505) baseStart_1030505 baseEnd_1030505 := by
    simpa [prefixWord, tailWord_1030505, baseEnd_1030505] using wordTrace_append hprefix tailTrace_1030505
  have hstable : (prefixWord ++ tailWord_1030505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030505).length < 2 ^ (prefixWord ++ tailWord_1030505).sum := by decide
  have hdescent : baseEnd_1030505 < baseStart_1030505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030537 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 6]
def baseStart_1030537 : Nat := 118140960795 + 1030537 * 2 ^ 59
def prefixEnd_1030537 : Nat := 4983230072969 + 3 ^ 40 * 1030537 * 2
def baseEnd_1030537 : Nat := 117591291831675500655145

theorem tailTrace_1030537 : CollatzResearch.WordTrace tailWord_1030537 prefixEnd_1030537 117591291831675500655145 := by
  unfold tailWord_1030537
  simp only [CollatzResearch.WordTrace]
  refine ⟨37586772267547925552497865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057848178365283701665243 37586772267547925552497865)
  ·
    refine ⟨28190079200660944164373399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37586772267547925552497865 28190079200660944164373399)
    ·
      refine ⟨42285118800991416246560099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28190079200660944164373399 42285118800991416246560099)
      ·
        refine ⟨63427678201487124369840149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42285118800991416246560099 63427678201487124369840149)
        ·
          refine ⟨2973172415694708954836257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63427678201487124369840149 2973172415694708954836257)
          ·
            refine ⟨2229879311771031716127193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2973172415694708954836257 2229879311771031716127193)
            ·
              refine ⟨1672409483828273787095395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229879311771031716127193 1672409483828273787095395)
              ·
                refine ⟨2508614225742410680643093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672409483828273787095395 2508614225742410680643093)
                ·
                  refine ⟨117591291831675500655145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2508614225742410680643093 117591291831675500655145)
                  ·
                    rfl

theorem cell22_1030537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_1030537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030537 prefixEnd_1030537 := by exact prefixLift 1030537
  have htrace : WordTrace (prefixWord ++ tailWord_1030537) baseStart_1030537 baseEnd_1030537 := by
    simpa [prefixWord, tailWord_1030537, baseEnd_1030537] using wordTrace_append hprefix tailTrace_1030537
  have hstable : (prefixWord ++ tailWord_1030537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030537).length < 2 ^ (prefixWord ++ tailWord_1030537).sum := by decide
  have hdescent : baseEnd_1030537 < baseStart_1030537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030565 : List Nat := [1, 3, 1, 2, 1, 1, 5, 8]
def baseStart_1030565 : Nat := 118140960795 + 1030565 * 2 ^ 59
def prefixEnd_1030565 : Nat := 4983230072969 + 3 ^ 40 * 1030565 * 2
def baseEnd_1030565 : Nat := 39198162274138195807261

theorem tailTrace_1030565 : CollatzResearch.WordTrace tailWord_1030565 prefixEnd_1030565 39198162274138195807261 := by
  unfold tailWord_1030565
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587793511446486334517149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25058529007630990889678099 37587793511446486334517149)
  ·
    refine ⟨14095422566792432375443931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37587793511446486334517149 14095422566792432375443931)
    ·
      refine ⟨21143133850188648563165897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14095422566792432375443931 21143133850188648563165897)
      ·
        refine ⟨15857350387641486422374423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21143133850188648563165897 15857350387641486422374423)
        ·
          refine ⟨23786025581462229633561635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15857350387641486422374423 23786025581462229633561635)
          ·
            refine ⟨35679038372193344450342453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23786025581462229633561635 35679038372193344450342453)
            ·
              refine ⟨3344909847393126042219605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35679038372193344450342453 3344909847393126042219605)
              ·
                refine ⟨39198162274138195807261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3344909847393126042219605 39198162274138195807261)
                ·
                  rfl

theorem cell22_1030565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 8].length) (baseStart_1030565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030565 prefixEnd_1030565 := by exact prefixLift 1030565
  have htrace : WordTrace (prefixWord ++ tailWord_1030565) baseStart_1030565 baseEnd_1030565 := by
    simpa [prefixWord, tailWord_1030565, baseEnd_1030565] using wordTrace_append hprefix tailTrace_1030565
  have hstable : (prefixWord ++ tailWord_1030565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030565).length < 2 ^ (prefixWord ++ tailWord_1030565).sum := by decide
  have hdescent : baseEnd_1030565 < baseStart_1030565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030567 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1030567 : Nat := 118140960795 + 1030567 * 2 ^ 59
def prefixEnd_1030567 : Nat := 4983230072969 + 3 ^ 40 * 1030567 * 2
def baseEnd_1030567 : Nat := 352784145108116423715343

theorem tailTrace_1030567 : CollatzResearch.WordTrace tailWord_1030567 prefixEnd_1030567 352784145108116423715343 := by
  unfold tailWord_1030567
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587866457439240676089955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25058577638292827117393303 37587866457439240676089955)
  ·
    refine ⟨56381799686158861014134933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37587866457439240676089955 56381799686158861014134933)
    ·
      refine ⟨2642896860288696610037575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56381799686158861014134933 2642896860288696610037575)
      ·
        refine ⟨3964345290433044915056363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2642896860288696610037575 3964345290433044915056363)
        ·
          refine ⟨5946517935649567372584545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964345290433044915056363 5946517935649567372584545)
          ·
            refine ⟨4459888451737175529438409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5946517935649567372584545 4459888451737175529438409)
            ·
              refine ⟨3344916338802881647078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4459888451737175529438409 3344916338802881647078807)
              ·
                refine ⟨5017374508204322470618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344916338802881647078807 5017374508204322470618211)
                ·
                  refine ⟨7526061762306483705927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017374508204322470618211 7526061762306483705927317)
                  ·
                    refine ⟨352784145108116423715343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7526061762306483705927317 352784145108116423715343)
                    ·
                      rfl

theorem cell22_1030567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1030567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030567 prefixEnd_1030567 := by exact prefixLift 1030567
  have htrace : WordTrace (prefixWord ++ tailWord_1030567) baseStart_1030567 baseEnd_1030567 := by
    simpa [prefixWord, tailWord_1030567, baseEnd_1030567] using wordTrace_append hprefix tailTrace_1030567
  have hstable : (prefixWord ++ tailWord_1030567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030567).length < 2 ^ (prefixWord ++ tailWord_1030567).sum := by decide
  have hdescent : baseEnd_1030567 < baseStart_1030567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030595 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_1030595 : Nat := 118140960795 + 1030595 * 2 ^ 59
def prefixEnd_1030595 : Nat := 4983230072969 + 3 ^ 40 * 1030595 * 2
def baseEnd_1030595 : Nat := 352793730080333684015257

theorem tailTrace_1030595 : CollatzResearch.WordTrace tailWord_1030595 prefixEnd_1030595 352793730080333684015257 := by
  unfold tailWord_1030595
  simp only [CollatzResearch.WordTrace]
  refine ⟨37588887701337801458109239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25059258467558534305406159 37588887701337801458109239)
  ·
    refine ⟨56383331552006702187163859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37588887701337801458109239 56383331552006702187163859)
    ·
      refine ⟨84574997328010053280745789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56383331552006702187163859 84574997328010053280745789)
      ·
        refine ⟨31715623998003769980279671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84574997328010053280745789 31715623998003769980279671)
        ·
          refine ⟨47573435997005654970419507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31715623998003769980279671 47573435997005654970419507)
          ·
            refine ⟨71360153995508482455629261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47573435997005654970419507 71360153995508482455629261)
            ·
              refine ⟨26760057748315680920860973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71360153995508482455629261 26760057748315680920860973)
              ·
                refine ⟨10035021655618380345322865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26760057748315680920860973 10035021655618380345322865)
                ·
                  refine ⟨7526266241713785258992149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035021655618380345322865 7526266241713785258992149)
                  ·
                    refine ⟨352793730080333684015257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7526266241713785258992149 352793730080333684015257)
                    ·
                      rfl

theorem cell22_1030595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_1030595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030595 prefixEnd_1030595 := by exact prefixLift 1030595
  have htrace : WordTrace (prefixWord ++ tailWord_1030595) baseStart_1030595 baseEnd_1030595 := by
    simpa [prefixWord, tailWord_1030595, baseEnd_1030595] using wordTrace_append hprefix tailTrace_1030595
  have hstable : (prefixWord ++ tailWord_1030595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030595).length < 2 ^ (prefixWord ++ tailWord_1030595).sum := by decide
  have hdescent : baseEnd_1030595 < baseStart_1030595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030631 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1030631 : Nat := 118140960795 + 1030631 * 2 ^ 59
def prefixEnd_1030631 : Nat := 4983230072969 + 3 ^ 40 * 1030631 * 2
def baseEnd_1030631 : Nat := 352806053616041590115147

theorem tailTrace_1030631 : CollatzResearch.WordTrace tailWord_1030631 prefixEnd_1030631 352806053616041590115147 := by
  unfold tailWord_1030631
  simp only [CollatzResearch.WordTrace]
  refine ⟨37590200729207379606419747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25060133819471586404279831 37590200729207379606419747)
  ·
    refine ⟨56385301093811069409629621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37590200729207379606419747 56385301093811069409629621)
    ·
      refine ⟨5286121977544787757152777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56385301093811069409629621 5286121977544787757152777)
      ·
        refine ⟨3964591483158590817864583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5286121977544787757152777 3964591483158590817864583)
        ·
          refine ⟨5946887224737886226796875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964591483158590817864583 5946887224737886226796875)
          ·
            refine ⟨8920330837106829340195313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946887224737886226796875 8920330837106829340195313)
            ·
              refine ⟨6690248127830122005146485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8920330837106829340195313 6690248127830122005146485)
              ·
                refine ⟨627210761984073937982483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6690248127830122005146485 627210761984073937982483)
                ·
                  refine ⟨940816142976110906973725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627210761984073937982483 940816142976110906973725)
                  ·
                    refine ⟨352806053616041590115147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940816142976110906973725 352806053616041590115147)
                    ·
                      rfl

theorem cell22_1030631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1030631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030631 prefixEnd_1030631 := by exact prefixLift 1030631
  have htrace : WordTrace (prefixWord ++ tailWord_1030631) baseStart_1030631 baseEnd_1030631 := by
    simpa [prefixWord, tailWord_1030631, baseEnd_1030631] using wordTrace_append hprefix tailTrace_1030631
  have hstable : (prefixWord ++ tailWord_1030631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030631).length < 2 ^ (prefixWord ++ tailWord_1030631).sum := by decide
  have hdescent : baseEnd_1030631 < baseStart_1030631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030691 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 1, 4]
def baseStart_1030691 : Nat := 118140960795 + 1030691 * 2 ^ 59
def prefixEnd_1030691 : Nat := 4983230072969 + 3 ^ 40 * 1030691 * 2
def baseEnd_1030691 : Nat := 352826592842221433614963

theorem tailTrace_1030691 : CollatzResearch.WordTrace tailWord_1030691 prefixEnd_1030691 352826592842221433614963 := by
  unfold tailWord_1030691
  simp only [CollatzResearch.WordTrace]
  refine ⟨37592389108990009853603927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25061592739326673235735951 37592389108990009853603927)
  ·
    refine ⟨56388583663485014780405891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37592389108990009853603927 56388583663485014780405891)
    ·
      refine ⟨84582875495227522170608837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56388583663485014780405891 84582875495227522170608837)
      ·
        refine ⟨15859289155355160406989157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84582875495227522170608837 15859289155355160406989157)
        ·
          refine ⟨2973616716629092576310467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15859289155355160406989157 2973616716629092576310467)
          ·
            refine ⟨4460425074943638864465701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973616716629092576310467 4460425074943638864465701)
            ·
              refine ⟨836329701551932287087319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4460425074943638864465701 836329701551932287087319)
              ·
                refine ⟨1254494552327898430630979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836329701551932287087319 1254494552327898430630979)
                ·
                  refine ⟨1881741828491847645946469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254494552327898430630979 1881741828491847645946469)
                  ·
                    refine ⟨352826592842221433614963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1881741828491847645946469 352826592842221433614963)
                    ·
                      rfl

theorem cell22_1030691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 4].length) (baseStart_1030691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030691 prefixEnd_1030691 := by exact prefixLift 1030691
  have htrace : WordTrace (prefixWord ++ tailWord_1030691) baseStart_1030691 baseEnd_1030691 := by
    simpa [prefixWord, tailWord_1030691, baseEnd_1030691] using wordTrace_append hprefix tailTrace_1030691
  have hstable : (prefixWord ++ tailWord_1030691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030691).length < 2 ^ (prefixWord ++ tailWord_1030691).sum := by decide
  have hdescent : baseEnd_1030691 < baseStart_1030691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030695 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 5]
def baseStart_1030695 : Nat := 118140960795 + 1030695 * 2 ^ 59
def prefixEnd_1030695 : Nat := 4983230072969 + 3 ^ 40 * 1030695 * 2
def baseEnd_1030695 : Nat := 117609320707988918838317

theorem tailTrace_1030695 : CollatzResearch.WordTrace tailWord_1030695 prefixEnd_1030695 117609320707988918838317 := by
  unfold tailWord_1030695
  simp only [CollatzResearch.WordTrace]
  refine ⟨37592535000975518536749539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25061690000650345691166359 37592535000975518536749539)
  ·
    refine ⟨56388802501463277805124309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37592535000975518536749539 56388802501463277805124309)
    ·
      refine ⟨1321612558628045573557601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56388802501463277805124309 1321612558628045573557601)
      ·
        refine ⟨991209418971034180168201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1321612558628045573557601 991209418971034180168201)
        ·
          refine ⟨743407064228275635126151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991209418971034180168201 743407064228275635126151)
          ·
            refine ⟨1115110596342413452689227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743407064228275635126151 1115110596342413452689227)
            ·
              refine ⟨1672665894513620179033841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115110596342413452689227 1672665894513620179033841)
              ·
                refine ⟨1254499420885215134275381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672665894513620179033841 1254499420885215134275381)
                ·
                  refine ⟨117609320707988918838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1254499420885215134275381 117609320707988918838317)
                  ·
                    rfl

theorem cell22_1030695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 5].length) (baseStart_1030695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030695 prefixEnd_1030695 := by exact prefixLift 1030695
  have htrace : WordTrace (prefixWord ++ tailWord_1030695) baseStart_1030695 baseEnd_1030695 := by
    simpa [prefixWord, tailWord_1030695, baseEnd_1030695] using wordTrace_append hprefix tailTrace_1030695
  have hstable : (prefixWord ++ tailWord_1030695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030695).length < 2 ^ (prefixWord ++ tailWord_1030695).sum := by decide
  have hdescent : baseEnd_1030695 < baseStart_1030695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030721 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1030721 : Nat := 118140960795 + 1030721 * 2 ^ 59
def prefixEnd_1030721 : Nat := 4983230072969 + 3 ^ 40 * 1030721 * 2
def baseEnd_1030721 : Nat := 352836862455311355364871

theorem tailTrace_1030721 : CollatzResearch.WordTrace tailWord_1030721 prefixEnd_1030721 352836862455311355364871 := by
  unfold tailWord_1030721
  simp only [CollatzResearch.WordTrace]
  refine ⟨37593483298881324977196017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25062322199254216651464011 37593483298881324977196017)
  ·
    refine ⟨28195112474160993732897013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37593483298881324977196017 28195112474160993732897013)
    ·
      refine ⟨2643291794452593162459095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28195112474160993732897013 2643291794452593162459095)
      ·
        refine ⟨3964937691678889743688643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643291794452593162459095 3964937691678889743688643)
        ·
          refine ⟨5947406537518334615532965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964937691678889743688643 5947406537518334615532965)
          ·
            refine ⟨1115138725784687740412431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5947406537518334615532965 1115138725784687740412431)
            ·
              refine ⟨1672708088677031610618647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115138725784687740412431 1672708088677031610618647)
              ·
                refine ⟨2509062133015547415927971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672708088677031610618647 2509062133015547415927971)
                ·
                  refine ⟨3763593199523321123891957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509062133015547415927971 3763593199523321123891957)
                  ·
                    refine ⟨352836862455311355364871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3763593199523321123891957 352836862455311355364871)
                    ·
                      rfl

theorem cell22_1030721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1030721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030721 prefixEnd_1030721 := by exact prefixLift 1030721
  have htrace : WordTrace (prefixWord ++ tailWord_1030721) baseStart_1030721 baseEnd_1030721 := by
    simpa [prefixWord, tailWord_1030721, baseEnd_1030721] using wordTrace_append hprefix tailTrace_1030721
  have hstable : (prefixWord ++ tailWord_1030721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030721).length < 2 ^ (prefixWord ++ tailWord_1030721).sum := by decide
  have hdescent : baseEnd_1030721 < baseStart_1030721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030732 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1030732 : Nat := 118140960795 + 1030732 * 2 ^ 59
def prefixEnd_1030732 : Nat := 4983230072969 + 3 ^ 40 * 1030732 * 2
def baseEnd_1030732 : Nat := 352840627980110993339837

theorem tailTrace_1030732 : CollatzResearch.WordTrace tailWord_1030732 prefixEnd_1030732 352840627980110993339837 := by
  unfold tailWord_1030732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796942250920736927923225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25062589667894315903897633 18796942250920736927923225)
  ·
    refine ⟨14097706688190552695942419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18796942250920736927923225 14097706688190552695942419)
    ·
      refine ⟨21146560032285829043913629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14097706688190552695942419 21146560032285829043913629)
      ·
        refine ⟨7929960012107185891467611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21146560032285829043913629 7929960012107185891467611)
        ·
          refine ⟨11894940018160778837201417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929960012107185891467611 11894940018160778837201417)
          ·
            refine ⟨8921205013620584127901063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11894940018160778837201417 8921205013620584127901063)
            ·
              refine ⟨13381807520430876191851595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921205013620584127901063 13381807520430876191851595)
              ·
                refine ⟨20072711280646314287777393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381807520430876191851595 20072711280646314287777393)
                ·
                  refine ⟨15054533460484735715833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20072711280646314287777393 15054533460484735715833045)
                  ·
                    refine ⟨352840627980110993339837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15054533460484735715833045 352840627980110993339837)
                    ·
                      rfl

theorem cell22_1030732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1030732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030732 prefixEnd_1030732 := by exact prefixLift 1030732
  have htrace : WordTrace (prefixWord ++ tailWord_1030732) baseStart_1030732 baseEnd_1030732 := by
    simpa [prefixWord, tailWord_1030732, baseEnd_1030732] using wordTrace_append hprefix tailTrace_1030732
  have hstable : (prefixWord ++ tailWord_1030732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030732).length < 2 ^ (prefixWord ++ tailWord_1030732).sum := by decide
  have hdescent : baseEnd_1030732 < baseStart_1030732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030734 : List Nat := [4, 1, 1, 1, 1, 2, 6, 6]
def baseStart_1030734 : Nat := 118140960795 + 1030734 * 2 ^ 59
def prefixEnd_1030734 : Nat := 4983230072969 + 3 ^ 40 * 1030734 * 2
def baseEnd_1030734 : Nat := 39204590291220406087759

theorem tailTrace_1030734 : CollatzResearch.WordTrace tailWord_1030734 prefixEnd_1030734 39204590291220406087759 := by
  unfold tailWord_1030734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699244680979278524677407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25062638298556152131612837 4699244680979278524677407)
  ·
    refine ⟨7048867021468917787016111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699244680979278524677407 7048867021468917787016111)
    ·
      refine ⟨10573300532203376680524167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048867021468917787016111 10573300532203376680524167)
      ·
        refine ⟨15859950798305065020786251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10573300532203376680524167 15859950798305065020786251)
        ·
          refine ⟨23789926197457597531179377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859950798305065020786251 23789926197457597531179377)
          ·
            refine ⟨17842444648093198148384533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23789926197457597531179377 17842444648093198148384533)
            ·
              refine ⟨836364592879368663205525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17842444648093198148384533 836364592879368663205525)
              ·
                refine ⟨39204590291220406087759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 836364592879368663205525 39204590291220406087759)
                ·
                  rfl

theorem cell22_1030734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_1030734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030734 prefixEnd_1030734 := by exact prefixLift 1030734
  have htrace : WordTrace (prefixWord ++ tailWord_1030734) baseStart_1030734 baseEnd_1030734 := by
    simpa [prefixWord, tailWord_1030734, baseEnd_1030734] using wordTrace_append hprefix tailTrace_1030734
  have hstable : (prefixWord ++ tailWord_1030734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030734).length < 2 ^ (prefixWord ++ tailWord_1030734).sum := by decide
  have hdescent : baseEnd_1030734 < baseStart_1030734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030817 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 1, 3]
def baseStart_1030817 : Nat := 118140960795 + 1030817 * 2 ^ 59
def prefixEnd_1030817 : Nat := 4983230072969 + 3 ^ 40 * 1030817 * 2
def baseEnd_1030817 : Nat := 352869725217199104964577

theorem tailTrace_1030817 : CollatzResearch.WordTrace tailWord_1030817 prefixEnd_1030817 352869725217199104964577 := by
  unfold tailWord_1030817
  simp only [CollatzResearch.WordTrace]
  refine ⟨37596984706533533372690705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25064656471022355581793803 37596984706533533372690705)
  ·
    refine ⟨28197738529900150029518029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37596984706533533372690705 28197738529900150029518029)
    ·
      refine ⟨10574151948712556261069261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28197738529900150029518029 10574151948712556261069261)
      ·
        refine ⟨3965306980767208597900973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10574151948712556261069261 3965306980767208597900973)
        ·
          refine ⟨1486990117787703224212865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3965306980767208597900973 1486990117787703224212865)
          ·
            refine ⟨1115242588340777418159649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1486990117787703224212865 1115242588340777418159649)
            ·
              refine ⟨836431941255583063619737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115242588340777418159649 836431941255583063619737)
              ·
                refine ⟨627323955941687297714803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836431941255583063619737 627323955941687297714803)
                ·
                  refine ⟨940985933912530946572205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627323955941687297714803 940985933912530946572205)
                  ·
                    refine ⟨352869725217199104964577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 940985933912530946572205 352869725217199104964577)
                    ·
                      rfl

theorem cell22_1030817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_1030817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030817 prefixEnd_1030817 := by exact prefixLift 1030817
  have htrace : WordTrace (prefixWord ++ tailWord_1030817) baseStart_1030817 baseEnd_1030817 := by
    simpa [prefixWord, tailWord_1030817, baseEnd_1030817] using wordTrace_append hprefix tailTrace_1030817
  have hstable : (prefixWord ++ tailWord_1030817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030817).length < 2 ^ (prefixWord ++ tailWord_1030817).sum := by decide
  have hdescent : baseEnd_1030817 < baseStart_1030817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030858 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_1030858 : Nat := 118140960795 + 1030858 * 2 ^ 59
def prefixEnd_1030858 : Nat := 4983230072969 + 3 ^ 40 * 1030858 * 2
def baseEnd_1030858 : Nat := 117627920118362888229817

theorem tailTrace_1030858 : CollatzResearch.WordTrace tailWord_1030858 prefixEnd_1030858 117627920118362888229817 := by
  unfold tailWord_1030858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9399620024846249343733307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25065653399589998249955485 9399620024846249343733307)
  ·
    refine ⟨14099430037269374015599961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9399620024846249343733307 14099430037269374015599961)
    ·
      refine ⟨10574572527952030511699971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14099430037269374015599961 10574572527952030511699971)
      ·
        refine ⟨15861858791928045767549957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10574572527952030511699971 15861858791928045767549957)
        ·
          refine ⟨2974098523486508581415617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15861858791928045767549957 2974098523486508581415617)
          ·
            refine ⟨2230573892614881436061713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974098523486508581415617 2230573892614881436061713)
            ·
              refine ⟨1672930419461161077046285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230573892614881436061713 1672930419461161077046285)
              ·
                refine ⟨627348907297935403892357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1672930419461161077046285 627348907297935403892357)
                ·
                  refine ⟨117627920118362888229817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627348907297935403892357 117627920118362888229817)
                  ·
                    rfl

theorem cell22_1030858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_1030858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030858 prefixEnd_1030858 := by exact prefixLift 1030858
  have htrace : WordTrace (prefixWord ++ tailWord_1030858) baseStart_1030858 baseEnd_1030858 := by
    simpa [prefixWord, tailWord_1030858, baseEnd_1030858] using wordTrace_append hprefix tailTrace_1030858
  have hstable : (prefixWord ++ tailWord_1030858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030858).length < 2 ^ (prefixWord ++ tailWord_1030858).sum := by decide
  have hdescent : baseEnd_1030858 < baseStart_1030858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030860 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_1030860 : Nat := 118140960795 + 1030860 * 2 ^ 59
def prefixEnd_1030860 : Nat := 4983230072969 + 3 ^ 40 * 1030860 * 2
def baseEnd_1030860 : Nat := 352884444995961326139445

theorem tailTrace_1030860 : CollatzResearch.WordTrace tailWord_1030860 prefixEnd_1030860 352884444995961326139445 := by
  unfold tailWord_1030860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18799276522688875858253017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25065702030251834477670689 18799276522688875858253017)
  ·
    refine ⟨14099457392016656893689763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18799276522688875858253017 14099457392016656893689763)
    ·
      refine ⟨21149186088024985340534645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14099457392016656893689763 21149186088024985340534645)
      ·
        refine ⟨1982736195752342375675123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21149186088024985340534645 1982736195752342375675123)
        ·
          refine ⟨2974104293628513563512685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982736195752342375675123 2974104293628513563512685)
          ·
            refine ⟨1115289110110692586317257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2974104293628513563512685 1115289110110692586317257)
            ·
              refine ⟨836466832583019439737943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115289110110692586317257 836466832583019439737943)
              ·
                refine ⟨1254700248874529159606915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836466832583019439737943 1254700248874529159606915)
                ·
                  refine ⟨1882050373311793739410373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254700248874529159606915 1882050373311793739410373)
                  ·
                    refine ⟨352884444995961326139445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882050373311793739410373 352884444995961326139445)
                    ·
                      rfl

theorem cell22_1030860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_1030860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030860 prefixEnd_1030860 := by exact prefixLift 1030860
  have htrace : WordTrace (prefixWord ++ tailWord_1030860) baseStart_1030860 baseEnd_1030860 := by
    simpa [prefixWord, tailWord_1030860, baseEnd_1030860] using wordTrace_append hprefix tailTrace_1030860
  have hstable : (prefixWord ++ tailWord_1030860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030860).length < 2 ^ (prefixWord ++ tailWord_1030860).sum := by decide
  have hdescent : baseEnd_1030860 < baseStart_1030860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030929 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1030929 : Nat := 118140960795 + 1030929 * 2 ^ 59
def prefixEnd_1030929 : Nat := 4983230072969 + 3 ^ 40 * 1030929 * 2
def baseEnd_1030929 : Nat := 352908065106068146164233

theorem tailTrace_1030929 : CollatzResearch.WordTrace tailWord_1030929 prefixEnd_1030929 352908065106068146164233 := by
  unfold tailWord_1030929
  simp only [CollatzResearch.WordTrace]
  refine ⟨37601069682127776500767841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25067379788085184333845227 37601069682127776500767841)
  ·
    refine ⟨28200802261595832375575881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37601069682127776500767841 28200802261595832375575881)
    ·
      refine ⟨21150601696196874281681911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28200802261595832375575881 21150601696196874281681911)
      ·
        refine ⟨31725902544295311422522867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150601696196874281681911 31725902544295311422522867)
        ·
          refine ⟨47588853816442967133784301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31725902544295311422522867 47588853816442967133784301)
          ·
            refine ⟨17845820181166112675169113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47588853816442967133784301 17845820181166112675169113)
            ·
              refine ⟨13384365135874584506376835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845820181166112675169113 13384365135874584506376835)
              ·
                refine ⟨20076547703811876759565253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384365135874584506376835 20076547703811876759565253)
                ·
                  refine ⟨3764352694464726892418485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20076547703811876759565253 3764352694464726892418485)
                  ·
                    refine ⟨352908065106068146164233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3764352694464726892418485 352908065106068146164233)
                    ·
                      rfl

theorem cell22_1030929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1030929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030929 prefixEnd_1030929 := by exact prefixLift 1030929
  have htrace : WordTrace (prefixWord ++ tailWord_1030929) baseStart_1030929 baseEnd_1030929 := by
    simpa [prefixWord, tailWord_1030929, baseEnd_1030929] using wordTrace_append hprefix tailTrace_1030929
  have hstable : (prefixWord ++ tailWord_1030929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030929).length < 2 ^ (prefixWord ++ tailWord_1030929).sum := by decide
  have hdescent : baseEnd_1030929 < baseStart_1030929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030935 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 3, 3]
def baseStart_1030935 : Nat := 118140960795 + 1030935 * 2 ^ 59
def prefixEnd_1030935 : Nat := 4983230072969 + 3 ^ 40 * 1030935 * 2
def baseEnd_1030935 : Nat := 352910119028686130514215

theorem tailTrace_1030935 : CollatzResearch.WordTrace tailWord_1030935 prefixEnd_1030935 352910119028686130514215 := by
  unfold tailWord_1030935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37601288520106039525486259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25067525680070693016990839 37601288520106039525486259)
  ·
    refine ⟨56401932780159059288229389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37601288520106039525486259 56401932780159059288229389)
    ·
      refine ⟨21150724792559647233086021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56401932780159059288229389 21150724792559647233086021)
      ·
        refine ⟨3965760898604933856203629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21150724792559647233086021 3965760898604933856203629)
        ·
          refine ⟨1487160336976850196076361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3965760898604933856203629 1487160336976850196076361)
          ·
            refine ⟨1115370252732637647057271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487160336976850196076361 1115370252732637647057271)
            ·
              refine ⟨1673055379098956470585907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115370252732637647057271 1673055379098956470585907)
              ·
                refine ⟨2509583068648434705878861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673055379098956470585907 2509583068648434705878861)
                ·
                  refine ⟨941093650743163014704573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2509583068648434705878861 941093650743163014704573)
                  ·
                    refine ⟨352910119028686130514215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941093650743163014704573 352910119028686130514215)
                    ·
                      rfl

theorem cell22_1030935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_1030935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030935 prefixEnd_1030935 := by exact prefixLift 1030935
  have htrace : WordTrace (prefixWord ++ tailWord_1030935) baseStart_1030935 baseEnd_1030935 := by
    simpa [prefixWord, tailWord_1030935, baseEnd_1030935] using wordTrace_append hprefix tailTrace_1030935
  have hstable : (prefixWord ++ tailWord_1030935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030935).length < 2 ^ (prefixWord ++ tailWord_1030935).sum := by decide
  have hdescent : baseEnd_1030935 < baseStart_1030935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030948 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1030948 : Nat := 118140960795 + 1030948 * 2 ^ 59
def prefixEnd_1030948 : Nat := 4983230072969 + 3 ^ 40 * 1030948 * 2
def baseEnd_1030948 : Nat := 117638189731452809979725

theorem tailTrace_1030948 : CollatzResearch.WordTrace tailWord_1030948 prefixEnd_1030948 117638189731452809979725 := by
  unfold tailWord_1030948
  simp only [CollatzResearch.WordTrace]
  refine ⟨18800881334529471372854749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25067841779372628497139665 18800881334529471372854749)
  ·
    refine ⟨7050330500448551764820531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18800881334529471372854749 7050330500448551764820531)
    ·
      refine ⟨10575495750672827647230797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7050330500448551764820531 10575495750672827647230797)
      ·
        refine ⟨3965810906502310367711549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10575495750672827647230797 3965810906502310367711549)
        ·
          refine ⟨1487179089938366387891831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3965810906502310367711549 1487179089938366387891831)
          ·
            refine ⟨2230768634907549581837747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487179089938366387891831 2230768634907549581837747)
            ·
              refine ⟨3346152952361324372756621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230768634907549581837747 3346152952361324372756621)
              ·
                refine ⟨1254807357135496639783733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3346152952361324372756621 1254807357135496639783733)
                ·
                  refine ⟨117638189731452809979725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1254807357135496639783733 117638189731452809979725)
                  ·
                    rfl

theorem cell22_1030948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1030948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030948 prefixEnd_1030948 := by exact prefixLift 1030948
  have htrace : WordTrace (prefixWord ++ tailWord_1030948) baseStart_1030948 baseEnd_1030948 := by
    simpa [prefixWord, tailWord_1030948, baseEnd_1030948] using wordTrace_append hprefix tailTrace_1030948
  have hstable : (prefixWord ++ tailWord_1030948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030948).length < 2 ^ (prefixWord ++ tailWord_1030948).sum := by decide
  have hdescent : baseEnd_1030948 < baseStart_1030948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030961 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1030961 : Nat := 118140960795 + 1030961 * 2 ^ 59
def prefixEnd_1030961 : Nat := 4983230072969 + 3 ^ 40 * 1030961 * 2
def baseEnd_1030961 : Nat := 352919019360030729364135

theorem tailTrace_1030961 : CollatzResearch.WordTrace tailWord_1030961 prefixEnd_1030961 352919019360030729364135 := by
  unfold tailWord_1030961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37602236818011845965932737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25068157878674563977288491 37602236818011845965932737)
  ·
    refine ⟨28201677613508884474449553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37602236818011845965932737 28201677613508884474449553)
    ·
      refine ⟨21151258210131663355837165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28201677613508884474449553 21151258210131663355837165)
      ·
        refine ⟨7931721828799373758438937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21151258210131663355837165 7931721828799373758438937)
        ·
          refine ⟨5948791371599530318829203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931721828799373758438937 5948791371599530318829203)
          ·
            refine ⟨8923187057399295478243805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948791371599530318829203 8923187057399295478243805)
            ·
              refine ⟨3346195146524735804341427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8923187057399295478243805 3346195146524735804341427)
              ·
                refine ⟨5019292719787103706512141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346195146524735804341427 5019292719787103706512141)
                ·
                  refine ⟨1882234769920163889942053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5019292719787103706512141 1882234769920163889942053)
                  ·
                    refine ⟨352919019360030729364135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882234769920163889942053 352919019360030729364135)
                    ·
                      rfl

theorem cell22_1030961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1030961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030961 prefixEnd_1030961 := by exact prefixLift 1030961
  have htrace : WordTrace (prefixWord ++ tailWord_1030961) baseStart_1030961 baseEnd_1030961 := by
    simpa [prefixWord, tailWord_1030961, baseEnd_1030961] using wordTrace_append hprefix tailTrace_1030961
  have hstable : (prefixWord ++ tailWord_1030961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030961).length < 2 ^ (prefixWord ++ tailWord_1030961).sum := by decide
  have hdescent : baseEnd_1030961 < baseStart_1030961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030982 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1030982 : Nat := 118140960795 + 1030982 * 2 ^ 59
def prefixEnd_1030982 : Nat := 4983230072969 + 3 ^ 40 * 1030982 * 2
def baseEnd_1030982 : Nat := 117642069363064558196357

theorem tailTrace_1030982 : CollatzResearch.WordTrace tailWord_1030982 prefixEnd_1030982 117642069363064558196357 := by
  unfold tailWord_1030982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175093835966742704763975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25068668500623844368298133 1175093835966742704763975)
  ·
    refine ⟨1762640753950114057145963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175093835966742704763975 1762640753950114057145963)
    ·
      refine ⟨2643961130925171085718945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762640753950114057145963 2643961130925171085718945)
      ·
        refine ⟨1982970848193878314289209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643961130925171085718945 1982970848193878314289209)
        ·
          refine ⟨1487228136145408735716907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982970848193878314289209 1487228136145408735716907)
          ·
            refine ⟨2230842204218113103575361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487228136145408735716907 2230842204218113103575361)
            ·
              refine ⟨1673131653163584827681521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230842204218113103575361 1673131653163584827681521)
              ·
                refine ⟨1254848739872688620761141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673131653163584827681521 1254848739872688620761141)
                ·
                  refine ⟨117642069363064558196357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1254848739872688620761141 117642069363064558196357)
                  ·
                    rfl

theorem cell22_1030982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1030982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1030982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1030982 prefixEnd_1030982 := by exact prefixLift 1030982
  have htrace : WordTrace (prefixWord ++ tailWord_1030982) baseStart_1030982 baseEnd_1030982 := by
    simpa [prefixWord, tailWord_1030982, baseEnd_1030982] using wordTrace_append hprefix tailTrace_1030982
  have hstable : (prefixWord ++ tailWord_1030982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030982).length < 2 ^ (prefixWord ++ tailWord_1030982).sum := by decide
  have hdescent : baseEnd_1030982 < baseStart_1030982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031008 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_1031008 : Nat := 118140960795 + 1031008 * 2 ^ 59
def prefixEnd_1031008 : Nat := 4983230072969 + 3 ^ 40 * 1031008 * 2
def baseEnd_1031008 : Nat := 352935108420538273438991

theorem tailTrace_1031008 : CollatzResearch.WordTrace tailWord_1031008 prefixEnd_1031008 352935108420538273438991 := by
  unfold tailWord_1031008
  simp only [CollatzResearch.WordTrace]
  refine ⟨18801975524420786496446839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25069300699227715328595785 18801975524420786496446839)
  ·
    refine ⟨28202963286631179744670259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18801975524420786496446839 28202963286631179744670259)
    ·
      refine ⟨42304444929946769617005389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28202963286631179744670259 42304444929946769617005389)
      ·
        refine ⟨15864166848730038606377021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42304444929946769617005389 15864166848730038606377021)
        ·
          refine ⟨5949062568273764477391383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15864166848730038606377021 5949062568273764477391383)
          ·
            refine ⟨8923593852410646716087075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949062568273764477391383 8923593852410646716087075)
            ·
              refine ⟨13385390778615970074130613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8923593852410646716087075 13385390778615970074130613)
              ·
                refine ⟨1254880385495247194449745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13385390778615970074130613 1254880385495247194449745)
                ·
                  refine ⟨941160289121435395837309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1254880385495247194449745 941160289121435395837309)
                  ·
                    refine ⟨352935108420538273438991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941160289121435395837309 352935108420538273438991)
                    ·
                      rfl

theorem cell22_1031008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_1031008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031008 prefixEnd_1031008 := by exact prefixLift 1031008
  have htrace : WordTrace (prefixWord ++ tailWord_1031008) baseStart_1031008 baseEnd_1031008 := by
    simpa [prefixWord, tailWord_1031008, baseEnd_1031008] using wordTrace_append hprefix tailTrace_1031008
  have hstable : (prefixWord ++ tailWord_1031008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031008).length < 2 ^ (prefixWord ++ tailWord_1031008).sum := by decide
  have hdescent : baseEnd_1031008 < baseStart_1031008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031110 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1031110 : Nat := 118140960795 + 1031110 * 2 ^ 59
def prefixEnd_1031110 : Nat := 4983230072969 + 3 ^ 40 * 1031110 * 2
def baseEnd_1031110 : Nat := 352970025105044007388679

theorem tailTrace_1031110 : CollatzResearch.WordTrace tailWord_1031110 prefixEnd_1031110 352970025105044007388679 := by
  unfold tailWord_1031110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175239727952251387909587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25071780862981362942071189 1175239727952251387909587)
  ·
    refine ⟨1762859591928377081864381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175239727952251387909587 1762859591928377081864381)
    ·
      refine ⟨661072346973141405699143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1762859591928377081864381 661072346973141405699143)
      ·
        refine ⟨991608520459712108548715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661072346973141405699143 991608520459712108548715)
        ·
          refine ⟨1487412780689568162823073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991608520459712108548715 1487412780689568162823073)
          ·
            refine ⟨1115559585517176122117305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487412780689568162823073 1115559585517176122117305)
            ·
              refine ⟨836669689137882091587979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115559585517176122117305 836669689137882091587979)
              ·
                refine ⟨1255004533706823137381969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836669689137882091587979 1255004533706823137381969)
                ·
                  refine ⟨941253400280117353036477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255004533706823137381969 941253400280117353036477)
                  ·
                    refine ⟨352970025105044007388679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941253400280117353036477 352970025105044007388679)
                    ·
                      rfl

theorem cell22_1031110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1031110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031110 prefixEnd_1031110 := by exact prefixLift 1031110
  have htrace : WordTrace (prefixWord ++ tailWord_1031110) baseStart_1031110 baseEnd_1031110 := by
    simpa [prefixWord, tailWord_1031110, baseEnd_1031110] using wordTrace_append hprefix tailTrace_1031110
  have hstable : (prefixWord ++ tailWord_1031110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031110).length < 2 ^ (prefixWord ++ tailWord_1031110).sum := by decide
  have hdescent : baseEnd_1031110 < baseStart_1031110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031130 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1031130 : Nat := 118140960795 + 1031130 * 2 ^ 59
def prefixEnd_1031130 : Nat := 4983230072969 + 3 ^ 40 * 1031130 * 2
def baseEnd_1031130 : Nat := 352976871513770621888617

theorem tailTrace_1031130 : CollatzResearch.WordTrace tailWord_1031130 prefixEnd_1031130 352976871513770621888617 := by
  unfold tailWord_1031130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402100188599896957208711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25072267169599725219223229 9402100188599896957208711)
  ·
    refine ⟨14103150282899845435813067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9402100188599896957208711 14103150282899845435813067)
    ·
      refine ⟨21154725424349768153719601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14103150282899845435813067 21154725424349768153719601)
      ·
        refine ⟨15866044068262326115289701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21154725424349768153719601 15866044068262326115289701)
        ·
          refine ⟨2974883262799186146616819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15866044068262326115289701 2974883262799186146616819)
          ·
            refine ⟨4462324894198779219925229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974883262799186146616819 4462324894198779219925229)
            ·
              refine ⟨1673371835324542207471961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4462324894198779219925229 1673371835324542207471961)
              ·
                refine ⟨1255028876493406655603971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673371835324542207471961 1255028876493406655603971)
                ·
                  refine ⟨1882543314740109983405957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255028876493406655603971 1882543314740109983405957)
                  ·
                    refine ⟨352976871513770621888617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882543314740109983405957 352976871513770621888617)
                    ·
                      rfl

theorem cell22_1031130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1031130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031130 prefixEnd_1031130 := by exact prefixLift 1031130
  have htrace : WordTrace (prefixWord ++ tailWord_1031130) baseStart_1031130 baseEnd_1031130 := by
    simpa [prefixWord, tailWord_1031130, baseEnd_1031130] using wordTrace_append hprefix tailTrace_1031130
  have hstable : (prefixWord ++ tailWord_1031130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031130).length < 2 ^ (prefixWord ++ tailWord_1031130).sum := by decide
  have hdescent : baseEnd_1031130 < baseStart_1031130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031143 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1031143 : Nat := 118140960795 + 1031143 * 2 ^ 59
def prefixEnd_1031143 : Nat := 4983230072969 + 3 ^ 40 * 1031143 * 2
def baseEnd_1031143 : Nat := 352981321679442921313577

theorem tailTrace_1031143 : CollatzResearch.WordTrace tailWord_1031143 prefixEnd_1031143 352981321679442921313577 := by
  unfold tailWord_1031143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37608874903352491049058083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25072583268901660699372055 37608874903352491049058083)
  ·
    refine ⟨56413312355028736573587125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37608874903352491049058083 56413312355028736573587125)
    ·
      refine ⟨5288748033283944053773793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56413312355028736573587125 5288748033283944053773793)
      ·
        refine ⟨3966561024962958040330345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5288748033283944053773793 3966561024962958040330345)
        ·
          refine ⟨2974920768722218530247759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966561024962958040330345 2974920768722218530247759)
          ·
            refine ⟨4462381153083327795371639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974920768722218530247759 4462381153083327795371639)
            ·
              refine ⟨6693571729624991693057459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462381153083327795371639 6693571729624991693057459)
              ·
                refine ⟨10040357594437487539586189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693571729624991693057459 10040357594437487539586189)
                ·
                  refine ⟨3765134097914057827344821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10040357594437487539586189 3765134097914057827344821)
                  ·
                    refine ⟨352981321679442921313577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3765134097914057827344821 352981321679442921313577)
                    ·
                      rfl

theorem cell22_1031143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1031143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031143 prefixEnd_1031143 := by exact prefixLift 1031143
  have htrace : WordTrace (prefixWord ++ tailWord_1031143) baseStart_1031143 baseEnd_1031143 := by
    simpa [prefixWord, tailWord_1031143, baseEnd_1031143] using wordTrace_append hprefix tailTrace_1031143
  have hstable : (prefixWord ++ tailWord_1031143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031143).length < 2 ^ (prefixWord ++ tailWord_1031143).sum := by decide
  have hdescent : baseEnd_1031143 < baseStart_1031143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031171 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_1031171 : Nat := 118140960795 + 1031171 * 2 ^ 59
def prefixEnd_1031171 : Nat := 4983230072969 + 3 ^ 40 * 1031171 * 2
def baseEnd_1031171 : Nat := 352990906651660181613491

theorem tailTrace_1031171 : CollatzResearch.WordTrace tailWord_1031171 prefixEnd_1031171 352990906651660181613491 := by
  unfold tailWord_1031171
  simp only [CollatzResearch.WordTrace]
  refine ⟨37609896147251051831077367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25073264098167367887384911 37609896147251051831077367)
  ·
    refine ⟨56414844220876577746616051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37609896147251051831077367 56414844220876577746616051)
    ·
      refine ⟨84622266331314866619924077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56414844220876577746616051 84622266331314866619924077)
      ·
        refine ⟨31733349874243074982471529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84622266331314866619924077 31733349874243074982471529)
        ·
          refine ⟨23800012405682306236853647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31733349874243074982471529 23800012405682306236853647)
          ·
            refine ⟨35700018608523459355280471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23800012405682306236853647 35700018608523459355280471)
            ·
              refine ⟨53550027912785189032920707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35700018608523459355280471 53550027912785189032920707)
              ·
                refine ⟨80325041869177783549381061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53550027912785189032920707 80325041869177783549381061)
                ·
                  refine ⟨15060945350470834415508949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80325041869177783549381061 15060945350470834415508949)
                  ·
                    refine ⟨352990906651660181613491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15060945350470834415508949 352990906651660181613491)
                    ·
                      rfl

theorem cell22_1031171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_1031171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031171 prefixEnd_1031171 := by exact prefixLift 1031171
  have htrace : WordTrace (prefixWord ++ tailWord_1031171) baseStart_1031171 baseEnd_1031171 := by
    simpa [prefixWord, tailWord_1031171, baseEnd_1031171] using wordTrace_append hprefix tailTrace_1031171
  have hstable : (prefixWord ++ tailWord_1031171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031171).length < 2 ^ (prefixWord ++ tailWord_1031171).sum := by decide
  have hdescent : baseEnd_1031171 < baseStart_1031171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031218 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1031218 : Nat := 118140960795 + 1031218 * 2 ^ 59
def prefixEnd_1031218 : Nat := 4983230072969 + 3 ^ 40 * 1031218 * 2
def baseEnd_1031218 : Nat := 117668998570722575229449

theorem tailTrace_1031218 : CollatzResearch.WordTrace tailWord_1031218 prefixEnd_1031218 117668998570722575229449 := by
  unfold tailWord_1031218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402902594520194714509577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25074406918720519238692205 9402902594520194714509577)
  ·
    refine ⟨7052176945890146035882183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9402902594520194714509577 7052176945890146035882183)
    ·
      refine ⟨10578265418835219053823275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052176945890146035882183 10578265418835219053823275)
      ·
        refine ⟨15867398128252828580734913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578265418835219053823275 15867398128252828580734913)
        ·
          refine ⟨11900548596189621435551185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15867398128252828580734913 11900548596189621435551185)
          ·
            refine ⟨8925411447142216076663389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900548596189621435551185 8925411447142216076663389)
            ·
              refine ⟨3347029292678331028748771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8925411447142216076663389 3347029292678331028748771)
              ·
                refine ⟨5020543939017496543123157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3347029292678331028748771 5020543939017496543123157)
                ·
                  refine ⟨117668998570722575229449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5020543939017496543123157 117668998570722575229449)
                  ·
                    rfl

theorem cell22_1031218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1031218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031218 prefixEnd_1031218 := by exact prefixLift 1031218
  have htrace : WordTrace (prefixWord ++ tailWord_1031218) baseStart_1031218 baseEnd_1031218 := by
    simpa [prefixWord, tailWord_1031218, baseEnd_1031218] using wordTrace_append hprefix tailTrace_1031218
  have hstable : (prefixWord ++ tailWord_1031218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031218).length < 2 ^ (prefixWord ++ tailWord_1031218).sum := by decide
  have hdescent : baseEnd_1031218 < baseStart_1031218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031222 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1031222 : Nat := 118140960795 + 1031222 * 2 ^ 59
def prefixEnd_1031222 : Nat := 4983230072969 + 3 ^ 40 * 1031222 * 2
def baseEnd_1031222 : Nat := 353008364993913048588335

theorem tailTrace_1031222 : CollatzResearch.WordTrace tailWord_1031222 prefixEnd_1031222 353008364993913048588335 := by
  unfold tailWord_1031222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350734766879142971323995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25074504180044191694122613 2350734766879142971323995)
  ·
    refine ⟨3526102150318714456985993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2350734766879142971323995 3526102150318714456985993)
    ·
      refine ⟨2644576612739035842739495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3526102150318714456985993 2644576612739035842739495)
      ·
        refine ⟨3966864919108553764109243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644576612739035842739495 3966864919108553764109243)
        ·
          refine ⟨5950297378662830646163865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966864919108553764109243 5950297378662830646163865)
          ·
            refine ⟨4462723033997122984622899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5950297378662830646163865 4462723033997122984622899)
            ·
              refine ⟨6694084550995684476934349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462723033997122984622899 6694084550995684476934349)
              ·
                refine ⟨2510281706623381678850381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6694084550995684476934349 2510281706623381678850381)
                ·
                  refine ⟨941355639983768129568893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2510281706623381678850381 941355639983768129568893)
                  ·
                    refine ⟨353008364993913048588335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941355639983768129568893 353008364993913048588335)
                    ·
                      rfl

theorem cell22_1031222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1031222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031222 prefixEnd_1031222 := by exact prefixLift 1031222
  have htrace : WordTrace (prefixWord ++ tailWord_1031222) baseStart_1031222 baseEnd_1031222 := by
    simpa [prefixWord, tailWord_1031222, baseEnd_1031222] using wordTrace_append hprefix tailTrace_1031222
  have hstable : (prefixWord ++ tailWord_1031222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031222).length < 2 ^ (prefixWord ++ tailWord_1031222).sum := by decide
  have hdescent : baseEnd_1031222 < baseStart_1031222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031235 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 5]
def baseStart_1031235 : Nat := 118140960795 + 1031235 * 2 ^ 59
def prefixEnd_1031235 : Nat := 4983230072969 + 3 ^ 40 * 1031235 * 2
def baseEnd_1031235 : Nat := 117670938386528449337765

theorem tailTrace_1031235 : CollatzResearch.WordTrace tailWord_1031235 prefixEnd_1031235 117670938386528449337765 := by
  unfold tailWord_1031235
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612230419019190761407159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25074820279346127174271439 37612230419019190761407159)
  ·
    refine ⟨56418345628528786142110739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37612230419019190761407159 56418345628528786142110739)
    ·
      refine ⟨84627518442793179213166109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56418345628528786142110739 84627518442793179213166109)
      ·
        refine ⟨31735319416047442204937291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84627518442793179213166109 31735319416047442204937291)
        ·
          refine ⟨47602979124071163307405937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31735319416047442204937291 47602979124071163307405937)
          ·
            refine ⟨35702234343053372480554453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47602979124071163307405937 35702234343053372480554453)
            ·
              refine ⟨836771117415313417512995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35702234343053372480554453 836771117415313417512995)
              ·
                refine ⟨1255156676122970126269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836771117415313417512995 1255156676122970126269493)
                ·
                  refine ⟨117670938386528449337765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1255156676122970126269493 117670938386528449337765)
                  ·
                    rfl

theorem cell22_1031235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 5].length) (baseStart_1031235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031235 prefixEnd_1031235 := by exact prefixLift 1031235
  have htrace : WordTrace (prefixWord ++ tailWord_1031235) baseStart_1031235 baseEnd_1031235 := by
    simpa [prefixWord, tailWord_1031235, baseEnd_1031235] using wordTrace_append hprefix tailTrace_1031235
  have hstable : (prefixWord ++ tailWord_1031235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031235).length < 2 ^ (prefixWord ++ tailWord_1031235).sum := by decide
  have hdescent : baseEnd_1031235 < baseStart_1031235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031248 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_1031248 : Nat := 118140960795 + 1031248 * 2 ^ 59
def prefixEnd_1031248 : Nat := 4983230072969 + 3 ^ 40 * 1031248 * 2
def baseEnd_1031248 : Nat := 353017265325257647438255

theorem tailTrace_1031248 : CollatzResearch.WordTrace tailWord_1031248 prefixEnd_1031248 353017265325257647438255 := by
  unfold tailWord_1031248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806352283986046990815199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25075136378648062654420265 18806352283986046990815199)
  ·
    refine ⟨28209528425979070486222799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18806352283986046990815199 28209528425979070486222799)
    ·
      refine ⟨42314292638968605729334199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28209528425979070486222799 42314292638968605729334199)
      ·
        refine ⟨63471438958452908594001299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42314292638968605729334199 63471438958452908594001299)
        ·
          refine ⟨95207158437679362891001949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63471438958452908594001299 95207158437679362891001949)
          ·
            refine ⟨35702684414129761084125731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95207158437679362891001949 35702684414129761084125731)
            ·
              refine ⟨53554026621194641626188597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35702684414129761084125731 53554026621194641626188597)
              ·
                refine ⟨5020689995736997652455181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53554026621194641626188597 5020689995736997652455181)
                ·
                  refine ⟨1882758748401374119670693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5020689995736997652455181 1882758748401374119670693)
                  ·
                    refine ⟨353017265325257647438255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882758748401374119670693 353017265325257647438255)
                    ·
                      rfl

theorem cell22_1031248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_1031248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031248 prefixEnd_1031248 := by exact prefixLift 1031248
  have htrace : WordTrace (prefixWord ++ tailWord_1031248) baseStart_1031248 baseEnd_1031248 := by
    simpa [prefixWord, tailWord_1031248, baseEnd_1031248] using wordTrace_append hprefix tailTrace_1031248
  have hstable : (prefixWord ++ tailWord_1031248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031248).length < 2 ^ (prefixWord ++ tailWord_1031248).sum := by decide
  have hdescent : baseEnd_1031248 < baseStart_1031248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031265 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1031265 : Nat := 118140960795 + 1031265 * 2 ^ 59
def prefixEnd_1031265 : Nat := 4983230072969 + 3 ^ 40 * 1031265 * 2
def baseEnd_1031265 : Nat := 353023084772675269763203

theorem tailTrace_1031265 : CollatzResearch.WordTrace tailWord_1031265 prefixEnd_1031265 353023084772675269763203 := by
  unfold tailWord_1031265
  simp only [CollatzResearch.WordTrace]
  refine ⟨37613324608910505884999249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25075549739273670589999499 37613324608910505884999249)
  ·
    refine ⟨28209993456682879413749437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37613324608910505884999249 28209993456682879413749437)
    ·
      refine ⟨10578747546256079780156039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28209993456682879413749437 10578747546256079780156039)
      ·
        refine ⟨15868121319384119670234059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578747546256079780156039 15868121319384119670234059)
        ·
          refine ⟨23802181979076179505351089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15868121319384119670234059 23802181979076179505351089)
          ·
            refine ⟨17851636484307134629013317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23802181979076179505351089 17851636484307134629013317)
            ·
              refine ⟨3347181840807587742939997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17851636484307134629013317 3347181840807587742939997)
              ·
                refine ⟨1255193190302845403602499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3347181840807587742939997 1255193190302845403602499)
                ·
                  refine ⟨1882789785454268105403749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255193190302845403602499 1882789785454268105403749)
                  ·
                    refine ⟨353023084772675269763203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1882789785454268105403749 353023084772675269763203)
                    ·
                      rfl

theorem cell22_1031265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1031265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031265 prefixEnd_1031265 := by exact prefixLift 1031265
  have htrace : WordTrace (prefixWord ++ tailWord_1031265) baseStart_1031265 baseEnd_1031265 := by
    simpa [prefixWord, tailWord_1031265, baseEnd_1031265] using wordTrace_append hprefix tailTrace_1031265
  have hstable : (prefixWord ++ tailWord_1031265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031265).length < 2 ^ (prefixWord ++ tailWord_1031265).sum := by decide
  have hdescent : baseEnd_1031265 < baseStart_1031265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031417 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_1031417 : Nat := 118140960795 + 1031417 * 2 ^ 59
def prefixEnd_1031417 : Nat := 4983230072969 + 3 ^ 40 * 1031417 * 2
def baseEnd_1031417 : Nat := 353075117478997539962737

theorem tailTrace_1031417 : CollatzResearch.WordTrace tailWord_1031417 prefixEnd_1031417 353075117478997539962737 := by
  unfold tailWord_1031417
  simp only [CollatzResearch.WordTrace]
  refine ⟨37618868504359835844532505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25079245669573223896355003 37618868504359835844532505)
  ·
    refine ⟨28214151378269876883399379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37618868504359835844532505 28214151378269876883399379)
    ·
      refine ⟨42321227067404815325099069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28214151378269876883399379 42321227067404815325099069)
      ·
        refine ⟨15870460150276805746912151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42321227067404815325099069 15870460150276805746912151)
        ·
          refine ⟨23805690225415208620368227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870460150276805746912151 23805690225415208620368227)
          ·
            refine ⟨35708535338122812930552341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23805690225415208620368227 35708535338122812930552341)
            ·
              refine ⟨1673837593974506856119641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35708535338122812930552341 1673837593974506856119641)
              ·
                refine ⟨1255378195480880142089731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673837593974506856119641 1255378195480880142089731)
                ·
                  refine ⟨1883067293221320213134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255378195480880142089731 1883067293221320213134597)
                  ·
                    refine ⟨353075117478997539962737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883067293221320213134597 353075117478997539962737)
                    ·
                      rfl

theorem cell22_1031417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_1031417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031417 prefixEnd_1031417 := by exact prefixLift 1031417
  have htrace : WordTrace (prefixWord ++ tailWord_1031417) baseStart_1031417 baseEnd_1031417 := by
    simpa [prefixWord, tailWord_1031417, baseEnd_1031417] using wordTrace_append hprefix tailTrace_1031417
  have hstable : (prefixWord ++ tailWord_1031417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031417).length < 2 ^ (prefixWord ++ tailWord_1031417).sum := by decide
  have hdescent : baseEnd_1031417 < baseStart_1031417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031447 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 4, 3]
def baseStart_1031447 : Nat := 118140960795 + 1031447 * 2 ^ 59
def prefixEnd_1031447 : Nat := 4983230072969 + 3 ^ 40 * 1031447 * 2
def baseEnd_1031447 : Nat := 353085387092087461712645

theorem tailTrace_1031447 : CollatzResearch.WordTrace tailWord_1031447 prefixEnd_1031447 353085387092087461712645 := by
  unfold tailWord_1031447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37619962694251150968124595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25079975129500767312083063 37619962694251150968124595)
  ·
    refine ⟨56429944041376726452186893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37619962694251150968124595 56429944041376726452186893)
    ·
      refine ⟨21161229015516272419570085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56429944041376726452186893 21161229015516272419570085)
      ·
        refine ⟨3967730440409301078669391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21161229015516272419570085 3967730440409301078669391)
        ·
          refine ⟨5951595660613951618004087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967730440409301078669391 5951595660613951618004087)
          ·
            refine ⟨8927393490920927427006131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5951595660613951618004087 8927393490920927427006131)
            ·
              refine ⟨13391090236381391140509197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927393490920927427006131 13391090236381391140509197)
              ·
                refine ⟨5021658838643021677690949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13391090236381391140509197 5021658838643021677690949)
                ·
                  refine ⟨941561032245566564567053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5021658838643021677690949 941561032245566564567053)
                  ·
                    refine ⟨353085387092087461712645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 941561032245566564567053 353085387092087461712645)
                    ·
                      rfl

theorem cell22_1031447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_1031447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031447 prefixEnd_1031447 := by exact prefixLift 1031447
  have htrace : WordTrace (prefixWord ++ tailWord_1031447) baseStart_1031447 baseEnd_1031447 := by
    simpa [prefixWord, tailWord_1031447, baseEnd_1031447] using wordTrace_append hprefix tailTrace_1031447
  have hstable : (prefixWord ++ tailWord_1031447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031447).length < 2 ^ (prefixWord ++ tailWord_1031447).sum := by decide
  have hdescent : baseEnd_1031447 < baseStart_1031447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031494 : List Nat := [6, 1, 1, 3, 11]
def baseStart_1031494 : Nat := 118140960795 + 1031494 * 2 ^ 59
def prefixEnd_1031494 : Nat := 4983230072969 + 3 ^ 40 * 1031494 * 2
def baseEnd_1031494 : Nat := 1453092494455123480607

theorem tailTrace_1031494 : CollatzResearch.WordTrace tailWord_1031494 prefixEnd_1031494 1453092494455123480607 := by
  unfold tailWord_1031494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175677403908777437346423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25081117950053918663390357 1175677403908777437346423)
  ·
    refine ⟨1763516105863166156019635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175677403908777437346423 1763516105863166156019635)
    ·
      refine ⟨2645274158794749234029453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763516105863166156019635 2645274158794749234029453)
      ·
        refine ⟨991977809548030962761045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2645274158794749234029453 991977809548030962761045)
        ·
          refine ⟨1453092494455123480607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 991977809548030962761045 1453092494455123480607)
          ·
            rfl

theorem cell22_1031494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 11].length) (baseStart_1031494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031494 prefixEnd_1031494 := by exact prefixLift 1031494
  have htrace : WordTrace (prefixWord ++ tailWord_1031494) baseStart_1031494 baseEnd_1031494 := by
    simpa [prefixWord, tailWord_1031494, baseEnd_1031494] using wordTrace_append hprefix tailTrace_1031494
  have hstable : (prefixWord ++ tailWord_1031494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031494).length < 2 ^ (prefixWord ++ tailWord_1031494).sum := by decide
  have hdescent : baseEnd_1031494 < baseStart_1031494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031586 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1031586 : Nat := 118140960795 + 1031586 * 2 ^ 59
def prefixEnd_1031586 : Nat := 4983230072969 + 3 ^ 40 * 1031586 * 2
def baseEnd_1031586 : Nat := 353132969632737432487219

theorem tailTrace_1031586 : CollatzResearch.WordTrace tailWord_1031586 prefixEnd_1031586 353132969632737432487219 := by
  unfold tailWord_1031586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406258110186894426858653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25083354960498385138289741 9406258110186894426858653)
  ·
    refine ⟨3527346791320085410071995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9406258110186894426858653 3527346791320085410071995)
    ·
      refine ⟨5291020186980128115107993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527346791320085410071995 5291020186980128115107993)
      ·
        refine ⟨3968265140235096086330995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5291020186980128115107993 3968265140235096086330995)
        ·
          refine ⟨5952397710352644129496493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968265140235096086330995 5952397710352644129496493)
          ·
            refine ⟨2232149141382241548561185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5952397710352644129496493 2232149141382241548561185)
            ·
              refine ⟨1674111856036681161420889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232149141382241548561185 1674111856036681161420889)
              ·
                refine ⟨1255583892027510871065667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674111856036681161420889 1255583892027510871065667)
                ·
                  refine ⟨1883375838041266306598501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255583892027510871065667 1883375838041266306598501)
                  ·
                    refine ⟨353132969632737432487219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883375838041266306598501 353132969632737432487219)
                    ·
                      rfl

theorem cell22_1031586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1031586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031586 prefixEnd_1031586 := by exact prefixLift 1031586
  have htrace : WordTrace (prefixWord ++ tailWord_1031586) baseStart_1031586 baseEnd_1031586 := by
    simpa [prefixWord, tailWord_1031586, baseEnd_1031586] using wordTrace_append hprefix tailTrace_1031586
  have hstable : (prefixWord ++ tailWord_1031586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031586).length < 2 ^ (prefixWord ++ tailWord_1031586).sum := by decide
  have hdescent : baseEnd_1031586 < baseStart_1031586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031674 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_1031674 : Nat := 118140960795 + 1031674 * 2 ^ 59
def prefixEnd_1031674 : Nat := 4983230072969 + 3 ^ 40 * 1031674 * 2
def baseEnd_1031674 : Nat := 117721031277044845428983

theorem tailTrace_1031674 : CollatzResearch.WordTrace tailWord_1031674 prefixEnd_1031674 117721031277044845428983 := by
  unfold tailWord_1031674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407060516107192184159519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25085494709619179157758717 9407060516107192184159519)
  ·
    refine ⟨14110590774160788276239279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407060516107192184159519 14110590774160788276239279)
    ·
      refine ⟨21165886161241182414358919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14110590774160788276239279 21165886161241182414358919)
      ·
        refine ⟨31748829241861773621538379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21165886161241182414358919 31748829241861773621538379)
        ·
          refine ⟨47623243862792660432307569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31748829241861773621538379 47623243862792660432307569)
          ·
            refine ⟨35717432897094495324230677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47623243862792660432307569 35717432897094495324230677)
            ·
              refine ⟨1674254667051304468323313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35717432897094495324230677 1674254667051304468323313)
              ·
                refine ⟨1255691000288478351242485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674254667051304468323313 1255691000288478351242485)
                ·
                  refine ⟨117721031277044845428983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1255691000288478351242485 117721031277044845428983)
                  ·
                    rfl

theorem cell22_1031674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_1031674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031674 prefixEnd_1031674 := by exact prefixLift 1031674
  have htrace : WordTrace (prefixWord ++ tailWord_1031674) baseStart_1031674 baseEnd_1031674 := by
    simpa [prefixWord, tailWord_1031674, baseEnd_1031674] using wordTrace_append hprefix tailTrace_1031674
  have hstable : (prefixWord ++ tailWord_1031674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031674).length < 2 ^ (prefixWord ++ tailWord_1031674).sum := by decide
  have hdescent : baseEnd_1031674 < baseStart_1031674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031736 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_1031736 : Nat := 118140960795 + 1031736 * 2 ^ 59
def prefixEnd_1031736 : Nat := 4983230072969 + 3 ^ 40 * 1031736 * 2
def baseEnd_1031736 : Nat := 117728105899395680412253

theorem tailTrace_1031736 : CollatzResearch.WordTrace tailWord_1031736 prefixEnd_1031736 117728105899395680412253 := by
  unfold tailWord_1031736
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815251695102076662697531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25087002260136102216930041 18815251695102076662697531)
  ·
    refine ⟨28222877542653114994046297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18815251695102076662697531 28222877542653114994046297)
    ·
      refine ⟨21167158156989836245534723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28222877542653114994046297 21167158156989836245534723)
      ·
        refine ⟨31750737235484754368302085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167158156989836245534723 31750737235484754368302085)
        ·
          refine ⟨5953263231653391444056641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31750737235484754368302085 5953263231653391444056641)
          ·
            refine ⟨4464947423740043583042481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953263231653391444056641 4464947423740043583042481)
            ·
              refine ⟨3348710567805032687281861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464947423740043583042481 3348710567805032687281861)
              ·
                refine ⟨627883231463443628865349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3348710567805032687281861 627883231463443628865349)
                ·
                  refine ⟨117728105899395680412253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 627883231463443628865349 117728105899395680412253)
                  ·
                    rfl

theorem cell22_1031736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_1031736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031736 prefixEnd_1031736 := by exact prefixLift 1031736
  have htrace : WordTrace (prefixWord ++ tailWord_1031736) baseStart_1031736 baseEnd_1031736 := by
    simpa [prefixWord, tailWord_1031736, baseEnd_1031736] using wordTrace_append hprefix tailTrace_1031736
  have hstable : (prefixWord ++ tailWord_1031736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031736).length < 2 ^ (prefixWord ++ tailWord_1031736).sum := by decide
  have hdescent : baseEnd_1031736 < baseStart_1031736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031764 : List Nat := [2, 4, 1, 1, 1, 2, 3, 8]
def baseStart_1031764 : Nat := 118140960795 + 1031764 * 2 ^ 59
def prefixEnd_1031764 : Nat := 4983230072969 + 3 ^ 40 * 1031764 * 2
def baseEnd_1031764 : Nat := 39243766963378255726297

theorem tailTrace_1031764 : CollatzResearch.WordTrace tailWord_1031764 prefixEnd_1031764 39243766963378255726297 := by
  unfold tailWord_1031764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815762317051357053707173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25087683089401809404942897 18815762317051357053707173)
  ·
    refine ⟨3527955434447129447570095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18815762317051357053707173 3527955434447129447570095)
    ·
      refine ⟨5291933151670694171355143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527955434447129447570095 5291933151670694171355143)
      ·
        refine ⟨7937899727506041257032715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291933151670694171355143 7937899727506041257032715)
        ·
          refine ⟨11906849591259061885549073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7937899727506041257032715 11906849591259061885549073)
          ·
            refine ⟨8930137193444296414161805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11906849591259061885549073 8930137193444296414161805)
            ·
              refine ⟨3348801447541611155310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8930137193444296414161805 3348801447541611155310677)
              ·
                refine ⟨39243766963378255726297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3348801447541611155310677 39243766963378255726297)
                ·
                  rfl

theorem cell22_1031764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_1031764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031764 prefixEnd_1031764 := by exact prefixLift 1031764
  have htrace : WordTrace (prefixWord ++ tailWord_1031764) baseStart_1031764 baseEnd_1031764 := by
    simpa [prefixWord, tailWord_1031764, baseEnd_1031764] using wordTrace_append hprefix tailTrace_1031764
  have hstable : (prefixWord ++ tailWord_1031764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031764).length < 2 ^ (prefixWord ++ tailWord_1031764).sum := by decide
  have hdescent : baseEnd_1031764 < baseStart_1031764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031886 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1031886 : Nat := 118140960795 + 1031886 * 2 ^ 59
def prefixEnd_1031886 : Nat := 4983230072969 + 3 ^ 40 * 1031886 * 2
def baseEnd_1031886 : Nat := 353235665763636649986299

theorem tailTrace_1031886 : CollatzResearch.WordTrace tailWord_1031886 prefixEnd_1031886 353235665763636649986299 := by
  unfold tailWord_1031886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704496792457591117919439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25090649559773819295570341 4704496792457591117919439)
  ·
    refine ⟨7056745188686386676879159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4704496792457591117919439 7056745188686386676879159)
    ·
      refine ⟨10585117783029580015318739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056745188686386676879159 10585117783029580015318739)
      ·
        refine ⟨15877676674544370022978109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10585117783029580015318739 15877676674544370022978109)
        ·
          refine ⟨5954128752954138758616791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15877676674544370022978109 5954128752954138758616791)
          ·
            refine ⟨8931193129431208137925187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954128752954138758616791 8931193129431208137925187)
            ·
              refine ⟨13396789694146812206887781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931193129431208137925187 13396789694146812206887781)
              ·
                refine ⟨2511898067652527288791459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13396789694146812206887781 2511898067652527288791459)
                ·
                  refine ⟨3767847101478790933187189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511898067652527288791459 3767847101478790933187189)
                  ·
                    refine ⟨353235665763636649986299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3767847101478790933187189 353235665763636649986299)
                    ·
                      rfl

theorem cell22_1031886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1031886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031886 prefixEnd_1031886 := by exact prefixLift 1031886
  have htrace : WordTrace (prefixWord ++ tailWord_1031886) baseStart_1031886 baseEnd_1031886 := by
    simpa [prefixWord, tailWord_1031886, baseEnd_1031886] using wordTrace_append hprefix tailTrace_1031886
  have hstable : (prefixWord ++ tailWord_1031886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031886).length < 2 ^ (prefixWord ++ tailWord_1031886).sum := by decide
  have hdescent : baseEnd_1031886 < baseStart_1031886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031890 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1031890 : Nat := 118140960795 + 1031890 * 2 ^ 59
def prefixEnd_1031890 : Nat := 4983230072969 + 3 ^ 40 * 1031890 * 2
def baseEnd_1031890 : Nat := 353237035045381972886287

theorem tailTrace_1031890 : CollatzResearch.WordTrace tailWord_1031890 prefixEnd_1031890 353237035045381972886287 := by
  unfold tailWord_1031890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409030057911559406625281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25090746821097491751000749 9409030057911559406625281)
  ·
    refine ⟨7056772543433669554968961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9409030057911559406625281 7056772543433669554968961)
    ·
      refine ⟨5292579407575252166226721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7056772543433669554968961 5292579407575252166226721)
      ·
        refine ⟨3969434555681439124670041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5292579407575252166226721 3969434555681439124670041)
        ·
          refine ⟨2977075916761079343502531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3969434555681439124670041 2977075916761079343502531)
          ·
            refine ⟨4465613875141619015253797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977075916761079343502531 4465613875141619015253797)
            ·
              refine ⟨837302601589053565360087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4465613875141619015253797 837302601589053565360087)
              ·
                refine ⟨1255953902383580348040131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837302601589053565360087 1255953902383580348040131)
                ·
                  refine ⟨1883930853575370522060197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255953902383580348040131 1883930853575370522060197)
                  ·
                    refine ⟨353237035045381972886287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1883930853575370522060197 353237035045381972886287)
                    ·
                      rfl

theorem cell22_1031890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1031890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031890 prefixEnd_1031890 := by exact prefixLift 1031890
  have htrace : WordTrace (prefixWord ++ tailWord_1031890) baseStart_1031890 baseEnd_1031890 := by
    simpa [prefixWord, tailWord_1031890, baseEnd_1031890] using wordTrace_append hprefix tailTrace_1031890
  have hstable : (prefixWord ++ tailWord_1031890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031890).length < 2 ^ (prefixWord ++ tailWord_1031890).sum := by decide
  have hdescent : baseEnd_1031890 < baseStart_1031890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031894 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1031894 : Nat := 118140960795 + 1031894 * 2 ^ 59
def prefixEnd_1031894 : Nat := 4983230072969 + 3 ^ 40 * 1031894 * 2
def baseEnd_1031894 : Nat := 117746134775709098595425

theorem tailTrace_1031894 : CollatzResearch.WordTrace tailWord_1031894 prefixEnd_1031894 117746134775709098595425 := by
  unfold tailWord_1031894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352266632726984144352921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25090844082421164206431157 2352266632726984144352921)
  ·
    refine ⟨1764199974545238108264691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2352266632726984144352921 1764199974545238108264691)
    ·
      refine ⟨2646299961817857162397037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764199974545238108264691 2646299961817857162397037)
      ·
        refine ⟨992362485681696435898889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2646299961817857162397037 992362485681696435898889)
        ·
          refine ⟨744271864261272326924167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992362485681696435898889 744271864261272326924167)
          ·
            refine ⟨1116407796391908490386251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744271864261272326924167 1116407796391908490386251)
            ·
              refine ⟨1674611694587862735579377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116407796391908490386251 1674611694587862735579377)
              ·
                refine ⟨1255958770940897051684533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674611694587862735579377 1255958770940897051684533)
                ·
                  refine ⟨117746134775709098595425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1255958770940897051684533 117746134775709098595425)
                  ·
                    rfl

theorem cell22_1031894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1031894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031894 prefixEnd_1031894 := by exact prefixLift 1031894
  have htrace : WordTrace (prefixWord ++ tailWord_1031894) baseStart_1031894 baseEnd_1031894 := by
    simpa [prefixWord, tailWord_1031894, baseEnd_1031894] using wordTrace_append hprefix tailTrace_1031894
  have hstable : (prefixWord ++ tailWord_1031894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031894).length < 2 ^ (prefixWord ++ tailWord_1031894).sum := by decide
  have hdescent : baseEnd_1031894 < baseStart_1031894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031931 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 5, 3]
def baseStart_1031931 : Nat := 118140960795 + 1031931 * 2 ^ 59
def prefixEnd_1031931 : Nat := 4983230072969 + 3 ^ 40 * 1031931 * 2
def baseEnd_1031931 : Nat := 353251070183271532611161

theorem tailTrace_1031931 : CollatzResearch.WordTrace tailWord_1031931 prefixEnd_1031931 353251070183271532611161 := by
  unfold tailWord_1031931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637615624497701628743647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25091743749665134419162431 37637615624497701628743647)
  ·
    refine ⟨56456423436746552443115471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637615624497701628743647 56456423436746552443115471)
    ·
      refine ⟨84684635155119828664673207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56456423436746552443115471 84684635155119828664673207)
      ·
        refine ⟨127026952732679742997009811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84684635155119828664673207 127026952732679742997009811)
        ·
          refine ⟨190540429099019614495514717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127026952732679742997009811 190540429099019614495514717)
          ·
            refine ⟨71452660912132355435818019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190540429099019614495514717 71452660912132355435818019)
            ·
              refine ⟨107178991368198533153727029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71452660912132355435818019 107178991368198533153727029)
              ·
                refine ⟨10048030440768612483161909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107178991368198533153727029 10048030440768612483161909)
                ·
                  refine ⟨942002853822057420296429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10048030440768612483161909 942002853822057420296429)
                  ·
                    refine ⟨353251070183271532611161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942002853822057420296429 353251070183271532611161)
                    ·
                      rfl

theorem cell22_1031931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3].length) (baseStart_1031931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031931 prefixEnd_1031931 := by exact prefixLift 1031931
  have htrace : WordTrace (prefixWord ++ tailWord_1031931) baseStart_1031931 baseEnd_1031931 := by
    simpa [prefixWord, tailWord_1031931, baseEnd_1031931] using wordTrace_append hprefix tailTrace_1031931
  have hstable : (prefixWord ++ tailWord_1031931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031931).length < 2 ^ (prefixWord ++ tailWord_1031931).sum := by decide
  have hdescent : baseEnd_1031931 < baseStart_1031931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031956 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1031956 : Nat := 118140960795 + 1031956 * 2 ^ 59
def prefixEnd_1031956 : Nat := 4983230072969 + 3 ^ 40 * 1031956 * 2
def baseEnd_1031956 : Nat := 117753209398059933578695

theorem tailTrace_1031956 : CollatzResearch.WordTrace tailWord_1031956 prefixEnd_1031956 117753209398059933578695 := by
  unfold tailWord_1031956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819263724703565449201861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25092351632938087265602481 18819263724703565449201861)
  ·
    refine ⟨3528611948381918521725349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18819263724703565449201861 3528611948381918521725349)
    ·
      refine ⟨661614740321609722823503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3528611948381918521725349 661614740321609722823503)
      ·
        refine ⟨992422110482414584235255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661614740321609722823503 992422110482414584235255)
        ·
          refine ⟨1488633165723621876352883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992422110482414584235255 1488633165723621876352883)
          ·
            refine ⟨2232949748585432814529325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488633165723621876352883 2232949748585432814529325)
            ·
              refine ⟨837356155719537305448497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232949748585432814529325 837356155719537305448497)
              ·
                refine ⟨628017116789652979086373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837356155719537305448497 628017116789652979086373)
                ·
                  refine ⟨117753209398059933578695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628017116789652979086373 117753209398059933578695)
                  ·
                    rfl

theorem cell22_1031956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1031956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1031956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1031956 prefixEnd_1031956 := by exact prefixLift 1031956
  have htrace : WordTrace (prefixWord ++ tailWord_1031956) baseStart_1031956 baseEnd_1031956 := by
    simpa [prefixWord, tailWord_1031956, baseEnd_1031956] using wordTrace_append hprefix tailTrace_1031956
  have hstable : (prefixWord ++ tailWord_1031956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031956).length < 2 ^ (prefixWord ++ tailWord_1031956).sum := by decide
  have hdescent : baseEnd_1031956 < baseStart_1031956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032053 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1032053 : Nat := 118140960795 + 1032053 * 2 ^ 59
def prefixEnd_1032053 : Nat := 4983230072969 + 3 ^ 40 * 1032053 * 2
def baseEnd_1032053 : Nat := 353292833276503881060787

theorem tailTrace_1032053 : CollatzResearch.WordTrace tailWord_1032053 prefixEnd_1032053 353292833276503881060787 := by
  unfold tailWord_1032053
  simp only [CollatzResearch.WordTrace]
  refine ⟨37642065330055716464684813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25094710220037144309789875 37642065330055716464684813)
  ·
    refine ⟨14115774498770893674256805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37642065330055716464684813 14115774498770893674256805)
    ·
      refine ⟨2646707718519542563923151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14115774498770893674256805 2646707718519542563923151)
      ·
        refine ⟨3970061577779313845884727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646707718519542563923151 3970061577779313845884727)
        ·
          refine ⟨5955092366668970768827091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970061577779313845884727 5955092366668970768827091)
          ·
            refine ⟨8932638550003456153240637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5955092366668970768827091 8932638550003456153240637)
            ·
              refine ⟨3349739456251296057465239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8932638550003456153240637 3349739456251296057465239)
              ·
                refine ⟨5024609184376944086197859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349739456251296057465239 5024609184376944086197859)
                ·
                  refine ⟨7536913776565416129296789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024609184376944086197859 7536913776565416129296789)
                  ·
                    refine ⟨353292833276503881060787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7536913776565416129296789 353292833276503881060787)
                    ·
                      rfl

theorem cell22_1032053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1032053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032053 prefixEnd_1032053 := by exact prefixLift 1032053
  have htrace : WordTrace (prefixWord ++ tailWord_1032053) baseStart_1032053 baseEnd_1032053 := by
    simpa [prefixWord, tailWord_1032053, baseEnd_1032053] using wordTrace_append hprefix tailTrace_1032053
  have hstable : (prefixWord ++ tailWord_1032053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032053).length < 2 ^ (prefixWord ++ tailWord_1032053).sum := by decide
  have hdescent : baseEnd_1032053 < baseStart_1032053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032081 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1032081 : Nat := 118140960795 + 1032081 * 2 ^ 59
def prefixEnd_1032081 : Nat := 4983230072969 + 3 ^ 40 * 1032081 * 2
def baseEnd_1032081 : Nat := 353302418248721141360701

theorem tailTrace_1032081 : CollatzResearch.WordTrace tailWord_1032081 prefixEnd_1032081 353302418248721141360701 := by
  unfold tailWord_1032081
  simp only [CollatzResearch.WordTrace]
  refine ⟨37643086573954277246704097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25095391049302851497802731 37643086573954277246704097)
  ·
    refine ⟨28232314930465707935028073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37643086573954277246704097 28232314930465707935028073)
    ·
      refine ⟨21174236197849280951271055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28232314930465707935028073 21174236197849280951271055)
      ·
        refine ⟨31761354296773921426906583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21174236197849280951271055 31761354296773921426906583)
        ·
          refine ⟨47642031445160882140359875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31761354296773921426906583 47642031445160882140359875)
          ·
            refine ⟨71463047167741323210539813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47642031445160882140359875 71463047167741323210539813)
            ·
              refine ⟨13399321343951498101976215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71463047167741323210539813 13399321343951498101976215)
              ·
                refine ⟨20098982015927247152964323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13399321343951498101976215 20098982015927247152964323)
                ·
                  refine ⟨30148473023890870729446485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20098982015927247152964323 30148473023890870729446485)
                  ·
                    refine ⟨353302418248721141360701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30148473023890870729446485 353302418248721141360701)
                    ·
                      rfl

theorem cell22_1032081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1032081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032081 prefixEnd_1032081 := by exact prefixLift 1032081
  have htrace : WordTrace (prefixWord ++ tailWord_1032081) baseStart_1032081 baseEnd_1032081 := by
    simpa [prefixWord, tailWord_1032081, baseEnd_1032081] using wordTrace_append hprefix tailTrace_1032081
  have hstable : (prefixWord ++ tailWord_1032081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032081).length < 2 ^ (prefixWord ++ tailWord_1032081).sum := by decide
  have hdescent : baseEnd_1032081 < baseStart_1032081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032100 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_1032100 : Nat := 118140960795 + 1032100 * 2 ^ 59
def prefixEnd_1032100 : Nat := 4983230072969 + 3 ^ 40 * 1032100 * 2
def baseEnd_1032100 : Nat := 353308922337011425135643

theorem tailTrace_1032100 : CollatzResearch.WordTrace tailWord_1032100 prefixEnd_1032100 353308922337011425135643 := by
  unfold tailWord_1032100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18821889780442721745822877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25095853040590295661097169 18821889780442721745822877)
  ·
    refine ⟨7058208667666020654683579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18821889780442721745822877 7058208667666020654683579)
    ·
      refine ⟨10587313001499030982025369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058208667666020654683579 10587313001499030982025369)
      ·
        refine ⟨7940484751124273236519027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10587313001499030982025369 7940484751124273236519027)
        ·
          refine ⟨11910727126686409854778541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940484751124273236519027 11910727126686409854778541)
          ·
            refine ⟨4466522672507403695541953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11910727126686409854778541 4466522672507403695541953)
            ·
              refine ⟨3349892004380552771656465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466522672507403695541953 3349892004380552771656465)
              ·
                refine ⟨2512419003285414578742349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349892004380552771656465 2512419003285414578742349)
                ·
                  refine ⟨942157126232030467028381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2512419003285414578742349 942157126232030467028381)
                  ·
                    refine ⟨353308922337011425135643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942157126232030467028381 353308922337011425135643)
                    ·
                      rfl

theorem cell22_1032100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_1032100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032100 prefixEnd_1032100 := by exact prefixLift 1032100
  have htrace : WordTrace (prefixWord ++ tailWord_1032100) baseStart_1032100 baseEnd_1032100 := by
    simpa [prefixWord, tailWord_1032100, baseEnd_1032100] using wordTrace_append hprefix tailTrace_1032100
  have hstable : (prefixWord ++ tailWord_1032100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032100).length < 2 ^ (prefixWord ++ tailWord_1032100).sum := by decide
  have hdescent : baseEnd_1032100 < baseStart_1032100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032113 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 7]
def baseStart_1032113 : Nat := 118140960795 + 1032113 * 2 ^ 59
def prefixEnd_1032113 : Nat := 4983230072969 + 3 ^ 40 * 1032113 * 2
def baseEnd_1032113 : Nat := 117771124167561241520201

theorem tailTrace_1032113 : CollatzResearch.WordTrace tailWord_1032113 prefixEnd_1032113 117771124167561241520201 := by
  unfold tailWord_1032113
  simp only [CollatzResearch.WordTrace]
  refine ⟨37644253709838346711868993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25096169139892231141245995 37644253709838346711868993)
  ·
    refine ⟨28233190282378760033901745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37644253709838346711868993 28233190282378760033901745)
    ·
      refine ⟨21174892711784070025426309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28233190282378760033901745 21174892711784070025426309)
      ·
        refine ⟨3970292383459513129767433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21174892711784070025426309 3970292383459513129767433)
        ·
          refine ⟨2977719287594634847325575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3970292383459513129767433 2977719287594634847325575)
          ·
            refine ⟨4466578931391952270988363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977719287594634847325575 4466578931391952270988363)
            ·
              refine ⟨6699868397087928406482545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466578931391952270988363 6699868397087928406482545)
              ·
                refine ⟨5024901297815946304861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6699868397087928406482545 5024901297815946304861909)
                ·
                  refine ⟨117771124167561241520201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5024901297815946304861909 117771124167561241520201)
                  ·
                    rfl

theorem cell22_1032113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_1032113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032113 prefixEnd_1032113 := by exact prefixLift 1032113
  have htrace : WordTrace (prefixWord ++ tailWord_1032113) baseStart_1032113 baseEnd_1032113 := by
    simpa [prefixWord, tailWord_1032113, baseEnd_1032113] using wordTrace_append hprefix tailTrace_1032113
  have hstable : (prefixWord ++ tailWord_1032113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032113).length < 2 ^ (prefixWord ++ tailWord_1032113).sum := by decide
  have hdescent : baseEnd_1032113 < baseStart_1032113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032143 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_1032143 : Nat := 118140960795 + 1032143 * 2 ^ 59
def prefixEnd_1032143 : Nat := 4983230072969 + 3 ^ 40 * 1032143 * 2
def baseEnd_1032143 : Nat := 353323642115773646310511

theorem tailTrace_1032143 : CollatzResearch.WordTrace tailWord_1032143 prefixEnd_1032143 353323642115773646310511 := by
  unfold tailWord_1032143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37645347899729661835461083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25096898599819774556974055 37645347899729661835461083)
  ·
    refine ⟨56468021849594492753191625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37645347899729661835461083 56468021849594492753191625)
    ·
      refine ⟨42351016387195869564893719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56468021849594492753191625 42351016387195869564893719)
      ·
        refine ⟨63526524580793804347340579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42351016387195869564893719 63526524580793804347340579)
        ·
          refine ⟨95289786871190706521010869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63526524580793804347340579 95289786871190706521010869)
          ·
            refine ⟨8933417519174128736344769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95289786871190706521010869 8933417519174128736344769)
            ·
              refine ⟨6700063139380596552258577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8933417519174128736344769 6700063139380596552258577)
              ·
                refine ⟨5025047354535447414193933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700063139380596552258577 5025047354535447414193933)
                ·
                  refine ⟨1884392757950792780322725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5025047354535447414193933 1884392757950792780322725)
                  ·
                    refine ⟨353323642115773646310511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1884392757950792780322725 353323642115773646310511)
                    ·
                      rfl

theorem cell22_1032143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_1032143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032143 prefixEnd_1032143 := by exact prefixLift 1032143
  have htrace : WordTrace (prefixWord ++ tailWord_1032143) baseStart_1032143 baseEnd_1032143 := by
    simpa [prefixWord, tailWord_1032143, baseEnd_1032143] using wordTrace_append hprefix tailTrace_1032143
  have hstable : (prefixWord ++ tailWord_1032143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032143).length < 2 ^ (prefixWord ++ tailWord_1032143).sum := by decide
  have hdescent : baseEnd_1032143 < baseStart_1032143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032175 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 4]
def baseStart_1032175 : Nat := 118140960795 + 1032175 * 2 ^ 59
def prefixEnd_1032175 : Nat := 4983230072969 + 3 ^ 40 * 1032175 * 2
def baseEnd_1032175 : Nat := 117778198789912076503471

theorem tailTrace_1032175 : CollatzResearch.WordTrace tailWord_1032175 prefixEnd_1032175 117778198789912076503471 := by
  unfold tailWord_1032175
  simp only [CollatzResearch.WordTrace]
  refine ⟨37646515035613731300625979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25097676690409154200417319 37646515035613731300625979)
  ·
    refine ⟨56469772553420596950938969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37646515035613731300625979 56469772553420596950938969)
    ·
      refine ⟨42352329415065447713204227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56469772553420596950938969 42352329415065447713204227)
      ·
        refine ⟨63528494122598171569806341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42352329415065447713204227 63528494122598171569806341)
        ·
          refine ⟨11911592647987157169338689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63528494122598171569806341 11911592647987157169338689)
          ·
            refine ⟨8933694485990367877004017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11911592647987157169338689 8933694485990367877004017)
            ·
              refine ⟨6700270864492775907753013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8933694485990367877004017 6700270864492775907753013)
              ·
                refine ⟨628150393546197741351845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6700270864492775907753013 628150393546197741351845)
                ·
                  refine ⟨117778198789912076503471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628150393546197741351845 117778198789912076503471)
                  ·
                    rfl

theorem cell22_1032175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 4].length) (baseStart_1032175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032175 prefixEnd_1032175 := by exact prefixLift 1032175
  have htrace : WordTrace (prefixWord ++ tailWord_1032175) baseStart_1032175 baseEnd_1032175 := by
    simpa [prefixWord, tailWord_1032175, baseEnd_1032175] using wordTrace_append hprefix tailTrace_1032175
  have hstable : (prefixWord ++ tailWord_1032175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032175).length < 2 ^ (prefixWord ++ tailWord_1032175).sum := by decide
  have hdescent : baseEnd_1032175 < baseStart_1032175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032252 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1032252 : Nat := 118140960795 + 1032252 * 2 ^ 59
def prefixEnd_1032252 : Nat := 4983230072969 + 3 ^ 40 * 1032252 * 2
def baseEnd_1032252 : Nat := 353360955043333695335177

theorem tailTrace_1032252 : CollatzResearch.WordTrace tailWord_1032252 prefixEnd_1032252 353360955043333695335177 := by
  unfold tailWord_1032252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824661728167386725589505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25099548970889848967452673 18824661728167386725589505)
  ·
    refine ⟨14118496296125540044192129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18824661728167386725589505 14118496296125540044192129)
    ·
      refine ⟨10588872222094155033144097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14118496296125540044192129 10588872222094155033144097)
      ·
        refine ⟨7941654166570616274858073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10588872222094155033144097 7941654166570616274858073)
        ·
          refine ⟨5956240624927962206143555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7941654166570616274858073 5956240624927962206143555)
          ·
            refine ⟨8934360937391943309215333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956240624927962206143555 8934360937391943309215333)
            ·
              refine ⟨1675192675760989370477875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8934360937391943309215333 1675192675760989370477875)
              ·
                refine ⟨2512789013641484055716813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675192675760989370477875 2512789013641484055716813)
                ·
                  refine ⟨942295880115556520893805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2512789013641484055716813 942295880115556520893805)
                  ·
                    refine ⟨353360955043333695335177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942295880115556520893805 353360955043333695335177)
                    ·
                      rfl

theorem cell22_1032252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1032252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032252 prefixEnd_1032252 := by exact prefixLift 1032252
  have htrace : WordTrace (prefixWord ++ tailWord_1032252) baseStart_1032252 baseEnd_1032252 := by
    simpa [prefixWord, tailWord_1032252, baseEnd_1032252] using wordTrace_append hprefix tailTrace_1032252
  have hstable : (prefixWord ++ tailWord_1032252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032252).length < 2 ^ (prefixWord ++ tailWord_1032252).sum := by decide
  have hdescent : baseEnd_1032252 < baseStart_1032252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032346 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_1032346 : Nat := 118140960795 + 1032346 * 2 ^ 59
def prefixEnd_1032346 : Nat := 4983230072969 + 3 ^ 40 * 1032346 * 2
def baseEnd_1032346 : Nat := 353393133164348783484889

theorem tailTrace_1032346 : CollatzResearch.WordTrace tailWord_1032346 prefixEnd_1032346 353393133164348783484889 := by
  unfold tailWord_1032346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413187979498556876275223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25101834611996151670067261 9413187979498556876275223)
  ·
    refine ⟨14119781969247835314412835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9413187979498556876275223 14119781969247835314412835)
    ·
      refine ⟨21179672953871752971619253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14119781969247835314412835 21179672953871752971619253)
      ·
        refine ⟨1985594339425476841089305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21179672953871752971619253 1985594339425476841089305)
        ·
          refine ⟨1489195754569107630816979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985594339425476841089305 1489195754569107630816979)
          ·
            refine ⟨2233793631853661446225469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489195754569107630816979 2233793631853661446225469)
            ·
              refine ⟨837672611945123042334551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233793631853661446225469 837672611945123042334551)
              ·
                refine ⟨1256508917917684563501827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837672611945123042334551 1256508917917684563501827)
                ·
                  refine ⟨1884763376876526845252741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256508917917684563501827 1884763376876526845252741)
                  ·
                    refine ⟨353393133164348783484889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1884763376876526845252741 353393133164348783484889)
                    ·
                      rfl

theorem cell22_1032346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_1032346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032346 prefixEnd_1032346 := by exact prefixLift 1032346
  have htrace : WordTrace (prefixWord ++ tailWord_1032346) baseStart_1032346 baseEnd_1032346 := by
    simpa [prefixWord, tailWord_1032346, baseEnd_1032346] using wordTrace_append hprefix tailTrace_1032346
  have hstable : (prefixWord ++ tailWord_1032346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032346).length < 2 ^ (prefixWord ++ tailWord_1032346).sum := by decide
  have hdescent : baseEnd_1032346 < baseStart_1032346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032421 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_1032421 : Nat := 118140960795 + 1032421 * 2 ^ 59
def prefixEnd_1032421 : Nat := 4983230072969 + 3 ^ 40 * 1032421 * 2
def baseEnd_1032421 : Nat := 353418807197073587859659

theorem tailTrace_1032421 : CollatzResearch.WordTrace tailWord_1032421 prefixEnd_1032421 353418807197073587859659 := by
  unfold tailWord_1032421
  simp only [CollatzResearch.WordTrace]
  refine ⟨37655487392722515314081117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25103658261815010209387411 37655487392722515314081117)
  ·
    refine ⟨14120807772270943242780419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37655487392722515314081117 14120807772270943242780419)
    ·
      refine ⟨21181211658406414864170629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120807772270943242780419 21181211658406414864170629)
      ·
        refine ⟨3971477185951202787031993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21181211658406414864170629 3971477185951202787031993)
        ·
          refine ⟨2978607889463402090273995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3971477185951202787031993 2978607889463402090273995)
          ·
            refine ⟨4467911834195103135410993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978607889463402090273995 4467911834195103135410993)
            ·
              refine ⟨3350933875646327351558245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467911834195103135410993 3350933875646327351558245)
              ·
                refine ⟨628300101683686378417171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3350933875646327351558245 628300101683686378417171)
                ·
                  refine ⟨942450152525529567625757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628300101683686378417171 942450152525529567625757)
                  ·
                    refine ⟨353418807197073587859659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942450152525529567625757 353418807197073587859659)
                    ·
                      rfl

theorem cell22_1032421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_1032421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032421 prefixEnd_1032421 := by exact prefixLift 1032421
  have htrace : WordTrace (prefixWord ++ tailWord_1032421) baseStart_1032421 baseEnd_1032421 := by
    simpa [prefixWord, tailWord_1032421, baseEnd_1032421] using wordTrace_append hprefix tailTrace_1032421
  have hstable : (prefixWord ++ tailWord_1032421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032421).length < 2 ^ (prefixWord ++ tailWord_1032421).sum := by decide
  have hdescent : baseEnd_1032421 < baseStart_1032421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032455 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1032455 : Nat := 118140960795 + 1032455 * 2 ^ 59
def prefixEnd_1032455 : Nat := 4983230072969 + 3 ^ 40 * 1032455 * 2
def baseEnd_1032455 : Nat := 353430446091908832509555

theorem tailTrace_1032455 : CollatzResearch.WordTrace tailWord_1032455 prefixEnd_1032455 353430446091908832509555 := by
  unfold tailWord_1032455
  simp only [CollatzResearch.WordTrace]
  refine ⟨37656727474599339120818819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25104484983066226080545879 37656727474599339120818819)
  ·
    refine ⟨56485091211899008681228229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37656727474599339120818819 56485091211899008681228229)
    ·
      refine ⟨10590954602231064127730293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56485091211899008681228229 10590954602231064127730293)
      ·
        refine ⟨992901993959162261974715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10590954602231064127730293 992901993959162261974715)
        ·
          refine ⟨1489352990938743392962073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992901993959162261974715 1489352990938743392962073)
          ·
            refine ⟨1117014743204057544721555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489352990938743392962073 1117014743204057544721555)
            ·
              refine ⟨1675522114806086317082333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117014743204057544721555 1675522114806086317082333)
              ·
                refine ⟨628320793052282368905875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1675522114806086317082333 628320793052282368905875)
                ·
                  refine ⟨942481189578423553358813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628320793052282368905875 942481189578423553358813)
                  ·
                    refine ⟨353430446091908832509555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942481189578423553358813 353430446091908832509555)
                    ·
                      rfl

theorem cell22_1032455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1032455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032455 prefixEnd_1032455 := by exact prefixLift 1032455
  have htrace : WordTrace (prefixWord ++ tailWord_1032455) baseStart_1032455 baseEnd_1032455 := by
    simpa [prefixWord, tailWord_1032455, baseEnd_1032455] using wordTrace_append hprefix tailTrace_1032455
  have hstable : (prefixWord ++ tailWord_1032455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032455).length < 2 ^ (prefixWord ++ tailWord_1032455).sum := by decide
  have hdescent : baseEnd_1032455 < baseStart_1032455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032479 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 6]
def baseStart_1032479 : Nat := 118140960795 + 1032479 * 2 ^ 59
def prefixEnd_1032479 : Nat := 4983230072969 + 3 ^ 40 * 1032479 * 2
def baseEnd_1032479 : Nat := 117812887260793589969827

theorem tailTrace_1032479 : CollatzResearch.WordTrace tailWord_1032479 prefixEnd_1032479 117812887260793589969827 := by
  unfold tailWord_1032479
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657602826512391219692491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25105068551008260813128327 37657602826512391219692491)
  ·
    refine ⟨56486404239768586829538737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37657602826512391219692491 56486404239768586829538737)
    ·
      refine ⟨42364803179826440122154053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56486404239768586829538737 42364803179826440122154053)
      ·
        refine ⟨7943400596217457522903885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42364803179826440122154053 7943400596217457522903885)
        ·
          refine ⟨2978775223581546571088957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7943400596217457522903885 2978775223581546571088957)
          ·
            refine ⟨1117040708843079964158359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2978775223581546571088957 1117040708843079964158359)
            ·
              refine ⟨1675561063264619946237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117040708843079964158359 1675561063264619946237539)
              ·
                refine ⟨2513341594896929919356309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675561063264619946237539 2513341594896929919356309)
                ·
                  refine ⟨117812887260793589969827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2513341594896929919356309 117812887260793589969827)
                  ·
                    rfl

theorem cell22_1032479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 6].length) (baseStart_1032479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032479 prefixEnd_1032479 := by exact prefixLift 1032479
  have htrace : WordTrace (prefixWord ++ tailWord_1032479) baseStart_1032479 baseEnd_1032479 := by
    simpa [prefixWord, tailWord_1032479, baseEnd_1032479] using wordTrace_append hprefix tailTrace_1032479
  have hstable : (prefixWord ++ tailWord_1032479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032479).length < 2 ^ (prefixWord ++ tailWord_1032479).sum := by decide
  have hdescent : baseEnd_1032479 < baseStart_1032479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032498 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_1032498 : Nat := 118140960795 + 1032498 * 2 ^ 59
def prefixEnd_1032498 : Nat := 4983230072969 + 3 ^ 40 * 1032498 * 2
def baseEnd_1032498 : Nat := 353445165870671053684423

theorem tailTrace_1032498 : CollatzResearch.WordTrace tailWord_1032498 prefixEnd_1032498 353445165870671053684423 := by
  unfold tailWord_1032498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414573953360889366158537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25105530542295704976422765 9414573953360889366158537)
  ·
    refine ⟨7060930465020667024618903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9414573953360889366158537 7060930465020667024618903)
    ·
      refine ⟨10591395697531000536928355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060930465020667024618903 10591395697531000536928355)
      ·
        refine ⟨15887093546296500805392533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10591395697531000536928355 15887093546296500805392533)
        ·
          refine ⟨744707509982648475252775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15887093546296500805392533 744707509982648475252775)
          ·
            refine ⟨1117061264973972712879163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744707509982648475252775 1117061264973972712879163)
            ·
              refine ⟨1675591897460959069318745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117061264973972712879163 1675591897460959069318745)
              ·
                refine ⟨1256693923095719301989059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675591897460959069318745 1256693923095719301989059)
                ·
                  refine ⟨1885040884643578952983589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256693923095719301989059 1885040884643578952983589)
                  ·
                    refine ⟨353445165870671053684423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885040884643578952983589 353445165870671053684423)
                    ·
                      rfl

theorem cell22_1032498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_1032498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032498 prefixEnd_1032498 := by exact prefixLift 1032498
  have htrace : WordTrace (prefixWord ++ tailWord_1032498) baseStart_1032498 baseEnd_1032498 := by
    simpa [prefixWord, tailWord_1032498, baseEnd_1032498] using wordTrace_append hprefix tailTrace_1032498
  have hstable : (prefixWord ++ tailWord_1032498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032498).length < 2 ^ (prefixWord ++ tailWord_1032498).sum := by decide
  have hdescent : baseEnd_1032498 < baseStart_1032498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032556 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_1032556 : Nat := 118140960795 + 1032556 * 2 ^ 59
def prefixEnd_1032556 : Nat := 4983230072969 + 3 ^ 40 * 1032556 * 2
def baseEnd_1032556 : Nat := 353465020455978235734245

theorem tailTrace_1032556 : CollatzResearch.WordTrace tailWord_1032556 prefixEnd_1032556 353465020455978235734245 := by
  unfold tailWord_1032556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18830205623616716685122761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25106940831488955580163681 18830205623616716685122761)
  ·
    refine ⟨14122654217712537513842071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18830205623616716685122761 14122654217712537513842071)
    ·
      refine ⟨21183981326568806270763107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122654217712537513842071 21183981326568806270763107)
      ·
        refine ⟨31775971989853209406144661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21183981326568806270763107 31775971989853209406144661)
        ·
          refine ⟨1489498687024369190913031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31775971989853209406144661 1489498687024369190913031)
          ·
            refine ⟨2234248030536553786369547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489498687024369190913031 2234248030536553786369547)
            ·
              refine ⟨3351372045804830679554321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234248030536553786369547 3351372045804830679554321)
              ·
                refine ⟨2513529034353623009665741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351372045804830679554321 2513529034353623009665741)
                ·
                  refine ⟨942573387882608628624653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2513529034353623009665741 942573387882608628624653)
                  ·
                    refine ⟨353465020455978235734245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942573387882608628624653 353465020455978235734245)
                    ·
                      rfl

theorem cell22_1032556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_1032556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032556 prefixEnd_1032556 := by exact prefixLift 1032556
  have htrace : WordTrace (prefixWord ++ tailWord_1032556) baseStart_1032556 baseEnd_1032556 := by
    simpa [prefixWord, tailWord_1032556, baseEnd_1032556] using wordTrace_append hprefix tailTrace_1032556
  have hstable : (prefixWord ++ tailWord_1032556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032556).length < 2 ^ (prefixWord ++ tailWord_1032556).sum := by decide
  have hdescent : baseEnd_1032556 < baseStart_1032556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032573 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_1032573 : Nat := 118140960795 + 1032573 * 2 ^ 59
def prefixEnd_1032573 : Nat := 4983230072969 + 3 ^ 40 * 1032573 * 2
def baseEnd_1032573 : Nat := 353470839903395858059193

theorem tailTrace_1032573 : CollatzResearch.WordTrace tailWord_1032573 prefixEnd_1032573 353470839903395858059193 := by
  unfold tailWord_1032573
  simp only [CollatzResearch.WordTrace]
  refine ⟨37661031288171845273614373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25107354192114563515742915 37661031288171845273614373)
  ·
    refine ⟨7061443366532220988802695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37661031288171845273614373 7061443366532220988802695)
    ·
      refine ⟨10592165049798331483204043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7061443366532220988802695 10592165049798331483204043)
      ·
        refine ⟨15888247574697497224806065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592165049798331483204043 15888247574697497224806065)
        ·
          refine ⟨11916185681023122918604549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15888247574697497224806065 11916185681023122918604549)
          ·
            refine ⟨2234284815191835547238353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11916185681023122918604549 2234284815191835547238353)
            ·
              refine ⟨1675713611393876660428765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2234284815191835547238353 1675713611393876660428765)
              ·
                refine ⟨628392604272703747660787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1675713611393876660428765 628392604272703747660787)
                ·
                  refine ⟨942588906409055621491181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628392604272703747660787 942588906409055621491181)
                  ·
                    refine ⟨353470839903395858059193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942588906409055621491181 353470839903395858059193)
                    ·
                      rfl

theorem cell22_1032573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_1032573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032573 prefixEnd_1032573 := by exact prefixLift 1032573
  have htrace : WordTrace (prefixWord ++ tailWord_1032573) baseStart_1032573 baseEnd_1032573 := by
    simpa [prefixWord, tailWord_1032573, baseEnd_1032573] using wordTrace_append hprefix tailTrace_1032573
  have hstable : (prefixWord ++ tailWord_1032573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032573).length < 2 ^ (prefixWord ++ tailWord_1032573).sum := by decide
  have hdescent : baseEnd_1032573 < baseStart_1032573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032586 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_1032586 : Nat := 118140960795 + 1032586 * 2 ^ 59
def prefixEnd_1032586 : Nat := 4983230072969 + 3 ^ 40 * 1032586 * 2
def baseEnd_1032586 : Nat := 117825096689689385828051

theorem tailTrace_1032586 : CollatzResearch.WordTrace tailWord_1032586 prefixEnd_1032586 117825096689689385828051 := by
  unfold tailWord_1032586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415376359281187123459403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25107670291416498995891741 9415376359281187123459403)
  ·
    refine ⟨14123064538921780685189105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9415376359281187123459403 14123064538921780685189105)
    ·
      refine ⟨10592298404191335513891829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14123064538921780685189105 10592298404191335513891829)
      ·
        refine ⟨993027975392937704427359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10592298404191335513891829 993027975392937704427359)
        ·
          refine ⟨1489541963089406556641039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993027975392937704427359 1489541963089406556641039)
          ·
            refine ⟨2234312944634109834961559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489541963089406556641039 2234312944634109834961559)
            ·
              refine ⟨3351469416951164752442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234312944634109834961559 3351469416951164752442339)
              ·
                refine ⟨5027204125426747128663509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351469416951164752442339 5027204125426747128663509)
                ·
                  refine ⟨117825096689689385828051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5027204125426747128663509 117825096689689385828051)
                  ·
                    rfl

theorem cell22_1032586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_1032586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032586 prefixEnd_1032586 := by exact prefixLift 1032586
  have htrace : WordTrace (prefixWord ++ tailWord_1032586) baseStart_1032586 baseEnd_1032586 := by
    simpa [prefixWord, tailWord_1032586, baseEnd_1032586] using wordTrace_append hprefix tailTrace_1032586
  have hstable : (prefixWord ++ tailWord_1032586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032586).length < 2 ^ (prefixWord ++ tailWord_1032586).sum := by decide
  have hdescent : baseEnd_1032586 < baseStart_1032586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032631 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 4]
def baseStart_1032631 : Nat := 118140960795 + 1032631 * 2 ^ 59
def prefixEnd_1032631 : Nat := 4983230072969 + 3 ^ 40 * 1032631 * 2
def baseEnd_1032631 : Nat := 117830231496234346703005

theorem tailTrace_1032631 : CollatzResearch.WordTrace tailWord_1032631 prefixEnd_1032631 117830231496234346703005 := by
  unfold tailWord_1032631
  simp only [CollatzResearch.WordTrace]
  refine ⟨37663146721961721179225747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25108764481307814119483831 37663146721961721179225747)
  ·
    refine ⟨56494720082942581768838621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37663146721961721179225747 56494720082942581768838621)
    ·
      refine ⟨21185520031103468163314483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56494720082942581768838621 21185520031103468163314483)
      ·
        refine ⟨31778280046655202244971725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21185520031103468163314483 31778280046655202244971725)
        ·
          refine ⟨11916855017495700841864397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31778280046655202244971725 11916855017495700841864397)
          ·
            refine ⟨4468820631560887815699149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11916855017495700841864397 4468820631560887815699149)
            ·
              refine ⟨1675807736835332930887181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4468820631560887815699149 1675807736835332930887181)
              ·
                refine ⟨628427901313249849082693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1675807736835332930887181 628427901313249849082693)
                ·
                  refine ⟨117830231496234346703005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628427901313249849082693 117830231496234346703005)
                  ·
                    rfl

theorem cell22_1032631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 4].length) (baseStart_1032631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032631 prefixEnd_1032631 := by exact prefixLift 1032631
  have htrace : WordTrace (prefixWord ++ tailWord_1032631) baseStart_1032631 baseEnd_1032631 := by
    simpa [prefixWord, tailWord_1032631, baseEnd_1032631] using wordTrace_append hprefix tailTrace_1032631
  have hstable : (prefixWord ++ tailWord_1032631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032631).length < 2 ^ (prefixWord ++ tailWord_1032631).sum := by decide
  have hdescent : baseEnd_1032631 < baseStart_1032631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032648 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_1032648 : Nat := 118140960795 + 1032648 * 2 ^ 59
def prefixEnd_1032648 : Nat := 4983230072969 + 3 ^ 40 * 1032648 * 2
def baseEnd_1032648 : Nat := 117832171312040220811321

theorem tailTrace_1032648 : CollatzResearch.WordTrace tailWord_1032648 prefixEnd_1032648 117832171312040220811321 := by
  unfold tailWord_1032648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831883381450066541297299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25109177841933422055063065 18831883381450066541297299)
  ·
    refine ⟨28247825072175099811945949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18831883381450066541297299 28247825072175099811945949)
    ·
      refine ⟨10592934402065662429479731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28247825072175099811945949 10592934402065662429479731)
      ·
        refine ⟨15889401603098493644219597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592934402065662429479731 15889401603098493644219597)
        ·
          refine ⟨5958525601161935116582349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15889401603098493644219597 5958525601161935116582349)
          ·
            refine ⟨2234447100435725668718381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5958525601161935116582349 2234447100435725668718381)
            ·
              refine ⟨837917662663397125769393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234447100435725668718381 837917662663397125769393)
              ·
                refine ⟨628438246997547844327045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837917662663397125769393 628438246997547844327045)
                ·
                  refine ⟨117832171312040220811321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 628438246997547844327045 117832171312040220811321)
                  ·
                    rfl

theorem cell22_1032648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_1032648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032648 prefixEnd_1032648 := by exact prefixLift 1032648
  have htrace : WordTrace (prefixWord ++ tailWord_1032648) baseStart_1032648 baseEnd_1032648 := by
    simpa [prefixWord, tailWord_1032648, baseEnd_1032648] using wordTrace_append hprefix tailTrace_1032648
  have hstable : (prefixWord ++ tailWord_1032648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032648).length < 2 ^ (prefixWord ++ tailWord_1032648).sum := by decide
  have hdescent : baseEnd_1032648 < baseStart_1032648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032710 : List Nat := [6, 2, 1, 1, 1, 1, 3, 7]
def baseStart_1032710 : Nat := 118140960795 + 1032710 * 2 ^ 59
def prefixEnd_1032710 : Nat := 4983230072969 + 3 ^ 40 * 1032710 * 2
def baseEnd_1032710 : Nat := 39279748644797018598197

theorem tailTrace_1032710 : CollatzResearch.WordTrace tailWord_1032710 prefixEnd_1032710 39279748644797018598197 := by
  unfold tailWord_1032710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177063377771109927229737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25110685392450345114234389 1177063377771109927229737)
  ·
    refine ⟨882797533328332445422303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1177063377771109927229737 882797533328332445422303)
    ·
      refine ⟨1324196299992498668133455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882797533328332445422303 1324196299992498668133455)
      ·
        refine ⟨1986294449988748002200183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324196299992498668133455 1986294449988748002200183)
        ·
          refine ⟨2979441674983122003300275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986294449988748002200183 2979441674983122003300275)
          ·
            refine ⟨4469162512474683004950413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979441674983122003300275 4469162512474683004950413)
            ·
              refine ⟨1675935942178006126856405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4469162512474683004950413 1675935942178006126856405)
              ·
                refine ⟨39279748644797018598197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1675935942178006126856405 39279748644797018598197)
                ·
                  rfl

theorem cell22_1032710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1032710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032710 prefixEnd_1032710 := by exact prefixLift 1032710
  have htrace : WordTrace (prefixWord ++ tailWord_1032710) baseStart_1032710 baseEnd_1032710 := by
    simpa [prefixWord, tailWord_1032710, baseEnd_1032710] using wordTrace_append hprefix tailTrace_1032710
  have hstable : (prefixWord ++ tailWord_1032710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032710).length < 2 ^ (prefixWord ++ tailWord_1032710).sum := by decide
  have hdescent : baseEnd_1032710 < baseStart_1032710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032779 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_1032779 : Nat := 118140960795 + 1032779 * 2 ^ 59
def prefixEnd_1032779 : Nat := 4983230072969 + 3 ^ 40 * 1032779 * 2
def baseEnd_1032779 : Nat := 353541357913279987408561

theorem tailTrace_1032779 : CollatzResearch.WordTrace tailWord_1032779 prefixEnd_1032779 353541357913279987408561 := by
  unfold tailWord_1032779
  simp only [CollatzResearch.WordTrace]
  refine ⟨37668544725425542455613391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25112363150283694970408927 37668544725425542455613391)
  ·
    refine ⟨56502817088138313683420087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37668544725425542455613391 56502817088138313683420087)
    ·
      refine ⟨84754225632207470525130131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56502817088138313683420087 84754225632207470525130131)
      ·
        refine ⟨127131338448311205787695197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84754225632207470525130131 127131338448311205787695197)
        ·
          refine ⟨47674251918116702170385699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127131338448311205787695197 47674251918116702170385699)
          ·
            refine ⟨71511377877175053255578549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47674251918116702170385699 71511377877175053255578549)
            ·
              refine ⟨6704191675985161242710489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71511377877175053255578549 6704191675985161242710489)
              ·
                refine ⟨5028143756988870932032867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6704191675985161242710489 5028143756988870932032867)
                ·
                  refine ⟨7542215635483306398049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028143756988870932032867 7542215635483306398049301)
                  ·
                    refine ⟨353541357913279987408561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7542215635483306398049301 353541357913279987408561)
                    ·
                      rfl

theorem cell22_1032779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_1032779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032779 prefixEnd_1032779 := by exact prefixLift 1032779
  have htrace : WordTrace (prefixWord ++ tailWord_1032779) baseStart_1032779 baseEnd_1032779 := by
    simpa [prefixWord, tailWord_1032779, baseEnd_1032779] using wordTrace_append hprefix tailTrace_1032779
  have hstable : (prefixWord ++ tailWord_1032779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032779).length < 2 ^ (prefixWord ++ tailWord_1032779).sum := by decide
  have hdescent : baseEnd_1032779 < baseStart_1032779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032813 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1032813 : Nat := 118140960795 + 1032813 * 2 ^ 59
def prefixEnd_1032813 : Nat := 4983230072969 + 3 ^ 40 * 1032813 * 2
def baseEnd_1032813 : Nat := 353552996808115232058457

theorem tailTrace_1032813 : CollatzResearch.WordTrace tailWord_1032813 prefixEnd_1032813 353552996808115232058457 := by
  unfold tailWord_1032813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37669784807302366262351093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25113189871534910841567395 37669784807302366262351093)
  ·
    refine ⟨3531542325684596837095415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37669784807302366262351093 3531542325684596837095415)
    ·
      refine ⟨5297313488526895255643123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531542325684596837095415 5297313488526895255643123)
      ·
        refine ⟨7945970232790342883464685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297313488526895255643123 7945970232790342883464685)
        ·
          refine ⟨2979738837296378581299257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7945970232790342883464685 2979738837296378581299257)
          ·
            refine ⟨2234804127972283935974443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979738837296378581299257 2234804127972283935974443)
            ·
              refine ⟨3352206191958425903961665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234804127972283935974443 3352206191958425903961665)
              ·
                refine ⟨2514154643968819427971249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352206191958425903961665 2514154643968819427971249)
                ·
                  refine ⟨1885615982976614570978437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514154643968819427971249 1885615982976614570978437)
                  ·
                    refine ⟨353552996808115232058457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885615982976614570978437 353552996808115232058457)
                    ·
                      rfl

theorem cell22_1032813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1032813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032813 prefixEnd_1032813 := by exact prefixLift 1032813
  have htrace : WordTrace (prefixWord ++ tailWord_1032813) baseStart_1032813 baseEnd_1032813 := by
    simpa [prefixWord, tailWord_1032813, baseEnd_1032813] using wordTrace_append hprefix tailTrace_1032813
  have hstable : (prefixWord ++ tailWord_1032813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032813).length < 2 ^ (prefixWord ++ tailWord_1032813).sum := by decide
  have hdescent : baseEnd_1032813 < baseStart_1032813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032824 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1032824 : Nat := 118140960795 + 1032824 * 2 ^ 59
def prefixEnd_1032824 : Nat := 4983230072969 + 3 ^ 40 * 1032824 * 2
def baseEnd_1032824 : Nat := 353556762332914870033423

theorem tailTrace_1032824 : CollatzResearch.WordTrace tailWord_1032824 prefixEnd_1032824 353556762332914870033423 := by
  unfold tailWord_1032824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18835093005131257570500763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25113457340175010094001017 18835093005131257570500763)
  ·
    refine ⟨28252639507696886355751145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18835093005131257570500763 28252639507696886355751145)
    ·
      refine ⟨21189479630772664766813359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28252639507696886355751145 21189479630772664766813359)
      ·
        refine ⟨31784219446158997150220039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21189479630772664766813359 31784219446158997150220039)
        ·
          refine ⟨47676329169238495725330059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31784219446158997150220039 47676329169238495725330059)
          ·
            refine ⟨71514493753857743587995089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47676329169238495725330059 71514493753857743587995089)
            ·
              refine ⟨53635870315393307690996317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71514493753857743587995089 53635870315393307690996317)
              ·
                refine ⟨20113451368272490384123619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53635870315393307690996317 20113451368272490384123619)
                ·
                  refine ⟨30170177052408735576185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20113451368272490384123619 30170177052408735576185429)
                  ·
                    refine ⟨353556762332914870033423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30170177052408735576185429 353556762332914870033423)
                    ·
                      rfl

theorem cell22_1032824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1032824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032824 prefixEnd_1032824 := by exact prefixLift 1032824
  have htrace : WordTrace (prefixWord ++ tailWord_1032824) baseStart_1032824 baseEnd_1032824 := by
    simpa [prefixWord, tailWord_1032824, baseEnd_1032824] using wordTrace_append hprefix tailTrace_1032824
  have hstable : (prefixWord ++ tailWord_1032824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032824).length < 2 ^ (prefixWord ++ tailWord_1032824).sum := by decide
  have hdescent : baseEnd_1032824 < baseStart_1032824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032877 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1032877 : Nat := 118140960795 + 1032877 * 2 ^ 59
def prefixEnd_1032877 : Nat := 4983230072969 + 3 ^ 40 * 1032877 * 2
def baseEnd_1032877 : Nat := 353574905316040398458261

theorem tailTrace_1032877 : CollatzResearch.WordTrace tailWord_1032877 prefixEnd_1032877 353574905316040398458261 := by
  unfold tailWord_1032877
  simp only [CollatzResearch.WordTrace]
  refine ⟨37672119079070505192680885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25114746052713670128453923 37672119079070505192680885)
  ·
    refine ⟨3531761163662859861813833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37672119079070505192680885 3531761163662859861813833)
    ·
      refine ⟨2648820872747144896360375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3531761163662859861813833 2648820872747144896360375)
      ·
        refine ⟨3973231309120717344540563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648820872747144896360375 3973231309120717344540563)
        ·
          refine ⟨5959846963681076016810845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973231309120717344540563 5959846963681076016810845)
          ·
            refine ⟨2234942611380403506304067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5959846963681076016810845 2234942611380403506304067)
            ·
              refine ⟨3352413917070605259456101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234942611380403506304067 3352413917070605259456101)
              ·
                refine ⟨628577609450738486148019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3352413917070605259456101 628577609450738486148019)
                ·
                  refine ⟨942866414176107729222029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628577609450738486148019 942866414176107729222029)
                  ·
                    refine ⟨353574905316040398458261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942866414176107729222029 353574905316040398458261)
                    ·
                      rfl

theorem cell22_1032877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1032877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032877 prefixEnd_1032877 := by exact prefixLift 1032877
  have htrace : WordTrace (prefixWord ++ tailWord_1032877) baseStart_1032877 baseEnd_1032877 := by
    simpa [prefixWord, tailWord_1032877, baseEnd_1032877] using wordTrace_append hprefix tailTrace_1032877
  have hstable : (prefixWord ++ tailWord_1032877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032877).length < 2 ^ (prefixWord ++ tailWord_1032877).sum := by decide
  have hdescent : baseEnd_1032877 < baseStart_1032877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032920 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_1032920 : Nat := 118140960795 + 1032920 * 2 ^ 59
def prefixEnd_1032920 : Nat := 4983230072969 + 3 ^ 40 * 1032920 * 2
def baseEnd_1032920 : Nat := 353589625094802619633129

theorem tailTrace_1032920 : CollatzResearch.WordTrace tailWord_1032920 prefixEnd_1032920 353589625094802619633129 := by
  unfold tailWord_1032920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18836843708957361768248107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25115791611943149024330809 18836843708957361768248107)
  ·
    refine ⟨28255265563436042652372161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18836843708957361768248107 28255265563436042652372161)
    ·
      refine ⟨21191449172577031989279121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28255265563436042652372161 21191449172577031989279121)
      ·
        refine ⟨15893586879432773991959341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21191449172577031989279121 15893586879432773991959341)
        ·
          refine ⟨5960095079787290246984753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15893586879432773991959341 5960095079787290246984753)
          ·
            refine ⟨4470071309840467685238565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5960095079787290246984753 4470071309840467685238565)
            ·
              refine ⟨838138370595087690982231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4470071309840467685238565 838138370595087690982231)
              ·
                refine ⟨1257207555892631536473347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838138370595087690982231 1257207555892631536473347)
                ·
                  refine ⟨1885811333838947304710021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257207555892631536473347 1885811333838947304710021)
                  ·
                    refine ⟨353589625094802619633129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885811333838947304710021 353589625094802619633129)
                    ·
                      rfl

theorem cell22_1032920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_1032920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032920 prefixEnd_1032920 := by exact prefixLift 1032920
  have htrace : WordTrace (prefixWord ++ tailWord_1032920) baseStart_1032920 baseEnd_1032920 := by
    simpa [prefixWord, tailWord_1032920, baseEnd_1032920] using wordTrace_append hprefix tailTrace_1032920
  have hstable : (prefixWord ++ tailWord_1032920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032920).length < 2 ^ (prefixWord ++ tailWord_1032920).sum := by decide
  have hdescent : baseEnd_1032920 < baseStart_1032920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032961 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1032961 : Nat := 118140960795 + 1032961 * 2 ^ 59
def prefixEnd_1032961 : Nat := 4983230072969 + 3 ^ 40 * 1032961 * 2
def baseEnd_1032961 : Nat := 353603660232692179358003

theorem tailTrace_1032961 : CollatzResearch.WordTrace tailWord_1032961 prefixEnd_1032961 353603660232692179358003 := by
  unfold tailWord_1032961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37675182810766187538738737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25116788540510791692492491 37675182810766187538738737)
  ·
    refine ⟨28256387108074640654054053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37675182810766187538738737 28256387108074640654054053)
    ·
      refine ⟨5298072582763995122635135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28256387108074640654054053 5298072582763995122635135)
      ·
        refine ⟨7947108874145992683952703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298072582763995122635135 7947108874145992683952703)
        ·
          refine ⟨11920663311218989025929055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947108874145992683952703 11920663311218989025929055)
          ·
            refine ⟨17880994966828483538893583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920663311218989025929055 17880994966828483538893583)
            ·
              refine ⟨26821492450242725308340375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17880994966828483538893583 26821492450242725308340375)
              ·
                refine ⟨40232238675364087962510563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26821492450242725308340375 40232238675364087962510563)
                ·
                  refine ⟨60348358013046131943765845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40232238675364087962510563 60348358013046131943765845)
                  ·
                    refine ⟨353603660232692179358003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60348358013046131943765845 353603660232692179358003)
                    ·
                      rfl

theorem cell22_1032961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1032961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1032961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1032961 prefixEnd_1032961 := by exact prefixLift 1032961
  have htrace : WordTrace (prefixWord ++ tailWord_1032961) baseStart_1032961 baseEnd_1032961 := by
    simpa [prefixWord, tailWord_1032961, baseEnd_1032961] using wordTrace_append hprefix tailTrace_1032961
  have hstable : (prefixWord ++ tailWord_1032961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032961).length < 2 ^ (prefixWord ++ tailWord_1032961).sum := by decide
  have hdescent : baseEnd_1032961 < baseStart_1032961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033119 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 2, 3]
def baseStart_1033119 : Nat := 118140960795 + 1033119 * 2 ^ 59
def prefixEnd_1033119 : Nat := 4983230072969 + 3 ^ 40 * 1033119 * 2
def baseEnd_1033119 : Nat := 353657746861632433907519

theorem tailTrace_1033119 : CollatzResearch.WordTrace tailWord_1033119 prefixEnd_1033119 353657746861632433907519 := by
  unfold tailWord_1033119
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680945544193780522990411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25120630362795853681993607 37680945544193780522990411)
  ·
    refine ⟨56521418316290670784485617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37680945544193780522990411 56521418316290670784485617)
    ·
      refine ⟨42391063737218003088364213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56521418316290670784485617 42391063737218003088364213)
      ·
        refine ⟨3974162225364187789534145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42391063737218003088364213 3974162225364187789534145)
        ·
          refine ⟨2980621669023140842150609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3974162225364187789534145 2980621669023140842150609)
          ·
            refine ⟨2235466251767355631612957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980621669023140842150609 2235466251767355631612957)
            ·
              refine ⟨838299844412758361854859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2235466251767355631612957 838299844412758361854859)
              ·
                refine ⟨1257449766619137542782289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838299844412758361854859 1257449766619137542782289)
                ·
                  refine ⟨943087324964353157086717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257449766619137542782289 943087324964353157086717)
                  ·
                    refine ⟨353657746861632433907519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943087324964353157086717 353657746861632433907519)
                    ·
                      rfl

theorem cell22_1033119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_1033119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033119 prefixEnd_1033119 := by exact prefixLift 1033119
  have htrace : WordTrace (prefixWord ++ tailWord_1033119) baseStart_1033119 baseEnd_1033119 := by
    simpa [prefixWord, tailWord_1033119, baseEnd_1033119] using wordTrace_append hprefix tailTrace_1033119
  have hstable : (prefixWord ++ tailWord_1033119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033119).length < 2 ^ (prefixWord ++ tailWord_1033119).sum := by decide
  have hdescent : baseEnd_1033119 < baseStart_1033119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033143 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 7]
def baseStart_1033143 : Nat := 118140960795 + 1033143 * 2 ^ 59
def prefixEnd_1033143 : Nat := 4983230072969 + 3 ^ 40 * 1033143 * 2
def baseEnd_1033143 : Nat := 117888654184034790435815

theorem tailTrace_1033143 : CollatzResearch.WordTrace tailWord_1033143 prefixEnd_1033143 117888654184034790435815 := by
  unfold tailWord_1033143
  simp only [CollatzResearch.WordTrace]
  refine ⟨37681820896106832621864083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25121213930737888414576055 37681820896106832621864083)
  ·
    refine ⟨56522731344160248932796125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37681820896106832621864083 56522731344160248932796125)
    ·
      refine ⟨21196024254060093349798547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56522731344160248932796125 21196024254060093349798547)
      ·
        refine ⟨31794036381090140024697821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21196024254060093349798547 31794036381090140024697821)
        ·
          refine ⟨11922763642908802509261683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31794036381090140024697821 11922763642908802509261683)
          ·
            refine ⟨17884145464363203763892525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11922763642908802509261683 17884145464363203763892525)
            ·
              refine ⟨6706554549136201411459697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17884145464363203763892525 6706554549136201411459697)
              ·
                refine ⟨5029915911852151058594773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6706554549136201411459697 5029915911852151058594773)
                ·
                  refine ⟨117888654184034790435815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5029915911852151058594773 117888654184034790435815)
                  ·
                    rfl

theorem cell22_1033143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_1033143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033143 prefixEnd_1033143 := by exact prefixLift 1033143
  have htrace : WordTrace (prefixWord ++ tailWord_1033143) baseStart_1033143 baseEnd_1033143 := by
    simpa [prefixWord, tailWord_1033143, baseEnd_1033143] using wordTrace_append hprefix tailTrace_1033143
  have hstable : (prefixWord ++ tailWord_1033143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033143).length < 2 ^ (prefixWord ++ tailWord_1033143).sum := by decide
  have hdescent : baseEnd_1033143 < baseStart_1033143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033177 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 5]
def baseStart_1033177 : Nat := 118140960795 + 1033177 * 2 ^ 59
def prefixEnd_1033177 : Nat := 4983230072969 + 3 ^ 40 * 1033177 * 2
def baseEnd_1033177 : Nat := 117892533815646538652447

theorem tailTrace_1033177 : CollatzResearch.WordTrace tailWord_1033177 prefixEnd_1033177 117892533815646538652447 := by
  unfold tailWord_1033177
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683060977983656428601785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25122040651989104285734523 37683060977983656428601785)
  ·
    refine ⟨28262295733487742321451339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37683060977983656428601785 28262295733487742321451339)
    ·
      refine ⟨42393443600231613482177009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28262295733487742321451339 42393443600231613482177009)
      ·
        refine ⟨31795082700173710111632757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42393443600231613482177009 31795082700173710111632757)
        ·
          refine ⟨2980789003141285322965571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31795082700173710111632757 2980789003141285322965571)
          ·
            refine ⟨4471183504711927984448357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980789003141285322965571 4471183504711927984448357)
            ·
              refine ⟨838346907133486497084067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4471183504711927984448357 838346907133486497084067)
              ·
                refine ⟨1257520360700229745626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838346907133486497084067 1257520360700229745626101)
                ·
                  refine ⟨117892533815646538652447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257520360700229745626101 117892533815646538652447)
                  ·
                    rfl

theorem cell22_1033177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_1033177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033177 prefixEnd_1033177 := by exact prefixLift 1033177
  have htrace : WordTrace (prefixWord ++ tailWord_1033177) baseStart_1033177 baseEnd_1033177 := by
    simpa [prefixWord, tailWord_1033177, baseEnd_1033177] using wordTrace_append hprefix tailTrace_1033177
  have hstable : (prefixWord ++ tailWord_1033177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033177).length < 2 ^ (prefixWord ++ tailWord_1033177).sum := by decide
  have hdescent : baseEnd_1033177 < baseStart_1033177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033237 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1033237 : Nat := 118140960795 + 1033237 * 2 ^ 59
def prefixEnd_1033237 : Nat := 4983230072969 + 3 ^ 40 * 1033237 * 2
def baseEnd_1033237 : Nat := 353698140673119459457157

theorem tailTrace_1033237 : CollatzResearch.WordTrace tailWord_1033237 prefixEnd_1033237 353698140673119459457157 := by
  unfold tailWord_1033237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37685249357766286675785965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25123499571844191117190643 37685249357766286675785965)
  ·
    refine ⟨14131968509162357503419737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37685249357766286675785965 14131968509162357503419737)
    ·
      refine ⟨10598976381871768127564803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14131968509162357503419737 10598976381871768127564803)
      ·
        refine ⟨15898464572807652191347205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598976381871768127564803 15898464572807652191347205)
        ·
          refine ⟨2980962107401434785877601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15898464572807652191347205 2980962107401434785877601)
          ·
            refine ⟨2235721580551076089408201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980962107401434785877601 2235721580551076089408201)
            ·
              refine ⟨1676791185413307067056151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235721580551076089408201 1676791185413307067056151)
              ·
                refine ⟨2515186778119960600584227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676791185413307067056151 2515186778119960600584227)
                ·
                  refine ⟨3772780167179940900876341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515186778119960600584227 3772780167179940900876341)
                  ·
                    refine ⟨353698140673119459457157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3772780167179940900876341 353698140673119459457157)
                    ·
                      rfl

theorem cell22_1033237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1033237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033237 prefixEnd_1033237 := by exact prefixLift 1033237
  have htrace : WordTrace (prefixWord ++ tailWord_1033237) baseStart_1033237 baseEnd_1033237 := by
    simpa [prefixWord, tailWord_1033237, baseEnd_1033237] using wordTrace_append hprefix tailTrace_1033237
  have hstable : (prefixWord ++ tailWord_1033237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033237).length < 2 ^ (prefixWord ++ tailWord_1033237).sum := by decide
  have hdescent : baseEnd_1033237 < baseStart_1033237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033252 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1033252 : Nat := 118140960795 + 1033252 * 2 ^ 59
def prefixEnd_1033252 : Nat := 4983230072969 + 3 ^ 40 * 1033252 * 2
def baseEnd_1033252 : Nat := 353703275479664420332111

theorem tailTrace_1033252 : CollatzResearch.WordTrace tailWord_1033252 prefixEnd_1033252 353703275479664420332111 := by
  unfold tailWord_1033252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842898226355972118791005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25123864301807962825054673 18842898226355972118791005)
  ·
    refine ⟨7066086834883489544546627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18842898226355972118791005 7066086834883489544546627)
    ·
      refine ⟨10599130252325234316819941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066086834883489544546627 10599130252325234316819941)
      ·
        refine ⟨1987336922310981434403739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10599130252325234316819941 1987336922310981434403739)
        ·
          refine ⟨2981005383466472151605609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987336922310981434403739 2981005383466472151605609)
          ·
            refine ⟨2235754037599854113704207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981005383466472151605609 2235754037599854113704207)
            ·
              refine ⟨3353631056399781170556311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235754037599854113704207 3353631056399781170556311)
              ·
                refine ⟨5030446584599671755834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353631056399781170556311 5030446584599671755834467)
                ·
                  refine ⟨7545669876899507633751701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030446584599671755834467 7545669876899507633751701)
                  ·
                    refine ⟨353703275479664420332111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7545669876899507633751701 353703275479664420332111)
                    ·
                      rfl

theorem cell22_1033252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1033252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033252 prefixEnd_1033252 := by exact prefixLift 1033252
  have htrace : WordTrace (prefixWord ++ tailWord_1033252) baseStart_1033252 baseEnd_1033252 := by
    simpa [prefixWord, tailWord_1033252, baseEnd_1033252] using wordTrace_append hprefix tailTrace_1033252
  have hstable : (prefixWord ++ tailWord_1033252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033252).length < 2 ^ (prefixWord ++ tailWord_1033252).sum := by decide
  have hdescent : baseEnd_1033252 < baseStart_1033252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033258 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1033258 : Nat := 118140960795 + 1033258 * 2 ^ 59
def prefixEnd_1033258 : Nat := 4983230072969 + 3 ^ 40 * 1033258 * 2
def baseEnd_1033258 : Nat := 353705329402282404682093

theorem tailTrace_1033258 : CollatzResearch.WordTrace tailWord_1033258 prefixEnd_1033258 353705329402282404682093 := by
  unfold tailWord_1033258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421503822672551815575107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25124010193793471508200285 9421503822672551815575107)
  ·
    refine ⟨14132255734008827723362661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421503822672551815575107 14132255734008827723362661)
    ·
      refine ⟨2649797950126655198130499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14132255734008827723362661 2649797950126655198130499)
      ·
        refine ⟨3974696925189982797195749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649797950126655198130499 3974696925189982797195749)
        ·
          refine ⟨745255673473121774474203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3974696925189982797195749 745255673473121774474203)
          ·
            refine ⟨1117883510209682661711305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745255673473121774474203 1117883510209682661711305)
            ·
              refine ⟨838412632657261996283479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117883510209682661711305 838412632657261996283479)
              ·
                refine ⟨1257618948985892994425219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838412632657261996283479 1257618948985892994425219)
                ·
                  refine ⟨1886428423478839491637829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257618948985892994425219 1886428423478839491637829)
                  ·
                    refine ⟨353705329402282404682093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886428423478839491637829 353705329402282404682093)
                    ·
                      rfl

theorem cell22_1033258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1033258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033258 prefixEnd_1033258 := by exact prefixLift 1033258
  have htrace : WordTrace (prefixWord ++ tailWord_1033258) baseStart_1033258 baseEnd_1033258 := by
    simpa [prefixWord, tailWord_1033258, baseEnd_1033258] using wordTrace_append hprefix tailTrace_1033258
  have hstable : (prefixWord ++ tailWord_1033258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033258).length < 2 ^ (prefixWord ++ tailWord_1033258).sum := by decide
  have hdescent : baseEnd_1033258 < baseStart_1033258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033333 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1033333 : Nat := 118140960795 + 1033333 * 2 ^ 59
def prefixEnd_1033333 : Nat := 4983230072969 + 3 ^ 40 * 1033333 * 2
def baseEnd_1033333 : Nat := 353731003435007209056863

theorem tailTrace_1033333 : CollatzResearch.WordTrace tailWord_1033333 prefixEnd_1033333 353731003435007209056863 := by
  unfold tailWord_1033333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37688750765418495071280653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25125833843612330047520435 37688750765418495071280653)
  ·
    refine ⟨14133281537031935651730245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37688750765418495071280653 14133281537031935651730245)
    ·
      refine ⟨2649990288193487934699421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14133281537031935651730245 2649990288193487934699421)
      ·
        refine ⟨993746358072557975512283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2649990288193487934699421 993746358072557975512283)
        ·
          refine ⟨1490619537108836963268425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993746358072557975512283 1490619537108836963268425)
          ·
            refine ⟨1117964652831627722451319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490619537108836963268425 1117964652831627722451319)
            ·
              refine ⟨1676946979247441583676979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117964652831627722451319 1676946979247441583676979)
              ·
                refine ⟨2515420468871162375515469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676946979247441583676979 2515420468871162375515469)
                ·
                  refine ⟨943282675826685890818301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2515420468871162375515469 943282675826685890818301)
                  ·
                    refine ⟨353731003435007209056863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943282675826685890818301 353731003435007209056863)
                    ·
                      rfl

theorem cell22_1033333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1033333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033333 prefixEnd_1033333 := by exact prefixLift 1033333
  have htrace : WordTrace (prefixWord ++ tailWord_1033333) baseStart_1033333 baseEnd_1033333 := by
    simpa [prefixWord, tailWord_1033333, baseEnd_1033333] using wordTrace_append hprefix tailTrace_1033333
  have hstable : (prefixWord ++ tailWord_1033333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033333).length < 2 ^ (prefixWord ++ tailWord_1033333).sum := by decide
  have hdescent : baseEnd_1033333 < baseStart_1033333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033355 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_1033355 : Nat := 118140960795 + 1033355 * 2 ^ 59
def prefixEnd_1033355 : Nat := 4983230072969 + 3 ^ 40 * 1033355 * 2
def baseEnd_1033355 : Nat := 353738534484606485006795

theorem tailTrace_1033355 : CollatzResearch.WordTrace tailWord_1033355 prefixEnd_1033355 353738534484606485006795 := by
  unfold tailWord_1033355
  simp only [CollatzResearch.WordTrace]
  refine ⟨37689553171338792828581519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25126368780892528552387679 37689553171338792828581519)
  ·
    refine ⟨56534329757008189242872279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37689553171338792828581519 56534329757008189242872279)
    ·
      refine ⟨84801494635512283864308419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56534329757008189242872279 84801494635512283864308419)
      ·
        refine ⟨127202241953268425796462629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84801494635512283864308419 127202241953268425796462629)
        ·
          refine ⟨23850420366237829836836743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127202241953268425796462629 23850420366237829836836743)
          ·
            refine ⟨35775630549356744755255115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850420366237829836836743 35775630549356744755255115)
            ·
              refine ⟨53663445824035117132882673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35775630549356744755255115 53663445824035117132882673)
              ·
                refine ⟨40247584368026337849662005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53663445824035117132882673 40247584368026337849662005)
                ·
                  refine ⟨3773211034502469173405813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40247584368026337849662005 3773211034502469173405813)
                  ·
                    refine ⟨353738534484606485006795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3773211034502469173405813 353738534484606485006795)
                    ·
                      rfl

theorem cell22_1033355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_1033355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033355 prefixEnd_1033355 := by exact prefixLift 1033355
  have htrace : WordTrace (prefixWord ++ tailWord_1033355) baseStart_1033355 baseEnd_1033355 := by
    simpa [prefixWord, tailWord_1033355, baseEnd_1033355] using wordTrace_append hprefix tailTrace_1033355
  have hstable : (prefixWord ++ tailWord_1033355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033355).length < 2 ^ (prefixWord ++ tailWord_1033355).sum := by decide
  have hdescent : baseEnd_1033355 < baseStart_1033355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033372 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1033372 : Nat := 118140960795 + 1033372 * 2 ^ 59
def prefixEnd_1033372 : Nat := 4983230072969 + 3 ^ 40 * 1033372 * 2
def baseEnd_1033372 : Nat := 353744353932024107331743

theorem tailTrace_1033372 : CollatzResearch.WordTrace tailWord_1033372 prefixEnd_1033372 353744353932024107331743 := by
  unfold tailWord_1033372
  simp only [CollatzResearch.WordTrace]
  refine ⟨18845086606138602365975185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25126782141518136487966913 18845086606138602365975185)
  ·
    refine ⟨14133814954603951774481389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18845086606138602365975185 14133814954603951774481389)
    ·
      refine ⟨5300180607976481915430521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14133814954603951774481389 5300180607976481915430521)
      ·
        refine ⟨3975135455982361436572891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5300180607976481915430521 3975135455982361436572891)
        ·
          refine ⟨5962703183973542154859337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975135455982361436572891 5962703183973542154859337)
          ·
            refine ⟨4472027387980156616144503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962703183973542154859337 4472027387980156616144503)
            ·
              refine ⟨6708041081970234924216755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472027387980156616144503 6708041081970234924216755)
              ·
                refine ⟨10062061622955352386325133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708041081970234924216755 10062061622955352386325133)
                ·
                  refine ⟨3773273108608257144871925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10062061622955352386325133 3773273108608257144871925)
                  ·
                    refine ⟨353744353932024107331743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3773273108608257144871925 353744353932024107331743)
                    ·
                      rfl

theorem cell22_1033372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1033372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033372 prefixEnd_1033372 := by exact prefixLift 1033372
  have htrace : WordTrace (prefixWord ++ tailWord_1033372) baseStart_1033372 baseEnd_1033372 := by
    simpa [prefixWord, tailWord_1033372, baseEnd_1033372] using wordTrace_append hprefix tailTrace_1033372
  have hstable : (prefixWord ++ tailWord_1033372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033372).length < 2 ^ (prefixWord ++ tailWord_1033372).sum := by decide
  have hdescent : baseEnd_1033372 < baseStart_1033372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033406 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1033406 : Nat := 118140960795 + 1033406 * 2 ^ 59
def prefixEnd_1033406 : Nat := 4983230072969 + 3 ^ 40 * 1033406 * 2
def baseEnd_1033406 : Nat := 353755992826859351981639

theorem tailTrace_1033406 : CollatzResearch.WordTrace tailWord_1033406 prefixEnd_1033406 353755992826859351981639 := by
  unfold tailWord_1033406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711426661769253567336009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25127608862769352359125381 4711426661769253567336009)
  ·
    refine ⟨3533569996326940175502007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4711426661769253567336009 3533569996326940175502007)
    ·
      refine ⟨5300354994490410263253011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533569996326940175502007 5300354994490410263253011)
      ·
        refine ⟨7950532491735615394879517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300354994490410263253011 7950532491735615394879517)
        ·
          refine ⟨2981449684400855773079819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7950532491735615394879517 2981449684400855773079819)
          ·
            refine ⟨4472174526601283659619729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981449684400855773079819 4472174526601283659619729)
            ·
              refine ⟨3354130894950962744714797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472174526601283659619729 3354130894950962744714797)
              ·
                refine ⟨1257799085606611029268049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3354130894950962744714797 1257799085606611029268049)
                ·
                  refine ⟨943349314204958271951037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257799085606611029268049 943349314204958271951037)
                  ·
                    refine ⟨353755992826859351981639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943349314204958271951037 353755992826859351981639)
                    ·
                      rfl

theorem cell22_1033406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1033406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033406 prefixEnd_1033406 := by exact prefixLift 1033406
  have htrace : WordTrace (prefixWord ++ tailWord_1033406) baseStart_1033406 baseEnd_1033406 := by
    simpa [prefixWord, tailWord_1033406, baseEnd_1033406] using wordTrace_append hprefix tailTrace_1033406
  have hstable : (prefixWord ++ tailWord_1033406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033406).length < 2 ^ (prefixWord ++ tailWord_1033406).sum := by decide
  have hdescent : baseEnd_1033406 < baseStart_1033406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033451 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 1, 3]
def baseStart_1033451 : Nat := 118140960795 + 1033451 * 2 ^ 59
def prefixEnd_1033451 : Nat := 4983230072969 + 3 ^ 40 * 1033451 * 2
def baseEnd_1033451 : Nat := 353771397246494234606501

theorem tailTrace_1033451 : CollatzResearch.WordTrace tailWord_1033451 prefixEnd_1033451 353771397246494234606501 := by
  unfold tailWord_1033451
  simp only [CollatzResearch.WordTrace]
  refine ⟨37693054578991001224076207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25128703052660667482717471 37693054578991001224076207)
  ·
    refine ⟨56539581868486501836114311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37693054578991001224076207 56539581868486501836114311)
    ·
      refine ⟨84809372802729752754171467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56539581868486501836114311 84809372802729752754171467)
      ·
        refine ⟨127214059204094629131257201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84809372802729752754171467 127214059204094629131257201)
        ·
          refine ⟨95410544403070971848442901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127214059204094629131257201 95410544403070971848442901)
          ·
            refine ⟨4472369268893951805395761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95410544403070971848442901 4472369268893951805395761)
            ·
              refine ⟨3354276951670463854046821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472369268893951805395761 3354276951670463854046821)
              ·
                refine ⟨628926928438211972633779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3354276951670463854046821 628926928438211972633779)
                ·
                  refine ⟨943390392657317958950669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628926928438211972633779 943390392657317958950669)
                  ·
                    refine ⟨353771397246494234606501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943390392657317958950669 353771397246494234606501)
                    ·
                      rfl

theorem cell22_1033451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 3].length) (baseStart_1033451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033451 prefixEnd_1033451 := by exact prefixLift 1033451
  have htrace : WordTrace (prefixWord ++ tailWord_1033451) baseStart_1033451 baseEnd_1033451 := by
    simpa [prefixWord, tailWord_1033451, baseEnd_1033451] using wordTrace_append hprefix tailTrace_1033451
  have hstable : (prefixWord ++ tailWord_1033451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033451).length < 2 ^ (prefixWord ++ tailWord_1033451).sum := by decide
  have hdescent : baseEnd_1033451 < baseStart_1033451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033502 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1033502 : Nat := 118140960795 + 1033502 * 2 ^ 59
def prefixEnd_1033502 : Nat := 4983230072969 + 3 ^ 40 * 1033502 * 2
def baseEnd_1033502 : Nat := 353788855588747101581345

theorem tailTrace_1033502 : CollatzResearch.WordTrace tailWord_1033502 prefixEnd_1033502 353788855588747101581345 := by
  unfold tailWord_1033502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711864337725779616772845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25129943134537491289455173 4711864337725779616772845)
  ·
    refine ⟨1766949126647167356289817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4711864337725779616772845 1766949126647167356289817)
    ·
      refine ⟨1325211844985375517217363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1766949126647167356289817 1325211844985375517217363)
      ·
        refine ⟨1987817767478063275826045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325211844985375517217363 1987817767478063275826045)
        ·
          refine ⟨745431662804273728434767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1987817767478063275826045 745431662804273728434767)
          ·
            refine ⟨1118147494206410592652151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745431662804273728434767 1118147494206410592652151)
            ·
              refine ⟨1677221241309615888978227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118147494206410592652151 1677221241309615888978227)
              ·
                refine ⟨2515831861964423833467341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677221241309615888978227 2515831861964423833467341)
                ·
                  refine ⟨943436948236658937550253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2515831861964423833467341 943436948236658937550253)
                  ·
                    refine ⟨353788855588747101581345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943436948236658937550253 353788855588747101581345)
                    ·
                      rfl

theorem cell22_1033502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1033502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033502 prefixEnd_1033502 := by exact prefixLift 1033502
  have htrace : WordTrace (prefixWord ++ tailWord_1033502) baseStart_1033502 baseEnd_1033502 := by
    simpa [prefixWord, tailWord_1033502, baseEnd_1033502] using wordTrace_append hprefix tailTrace_1033502
  have hstable : (prefixWord ++ tailWord_1033502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033502).length < 2 ^ (prefixWord ++ tailWord_1033502).sum := by decide
  have hdescent : baseEnd_1033502 < baseStart_1033502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033509 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 6]
def baseStart_1033509 : Nat := 118140960795 + 1033509 * 2 ^ 59
def prefixEnd_1033509 : Nat := 4983230072969 + 3 ^ 40 * 1033509 * 2
def baseEnd_1033509 : Nat := 117930417277267138885441

theorem tailTrace_1033509 : CollatzResearch.WordTrace tailWord_1033509 prefixEnd_1033509 117930417277267138885441 := by
  unfold tailWord_1033509
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695170012780877129687581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25130113341853918086458387 37695170012780877129687581)
  ·
    refine ⟨14135688754792828923632843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37695170012780877129687581 14135688754792828923632843)
    ·
      refine ⟨21203533132189243385449265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14135688754792828923632843 21203533132189243385449265)
      ·
        refine ⟨15902649849141932539086949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21203533132189243385449265 15902649849141932539086949)
        ·
          refine ⟨2981746846714112351078803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15902649849141932539086949 2981746846714112351078803)
          ·
            refine ⟨4472620270071168526618205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981746846714112351078803 4472620270071168526618205)
            ·
              refine ⟨1677232601276688197481827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4472620270071168526618205 1677232601276688197481827)
              ·
                refine ⟨2515848901915032296222741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677232601276688197481827 2515848901915032296222741)
                ·
                  refine ⟨117930417277267138885441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2515848901915032296222741 117930417277267138885441)
                  ·
                    rfl

theorem cell22_1033509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_1033509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033509 prefixEnd_1033509 := by exact prefixLift 1033509
  have htrace : WordTrace (prefixWord ++ tailWord_1033509) baseStart_1033509 baseEnd_1033509 := by
    simpa [prefixWord, tailWord_1033509, baseEnd_1033509] using wordTrace_append hprefix tailTrace_1033509
  have hstable : (prefixWord ++ tailWord_1033509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033509).length < 2 ^ (prefixWord ++ tailWord_1033509).sum := by decide
  have hdescent : baseEnd_1033509 < baseStart_1033509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033569 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1033569 : Nat := 118140960795 + 1033569 * 2 ^ 59
def prefixEnd_1033569 : Nat := 4983230072969 + 3 ^ 40 * 1033569 * 2
def baseEnd_1033569 : Nat := 353811791057981260156139

theorem tailTrace_1033569 : CollatzResearch.WordTrace tailWord_1033569 prefixEnd_1033569 353811791057981260156139 := by
  unfold tailWord_1033569
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697358392563507376871761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25131572261709004917914507 37697358392563507376871761)
  ·
    refine ⟨28273018794422630532653821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37697358392563507376871761 28273018794422630532653821)
    ·
      refine ⟨10602382047908486449745183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28273018794422630532653821 10602382047908486449745183)
      ·
        refine ⟨15903573071862729674617775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10602382047908486449745183 15903573071862729674617775)
        ·
          refine ⟨23855359607794094511926663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15903573071862729674617775 23855359607794094511926663)
          ·
            refine ⟨35783039411691141767889995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23855359607794094511926663 35783039411691141767889995)
            ·
              refine ⟨53674559117536712651834993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35783039411691141767889995 53674559117536712651834993)
              ·
                refine ⟨40255919338152534488876245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53674559117536712651834993 40255919338152534488876245)
                ·
                  refine ⟨943498109487950027083037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40255919338152534488876245 943498109487950027083037)
                  ·
                    refine ⟨353811791057981260156139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943498109487950027083037 353811791057981260156139)
                    ·
                      rfl

theorem cell22_1033569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1033569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033569 prefixEnd_1033569 := by exact prefixLift 1033569
  have htrace : WordTrace (prefixWord ++ tailWord_1033569) baseStart_1033569 baseEnd_1033569 := by
    simpa [prefixWord, tailWord_1033569, baseEnd_1033569] using wordTrace_append hprefix tailTrace_1033569
  have hstable : (prefixWord ++ tailWord_1033569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033569).length < 2 ^ (prefixWord ++ tailWord_1033569).sum := by decide
  have hdescent : baseEnd_1033569 < baseStart_1033569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033586 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1033586 : Nat := 118140960795 + 1033586 * 2 ^ 59
def prefixEnd_1033586 : Nat := 4983230072969 + 3 ^ 40 * 1033586 * 2
def baseEnd_1033586 : Nat := 353817610505398882481087

theorem tailTrace_1033586 : CollatzResearch.WordTrace tailWord_1033586 prefixEnd_1033586 353817610505398882481087 := by
  unfold tailWord_1033586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9424494608375479820060153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25131985622334612853493741 9424494608375479820060153)
  ·
    refine ⟨7068370956281609865045115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9424494608375479820060153 7068370956281609865045115)
    ·
      refine ⟨10602556434422414797567673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7068370956281609865045115 10602556434422414797567673)
      ·
        refine ⟨7951917325816811098175755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10602556434422414797567673 7951917325816811098175755)
        ·
          refine ⟨11927875988725216647263633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951917325816811098175755 11927875988725216647263633)
          ·
            refine ⟨8945906991543912485447725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11927875988725216647263633 8945906991543912485447725)
            ·
              refine ⟨3354715121828967182042897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8945906991543912485447725 3354715121828967182042897)
              ·
                refine ⟨2516036341371725386532173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354715121828967182042897 2516036341371725386532173)
                ·
                  refine ⟨943513628014397019949565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2516036341371725386532173 943513628014397019949565)
                  ·
                    refine ⟨353817610505398882481087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943513628014397019949565 353817610505398882481087)
                    ·
                      rfl

theorem cell22_1033586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1033586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033586 prefixEnd_1033586 := by exact prefixLift 1033586
  have htrace : WordTrace (prefixWord ++ tailWord_1033586) baseStart_1033586 baseEnd_1033586 := by
    simpa [prefixWord, tailWord_1033586, baseEnd_1033586] using wordTrace_append hprefix tailTrace_1033586
  have hstable : (prefixWord ++ tailWord_1033586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033586).length < 2 ^ (prefixWord ++ tailWord_1033586).sum := by decide
  have hdescent : baseEnd_1033586 < baseStart_1033586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033603 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 1, 3]
def baseStart_1033603 : Nat := 118140960795 + 1033603 * 2 ^ 59
def prefixEnd_1033603 : Nat := 4983230072969 + 3 ^ 40 * 1033603 * 2
def baseEnd_1033603 : Nat := 353823429952816504806035

theorem tailTrace_1033603 : CollatzResearch.WordTrace tailWord_1033603 prefixEnd_1033603 353823429952816504806035 := by
  unfold tailWord_1033603
  simp only [CollatzResearch.WordTrace]
  refine ⟨37698598474440331183609463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25132398982960220789072975 37698598474440331183609463)
  ·
    refine ⟨56547897711660496775414195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37698598474440331183609463 56547897711660496775414195)
    ·
      refine ⟨84821846567490745163121293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56547897711660496775414195 84821846567490745163121293)
      ·
        refine ⟨31808192462809029436170485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84821846567490745163121293 31808192462809029436170485)
        ·
          refine ⟨2982018043388346509640983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31808192462809029436170485 2982018043388346509640983)
          ·
            refine ⟨4473027065082519764461475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982018043388346509640983 4473027065082519764461475)
            ·
              refine ⟨6709540597623779646692213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473027065082519764461475 6709540597623779646692213)
              ·
                refine ⟨629019431027229341877395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6709540597623779646692213 629019431027229341877395)
                ·
                  refine ⟨943529146540844012816093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629019431027229341877395 943529146540844012816093)
                  ·
                    refine ⟨353823429952816504806035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943529146540844012816093 353823429952816504806035)
                    ·
                      rfl

theorem cell22_1033603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 3].length) (baseStart_1033603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033603 prefixEnd_1033603 := by exact prefixLift 1033603
  have htrace : WordTrace (prefixWord ++ tailWord_1033603) baseStart_1033603 baseEnd_1033603 := by
    simpa [prefixWord, tailWord_1033603, baseEnd_1033603] using wordTrace_append hprefix tailTrace_1033603
  have hstable : (prefixWord ++ tailWord_1033603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033603).length < 2 ^ (prefixWord ++ tailWord_1033603).sum := by decide
  have hdescent : baseEnd_1033603 < baseStart_1033603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033620 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1033620 : Nat := 118140960795 + 1033620 * 2 ^ 59
def prefixEnd_1033620 : Nat := 4983230072969 + 3 ^ 40 * 1033620 * 2
def baseEnd_1033620 : Nat := 353829249400234127130983

theorem tailTrace_1033620 : CollatzResearch.WordTrace tailWord_1033620 prefixEnd_1033620 353829249400234127130983 := by
  unfold tailWord_1033620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849609257689371543489157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25132812343585828724652209 18849609257689371543489157)
  ·
    refine ⟨3534301735816757164404217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18849609257689371543489157 3534301735816757164404217)
    ·
      refine ⟨2650726301862567873303163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534301735816757164404217 2650726301862567873303163)
      ·
        refine ⟨3976089452793851809954745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650726301862567873303163 3976089452793851809954745)
        ·
          refine ⟨2982067089595388857466059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976089452793851809954745 2982067089595388857466059)
          ·
            refine ⟨4473100634393083286199089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982067089595388857466059 4473100634393083286199089)
            ·
              refine ⟨3354825475794812464649317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473100634393083286199089 3354825475794812464649317)
              ·
                refine ⟨629029776711527337121747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3354825475794812464649317 629029776711527337121747)
                ·
                  refine ⟨943544665067291005682621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629029776711527337121747 943544665067291005682621)
                  ·
                    refine ⟨353829249400234127130983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943544665067291005682621 353829249400234127130983)
                    ·
                      rfl

theorem cell22_1033620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1033620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033620 prefixEnd_1033620 := by exact prefixLift 1033620
  have htrace : WordTrace (prefixWord ++ tailWord_1033620) baseStart_1033620 baseEnd_1033620 := by
    simpa [prefixWord, tailWord_1033620, baseEnd_1033620] using wordTrace_append hprefix tailTrace_1033620
  have hstable : (prefixWord ++ tailWord_1033620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033620).length < 2 ^ (prefixWord ++ tailWord_1033620).sum := by decide
  have hdescent : baseEnd_1033620 < baseStart_1033620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033644 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_1033644 : Nat := 118140960795 + 1033644 * 2 ^ 59
def prefixEnd_1033644 : Nat := 4983230072969 + 3 ^ 40 * 1033644 * 2
def baseEnd_1033644 : Nat := 117945821696902021510303

theorem tailTrace_1033644 : CollatzResearch.WordTrace tailWord_1033644 prefixEnd_1033644 117945821696902021510303 := by
  unfold tailWord_1033644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850046933645897592925993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25133395911527863457234657 18850046933645897592925993)
  ·
    refine ⟨14137535200234423194694495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18850046933645897592925993 14137535200234423194694495)
    ·
      refine ⟨21206302800351634792041743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14137535200234423194694495 21206302800351634792041743)
      ·
        refine ⟨31809454200527452188062615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21206302800351634792041743 31809454200527452188062615)
        ·
          refine ⟨47714181300791178282093923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31809454200527452188062615 47714181300791178282093923)
          ·
            refine ⟨71571271951186767423140885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47714181300791178282093923 71571271951186767423140885)
            ·
              refine ⟨3354903372711879722959729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71571271951186767423140885 3354903372711879722959729)
              ·
                refine ⟨2516177529533909792219797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354903372711879722959729 2516177529533909792219797)
                ·
                  refine ⟨117945821696902021510303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2516177529533909792219797 117945821696902021510303)
                  ·
                    rfl

theorem cell22_1033644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_1033644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033644 prefixEnd_1033644 := by exact prefixLift 1033644
  have htrace : WordTrace (prefixWord ++ tailWord_1033644) baseStart_1033644 baseEnd_1033644 := by
    simpa [prefixWord, tailWord_1033644, baseEnd_1033644] using wordTrace_append hprefix tailTrace_1033644
  have hstable : (prefixWord ++ tailWord_1033644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033644).length < 2 ^ (prefixWord ++ tailWord_1033644).sum := by decide
  have hdescent : baseEnd_1033644 < baseStart_1033644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033689 : List Nat := [1, 2, 1, 2, 4, 2, 1, 9]
def baseStart_1033689 : Nat := 118140960795 + 1033689 * 2 ^ 59
def prefixEnd_1033689 : Nat := 4983230072969 + 3 ^ 40 * 1033689 * 2
def baseEnd_1033689 : Nat := 39316985501148994128419

theorem tailTrace_1033689 : CollatzResearch.WordTrace tailWord_1033689 prefixEnd_1033689 39316985501148994128419 := by
  unfold tailWord_1033689
  simp only [CollatzResearch.WordTrace]
  refine ⟨37701735152128767871240121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25134490101419178580826747 37701735152128767871240121)
  ·
    refine ⟨28276301364096575903430091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37701735152128767871240121 28276301364096575903430091)
    ·
      refine ⟨42414452046144863855145137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28276301364096575903430091 42414452046144863855145137)
      ·
        refine ⟨31810839034608647891358853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42414452046144863855145137 31810839034608647891358853)
        ·
          refine ⟨5964532318989121479629785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31810839034608647891358853 5964532318989121479629785)
          ·
            refine ⟨4473399239241841109722339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5964532318989121479629785 4473399239241841109722339)
            ·
              refine ⟨6710098858862761664583509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473399239241841109722339 6710098858862761664583509)
              ·
                refine ⟨39316985501148994128419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6710098858862761664583509 39316985501148994128419)
                ·
                  rfl

theorem cell22_1033689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 9].length) (baseStart_1033689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033689 prefixEnd_1033689 := by exact prefixLift 1033689
  have htrace : WordTrace (prefixWord ++ tailWord_1033689) baseStart_1033689 baseEnd_1033689 := by
    simpa [prefixWord, tailWord_1033689, baseEnd_1033689] using wordTrace_append hprefix tailTrace_1033689
  have hstable : (prefixWord ++ tailWord_1033689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033689).length < 2 ^ (prefixWord ++ tailWord_1033689).sum := by decide
  have hdescent : baseEnd_1033689 < baseStart_1033689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033828 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_1033828 : Nat := 118140960795 + 1033828 * 2 ^ 59
def prefixEnd_1033828 : Nat := 4983230072969 + 3 ^ 40 * 1033828 * 2
def baseEnd_1033828 : Nat := 353900452050990917930345

theorem tailTrace_1033828 : CollatzResearch.WordTrace tailWord_1033828 prefixEnd_1033828 353900452050990917930345 := by
  unfold tailWord_1033828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853402449312597305275069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25137869932416796407033425 18853402449312597305275069)
  ·
    refine ⟨7070025918492223989478151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18853402449312597305275069 7070025918492223989478151)
    ·
      refine ⟨10605038877738335984217227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070025918492223989478151 10605038877738335984217227)
      ·
        refine ⟨15907558316607503976325841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605038877738335984217227 15907558316607503976325841)
        ·
          refine ⟨11930668737455627982244381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15907558316607503976325841 11930668737455627982244381)
          ·
            refine ⟨4474000776545860493341643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11930668737455627982244381 4474000776545860493341643)
            ·
              refine ⟨6711001164818790740012465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474000776545860493341643 6711001164818790740012465)
              ·
                refine ⟨5033250873614093055009349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711001164818790740012465 5033250873614093055009349)
                ·
                  refine ⟨943734538802642447814253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5033250873614093055009349 943734538802642447814253)
                  ·
                    refine ⟨353900452050990917930345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943734538802642447814253 353900452050990917930345)
                    ·
                      rfl

theorem cell22_1033828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_1033828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033828 prefixEnd_1033828 := by exact prefixLift 1033828
  have htrace : WordTrace (prefixWord ++ tailWord_1033828) baseStart_1033828 baseEnd_1033828 := by
    simpa [prefixWord, tailWord_1033828, baseEnd_1033828] using wordTrace_append hprefix tailTrace_1033828
  have hstable : (prefixWord ++ tailWord_1033828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033828).length < 2 ^ (prefixWord ++ tailWord_1033828).sum := by decide
  have hdescent : baseEnd_1033828 < baseStart_1033828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033845 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1033845 : Nat := 118140960795 + 1033845 * 2 ^ 59
def prefixEnd_1033845 : Nat := 4983230072969 + 3 ^ 40 * 1033845 * 2
def baseEnd_1033845 : Nat := 353906271498408540255293

theorem tailTrace_1033845 : CollatzResearch.WordTrace tailWord_1033845 prefixEnd_1033845 353906271498408540255293 := by
  unfold tailWord_1033845
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707424939563606513918989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25138283293042404342612659 37707424939563606513918989)
  ·
    refine ⟨14140284352336352442719621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37707424939563606513918989 14140284352336352442719621)
    ·
      refine ⟨2651303316063066083009929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14140284352336352442719621 2651303316063066083009929)
      ·
        refine ⟨1988477487047299562257447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2651303316063066083009929 1988477487047299562257447)
        ·
          refine ⟨2982716230570949343386171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988477487047299562257447 2982716230570949343386171)
          ·
            refine ⟨4474074345856424015079257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982716230570949343386171 4474074345856424015079257)
            ·
              refine ⟨3355555759392318011309443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474074345856424015079257 3355555759392318011309443)
              ·
                refine ⟨5033333639088477016964165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355555759392318011309443 5033333639088477016964165)
                ·
                  refine ⟨943750057329089440680781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5033333639088477016964165 943750057329089440680781)
                  ·
                    refine ⟨353906271498408540255293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943750057329089440680781 353906271498408540255293)
                    ·
                      rfl

theorem cell22_1033845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1033845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033845 prefixEnd_1033845 := by exact prefixLift 1033845
  have htrace : WordTrace (prefixWord ++ tailWord_1033845) baseStart_1033845 baseEnd_1033845 := by
    simpa [prefixWord, tailWord_1033845, baseEnd_1033845] using wordTrace_append hprefix tailTrace_1033845
  have hstable : (prefixWord ++ tailWord_1033845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033845).length < 2 ^ (prefixWord ++ tailWord_1033845).sum := by decide
  have hdescent : baseEnd_1033845 < baseStart_1033845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033896 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1033896 : Nat := 118140960795 + 1033896 * 2 ^ 59
def prefixEnd_1033896 : Nat := 4983230072969 + 3 ^ 40 * 1033896 * 2
def baseEnd_1033896 : Nat := 353923729840661407230137

theorem tailTrace_1033896 : CollatzResearch.WordTrace tailWord_1033896 prefixEnd_1033896 353923729840661407230137 := by
  unfold tailWord_1033896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854642531189421112012771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25139523374919228149350361 18854642531189421112012771)
  ·
    refine ⟨28281963796784131668019157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18854642531189421112012771 28281963796784131668019157)
    ·
      refine ⟨662858526487128085969199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28281963796784131668019157 662858526487128085969199)
      ·
        refine ⟨994287789730692128953799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662858526487128085969199 994287789730692128953799)
        ·
          refine ⟨1491431684596038193430699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994287789730692128953799 1491431684596038193430699)
          ·
            refine ⟨2237147526894057290146049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491431684596038193430699 2237147526894057290146049)
            ·
              refine ⟨1677860645170542967609537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237147526894057290146049 1677860645170542967609537)
              ·
                refine ⟨1258395483877907225707153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677860645170542967609537 1258395483877907225707153)
                ·
                  refine ⟨943796612908430419280365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1258395483877907225707153 943796612908430419280365)
                  ·
                    refine ⟨353923729840661407230137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943796612908430419280365 353923729840661407230137)
                    ·
                      rfl

theorem cell22_1033896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1033896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033896 prefixEnd_1033896 := by exact prefixLift 1033896
  have htrace : WordTrace (prefixWord ++ tailWord_1033896) baseStart_1033896 baseEnd_1033896 := by
    simpa [prefixWord, tailWord_1033896, baseEnd_1033896] using wordTrace_append hprefix tailTrace_1033896
  have hstable : (prefixWord ++ tailWord_1033896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033896).length < 2 ^ (prefixWord ++ tailWord_1033896).sum := by decide
  have hdescent : baseEnd_1033896 < baseStart_1033896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033903 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 5]
def baseStart_1033903 : Nat := 118140960795 + 1033903 * 2 ^ 59
def prefixEnd_1033903 : Nat := 4983230072969 + 3 ^ 40 * 1033903 * 2
def baseEnd_1033903 : Nat := 117975375361238574101705

theorem tailTrace_1033903 : CollatzResearch.WordTrace tailWord_1033903 prefixEnd_1033903 117975375361238574101705 := by
  unfold tailWord_1033903
  simp only [CollatzResearch.WordTrace]
  refine ⟨37709540373353482419530363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25139693582235654946353575 37709540373353482419530363)
  ·
    refine ⟨56564310560030223629295545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37709540373353482419530363 56564310560030223629295545)
    ·
      refine ⟨42423232920022667721971659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56564310560030223629295545 42423232920022667721971659)
      ·
        refine ⟨63634849380034001582957489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42423232920022667721971659 63634849380034001582957489)
        ·
          refine ⟨47726137035025501187218117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63634849380034001582957489 47726137035025501187218117)
          ·
            refine ⟨8948650694067281472603397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47726137035025501187218117 8948650694067281472603397)
            ·
              refine ⟨1677872005137615276113137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8948650694067281472603397 1677872005137615276113137)
              ·
                refine ⟨1258404003853211457084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677872005137615276113137 1258404003853211457084853)
                ·
                  refine ⟨117975375361238574101705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1258404003853211457084853 117975375361238574101705)
                  ·
                    rfl

theorem cell22_1033903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 5].length) (baseStart_1033903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033903 prefixEnd_1033903 := by exact prefixLift 1033903
  have htrace : WordTrace (prefixWord ++ tailWord_1033903) baseStart_1033903 baseEnd_1033903 := by
    simpa [prefixWord, tailWord_1033903, baseEnd_1033903] using wordTrace_append hprefix tailTrace_1033903
  have hstable : (prefixWord ++ tailWord_1033903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033903).length < 2 ^ (prefixWord ++ tailWord_1033903).sum := by decide
  have hdescent : baseEnd_1033903 < baseStart_1033903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033918 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1033918 : Nat := 118140960795 + 1033918 * 2 ^ 59
def prefixEnd_1033918 : Nat := 4983230072969 + 3 ^ 40 * 1033918 * 2
def baseEnd_1033918 : Nat := 353931260890260683180069

theorem tailTrace_1033918 : CollatzResearch.WordTrace tailWord_1033918 prefixEnd_1033918 353931260890260683180069 := by
  unfold tailWord_1033918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713760933537392497665801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25140058312199426654217605 4713760933537392497665801)
  ·
    refine ⟨3535320700153044373249351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4713760933537392497665801 3535320700153044373249351)
    ·
      refine ⟨5302981050229566559874027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535320700153044373249351 5302981050229566559874027)
      ·
        refine ⟨7954471575344349839811041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302981050229566559874027 7954471575344349839811041)
        ·
          refine ⟨5965853681508262379858281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954471575344349839811041 5965853681508262379858281)
          ·
            refine ⟨4474390261131196784893711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965853681508262379858281 4474390261131196784893711)
            ·
              refine ⟨6711585391696795177340567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474390261131196784893711 6711585391696795177340567)
              ·
                refine ⟨10067378087545192766010851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711585391696795177340567 10067378087545192766010851)
                ·
                  refine ⟨15101067131317789149016277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067378087545192766010851 15101067131317789149016277)
                  ·
                    refine ⟨353931260890260683180069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15101067131317789149016277 353931260890260683180069)
                    ·
                      rfl

theorem cell22_1033918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1033918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033918 prefixEnd_1033918 := by exact prefixLift 1033918
  have htrace : WordTrace (prefixWord ++ tailWord_1033918) baseStart_1033918 baseEnd_1033918 := by
    simpa [prefixWord, tailWord_1033918, baseEnd_1033918] using wordTrace_append hprefix tailTrace_1033918
  have hstable : (prefixWord ++ tailWord_1033918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033918).length < 2 ^ (prefixWord ++ tailWord_1033918).sum := by decide
  have hdescent : baseEnd_1033918 < baseStart_1033918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033965 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1033965 : Nat := 118140960795 + 1033965 * 2 ^ 59
def prefixEnd_1033965 : Nat := 4983230072969 + 3 ^ 40 * 1033965 * 2
def baseEnd_1033965 : Nat := 117982449983589409084975

theorem tailTrace_1033965 : CollatzResearch.WordTrace tailWord_1033965 prefixEnd_1033965 117982449983589409084975 := by
  unfold tailWord_1033965
  simp only [CollatzResearch.WordTrace]
  refine ⟨37711801699128867008287349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25141201132752578005524899 37711801699128867008287349)
  ·
    refine ⟨3535481409293331282026939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37711801699128867008287349 3535481409293331282026939)
    ·
      refine ⟨5303222113939996923040409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535481409293331282026939 5303222113939996923040409)
      ·
        refine ⟨3977416585454997692280307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5303222113939996923040409 3977416585454997692280307)
        ·
          refine ⟨5966124878182496538420461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977416585454997692280307 5966124878182496538420461)
          ·
            refine ⟨2237296829318436201907673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5966124878182496538420461 2237296829318436201907673)
            ·
              refine ⟨1677972621988827151430755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237296829318436201907673 1677972621988827151430755)
              ·
                refine ⟨2516958932983240727146133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677972621988827151430755 2516958932983240727146133)
                ·
                  refine ⟨117982449983589409084975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2516958932983240727146133 117982449983589409084975)
                  ·
                    rfl

theorem cell22_1033965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1033965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1033965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1033965 prefixEnd_1033965 := by exact prefixLift 1033965
  have htrace : WordTrace (prefixWord ++ tailWord_1033965) baseStart_1033965 baseEnd_1033965 := by
    simpa [prefixWord, tailWord_1033965, baseEnd_1033965] using wordTrace_append hprefix tailTrace_1033965
  have hstable : (prefixWord ++ tailWord_1033965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033965).length < 2 ^ (prefixWord ++ tailWord_1033965).sum := by decide
  have hdescent : baseEnd_1033965 < baseStart_1033965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034076 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1034076 : Nat := 118140960795 + 1034076 * 2 ^ 59
def prefixEnd_1034076 : Nat := 4983230072969 + 3 ^ 40 * 1034076 * 2
def baseEnd_1034076 : Nat := 353985347519200937729585

theorem tailTrace_1034076 : CollatzResearch.WordTrace tailWord_1034076 prefixEnd_1034076 353985347519200937729585 := by
  unfold tailWord_1034076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18857925100863366482789041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25143900134484488643718721 18857925100863366482789041)
  ·
    refine ⟨14143443825647524862091781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18857925100863366482789041 14143443825647524862091781)
    ·
      refine ⟨2651895717308910911642209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14143443825647524862091781 2651895717308910911642209)
      ·
        refine ⟨1988921787981683183731657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2651895717308910911642209 1988921787981683183731657)
        ·
          refine ⟨1491691340986262387798743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988921787981683183731657 1491691340986262387798743)
          ·
            refine ⟨2237537011479393581698115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491691340986262387798743 2237537011479393581698115)
            ·
              refine ⟨3356305517219090372547173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237537011479393581698115 3356305517219090372547173)
              ·
                refine ⟨629307284478579444852595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3356305517219090372547173 629307284478579444852595)
                ·
                  refine ⟨943960926717869167278893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629307284478579444852595 943960926717869167278893)
                  ·
                    refine ⟨353985347519200937729585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943960926717869167278893 353985347519200937729585)
                    ·
                      rfl

theorem cell22_1034076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1034076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034076 prefixEnd_1034076 := by exact prefixLift 1034076
  have htrace : WordTrace (prefixWord ++ tailWord_1034076) baseStart_1034076 baseEnd_1034076 := by
    simpa [prefixWord, tailWord_1034076, baseEnd_1034076] using wordTrace_append hprefix tailTrace_1034076
  have hstable : (prefixWord ++ tailWord_1034076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034076).length < 2 ^ (prefixWord ++ tailWord_1034076).sum := by decide
  have hdescent : baseEnd_1034076 < baseStart_1034076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034115 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_1034115 : Nat := 118140960795 + 1034115 * 2 ^ 59
def prefixEnd_1034115 : Nat := 4983230072969 + 3 ^ 40 * 1034115 * 2
def baseEnd_1034115 : Nat := 353998698016217836004465

theorem tailTrace_1034115 : CollatzResearch.WordTrace tailWord_1034115 prefixEnd_1034115 353998698016217836004465 := by
  unfold tailWord_1034115
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717272648585442626247799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25144848432390295084165199 37717272648585442626247799)
  ·
    refine ⟨56575908972878163939371699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37717272648585442626247799 56575908972878163939371699)
    ·
      refine ⟨84863863459317245909057549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56575908972878163939371699 84863863459317245909057549)
      ·
        refine ⟨31823948797243967215896581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84863863459317245909057549 31823948797243967215896581)
        ·
          refine ⟨5966990399483243852980609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31823948797243967215896581 5966990399483243852980609)
          ·
            refine ⟨4475242799612432889735457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5966990399483243852980609 4475242799612432889735457)
            ·
              refine ⟨3356432099709324667301593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4475242799612432889735457 3356432099709324667301593)
              ·
                refine ⟨2517324074781993500476195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356432099709324667301593 2517324074781993500476195)
                ·
                  refine ⟨3775986112172990250714293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517324074781993500476195 3775986112172990250714293)
                  ·
                    refine ⟨353998698016217836004465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3775986112172990250714293 353998698016217836004465)
                    ·
                      rfl

theorem cell22_1034115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_1034115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034115 prefixEnd_1034115 := by exact prefixLift 1034115
  have htrace : WordTrace (prefixWord ++ tailWord_1034115) baseStart_1034115 baseEnd_1034115 := by
    simpa [prefixWord, tailWord_1034115, baseEnd_1034115] using wordTrace_append hprefix tailTrace_1034115
  have hstable : (prefixWord ++ tailWord_1034115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034115).length < 2 ^ (prefixWord ++ tailWord_1034115).sum := by decide
  have hdescent : baseEnd_1034115 < baseStart_1034115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034117 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 4]
def baseStart_1034117 : Nat := 118140960795 + 1034117 * 2 ^ 59
def prefixEnd_1034117 : Nat := 4983230072969 + 3 ^ 40 * 1034117 * 2
def baseEnd_1034117 : Nat := 117999794219030165818153

theorem tailTrace_1034117 : CollatzResearch.WordTrace tailWord_1034117 prefixEnd_1034117 117999794219030165818153 := by
  unfold tailWord_1034117
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717345594578196967820605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25144897063052131311880403 37717345594578196967820605)
  ·
    refine ⟨14144004597966823862932727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37717345594578196967820605 14144004597966823862932727)
    ·
      refine ⟨21216006896950235794399091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14144004597966823862932727 21216006896950235794399091)
      ·
        refine ⟨31824010345425353691598637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216006896950235794399091 31824010345425353691598637)
        ·
          refine ⟨11934003879534507634349489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31824010345425353691598637 11934003879534507634349489)
          ·
            refine ⟨8950502909650880725762117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11934003879534507634349489 8950502909650880725762117)
            ·
              refine ⟨1678219295559540136080397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8950502909650880725762117 1678219295559540136080397)
              ·
                refine ⟨629332235834827551030149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1678219295559540136080397 629332235834827551030149)
                ·
                  refine ⟨117999794219030165818153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629332235834827551030149 117999794219030165818153)
                  ·
                    rfl

theorem cell22_1034117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_1034117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034117 prefixEnd_1034117 := by exact prefixLift 1034117
  have htrace : WordTrace (prefixWord ++ tailWord_1034117) baseStart_1034117 baseEnd_1034117 := by
    simpa [prefixWord, tailWord_1034117, baseEnd_1034117] using wordTrace_append hprefix tailTrace_1034117
  have hstable : (prefixWord ++ tailWord_1034117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034117).length < 2 ^ (prefixWord ++ tailWord_1034117).sum := by decide
  have hdescent : baseEnd_1034117 < baseStart_1034117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034190 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_1034190 : Nat := 118140960795 + 1034190 * 2 ^ 59
def prefixEnd_1034190 : Nat := 4983230072969 + 3 ^ 40 * 1034190 * 2
def baseEnd_1034190 : Nat := 118008124016314213459745

theorem tailTrace_1034190 : CollatzResearch.WordTrace tailWord_1034190 prefixEnd_1034190 118008124016314213459745 := by
  unfold tailWord_1034190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715001015414216304403503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25146672082209153623485349 4715001015414216304403503)
  ·
    refine ⟨7072501523121324456605255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4715001015414216304403503 7072501523121324456605255)
    ·
      refine ⟨10608752284681986684907883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7072501523121324456605255 10608752284681986684907883)
      ·
        refine ⟨15913128427022980027361825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608752284681986684907883 15913128427022980027361825)
        ·
          refine ⟨11934846320267235020521369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15913128427022980027361825 11934846320267235020521369)
          ·
            refine ⟨8951134740200426265391027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11934846320267235020521369 8951134740200426265391027)
            ·
              refine ⟨13426702110300639398086541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951134740200426265391027 13426702110300639398086541)
              ·
                refine ⟨5035013291362739774282453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13426702110300639398086541 5035013291362739774282453)
                ·
                  refine ⟨118008124016314213459745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5035013291362739774282453 118008124016314213459745)
                  ·
                    rfl

theorem cell22_1034190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_1034190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034190 prefixEnd_1034190 := by exact prefixLift 1034190
  have htrace : WordTrace (prefixWord ++ tailWord_1034190) baseStart_1034190 baseEnd_1034190 := by
    simpa [prefixWord, tailWord_1034190, baseEnd_1034190] using wordTrace_append hprefix tailTrace_1034190
  have hstable : (prefixWord ++ tailWord_1034190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034190).length < 2 ^ (prefixWord ++ tailWord_1034190).sum := by decide
  have hdescent : baseEnd_1034190 < baseStart_1034190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034207 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 5]
def baseStart_1034207 : Nat := 118140960795 + 1034207 * 2 ^ 59
def prefixEnd_1034207 : Nat := 4983230072969 + 3 ^ 40 * 1034207 * 2
def baseEnd_1034207 : Nat := 118010063832120087568061

theorem tailTrace_1034207 : CollatzResearch.WordTrace tailWord_1034207 prefixEnd_1034207 118010063832120087568061 := by
  unfold tailWord_1034207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37720628164252142338596875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25147085442834761559064583 37720628164252142338596875)
  ·
    refine ⟨56580942246378213507895313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37720628164252142338596875 56580942246378213507895313)
    ·
      refine ⟨42435706684783660130921485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56580942246378213507895313 42435706684783660130921485)
      ·
        refine ⟨15913390006793872549095557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42435706684783660130921485 15913390006793872549095557)
        ·
          refine ⟨2983760626273851102955417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15913390006793872549095557 2983760626273851102955417)
          ·
            refine ⟨2237820469705388327216563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983760626273851102955417 2237820469705388327216563)
            ·
              refine ⟨3356730704558082490824845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237820469705388327216563 3356730704558082490824845)
              ·
                refine ⟨1258774014209280934059317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3356730704558082490824845 1258774014209280934059317)
                ·
                  refine ⟨118010063832120087568061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1258774014209280934059317 118010063832120087568061)
                  ·
                    rfl

theorem cell22_1034207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 5].length) (baseStart_1034207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034207 prefixEnd_1034207 := by exact prefixLift 1034207
  have htrace : WordTrace (prefixWord ++ tailWord_1034207) baseStart_1034207 baseEnd_1034207 := by
    simpa [prefixWord, tailWord_1034207, baseEnd_1034207] using wordTrace_append hprefix tailTrace_1034207
  have hstable : (prefixWord ++ tailWord_1034207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034207).length < 2 ^ (prefixWord ++ tailWord_1034207).sum := by decide
  have hdescent : baseEnd_1034207 < baseStart_1034207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034237 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1034237 : Nat := 118140960795 + 1034237 * 2 ^ 59
def prefixEnd_1034237 : Nat := 4983230072969 + 3 ^ 40 * 1034237 * 2
def baseEnd_1034237 : Nat := 354040461109450184454091

theorem tailTrace_1034237 : CollatzResearch.WordTrace tailWord_1034237 prefixEnd_1034237 354040461109450184454091 := by
  unfold tailWord_1034237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37721722354143457462188965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25147814902762304974792643 37721722354143457462188965)
  ·
    refine ⟨7072822941401898274160431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37721722354143457462188965 7072822941401898274160431)
    ·
      refine ⟨10609234412102847411240647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7072822941401898274160431 10609234412102847411240647)
      ·
        refine ⟨15913851618154271116860971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609234412102847411240647 15913851618154271116860971)
        ·
          refine ⟨23870777427231406675291457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15913851618154271116860971 23870777427231406675291457)
          ·
            refine ⟨17903083070423555006468593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23870777427231406675291457 17903083070423555006468593)
            ·
              refine ⟨13427312302817666254851445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17903083070423555006468593 13427312302817666254851445)
              ·
                refine ⟨1258810528389156211392323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13427312302817666254851445 1258810528389156211392323)
                ·
                  refine ⟨1888215792583734317088485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258810528389156211392323 1888215792583734317088485)
                  ·
                    refine ⟨354040461109450184454091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888215792583734317088485 354040461109450184454091)
                    ·
                      rfl

theorem cell22_1034237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1034237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034237 prefixEnd_1034237 := by exact prefixLift 1034237
  have htrace : WordTrace (prefixWord ++ tailWord_1034237) baseStart_1034237 baseEnd_1034237 := by
    simpa [prefixWord, tailWord_1034237, baseEnd_1034237] using wordTrace_append hprefix tailTrace_1034237
  have hstable : (prefixWord ++ tailWord_1034237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034237).length < 2 ^ (prefixWord ++ tailWord_1034237).sum := by decide
  have hdescent : baseEnd_1034237 < baseStart_1034237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034265 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_1034265 : Nat := 118140960795 + 1034265 * 2 ^ 59
def prefixEnd_1034265 : Nat := 4983230072969 + 3 ^ 40 * 1034265 * 2
def baseEnd_1034265 : Nat := 354050046081667444754005

theorem tailTrace_1034265 : CollatzResearch.WordTrace tailWord_1034265 prefixEnd_1034265 354050046081667444754005 := by
  unfold tailWord_1034265
  simp only [CollatzResearch.WordTrace]
  refine ⟨37722743598042018244208249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25148495732028012162805499 37722743598042018244208249)
  ·
    refine ⟨28292057698531513683156187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37722743598042018244208249 28292057698531513683156187)
    ·
      refine ⟨42438086547797270524734281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28292057698531513683156187 42438086547797270524734281)
      ·
        refine ⟨31828564910847952893550711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42438086547797270524734281 31828564910847952893550711)
        ·
          refine ⟨47742847366271929340326067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31828564910847952893550711 47742847366271929340326067)
          ·
            refine ⟨71614271049407894010489101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47742847366271929340326067 71614271049407894010489101)
            ·
              refine ⟨26855351643527960253933413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71614271049407894010489101 26855351643527960253933413)
              ·
                refine ⟨5035378433161492547612515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26855351643527960253933413 5035378433161492547612515)
                ·
                  refine ⟨7553067649742238821418773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035378433161492547612515 7553067649742238821418773)
                  ·
                    refine ⟨354050046081667444754005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7553067649742238821418773 354050046081667444754005)
                    ·
                      rfl

theorem cell22_1034265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_1034265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034265 prefixEnd_1034265 := by exact prefixLift 1034265
  have htrace : WordTrace (prefixWord ++ tailWord_1034265) baseStart_1034265 baseEnd_1034265 := by
    simpa [prefixWord, tailWord_1034265, baseEnd_1034265] using wordTrace_append hprefix tailTrace_1034265
  have hstable : (prefixWord ++ tailWord_1034265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034265).length < 2 ^ (prefixWord ++ tailWord_1034265).sum := by decide
  have hdescent : baseEnd_1034265 < baseStart_1034265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034286 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_1034286 : Nat := 118140960795 + 1034286 * 2 ^ 59
def prefixEnd_1034286 : Nat := 4983230072969 + 3 ^ 40 * 1034286 * 2
def baseEnd_1034286 : Nat := 118019078270276796659647

theorem tailTrace_1034286 : CollatzResearch.WordTrace tailWord_1034286 prefixEnd_1034286 118019078270276796659647 := by
  unfold tailWord_1034286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715438691370742353840339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25149006353977292553815141 4715438691370742353840339)
  ·
    refine ⟨7073158037056113530760509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4715438691370742353840339 7073158037056113530760509)
    ·
      refine ⟨2652434263896042574035191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7073158037056113530760509 2652434263896042574035191)
      ·
        refine ⟨3978651395844063861052787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652434263896042574035191 3978651395844063861052787)
        ·
          refine ⟨5967977093766095791579181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978651395844063861052787 5967977093766095791579181)
          ·
            refine ⟨2237991410162285921842193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5967977093766095791579181 2237991410162285921842193)
            ·
              refine ⟨1678493557621714441381645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237991410162285921842193 1678493557621714441381645)
              ·
                refine ⟨629435084108142915518117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1678493557621714441381645 629435084108142915518117)
                ·
                  refine ⟨118019078270276796659647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629435084108142915518117 118019078270276796659647)
                  ·
                    rfl

theorem cell22_1034286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_1034286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034286 prefixEnd_1034286 := by exact prefixLift 1034286
  have htrace : WordTrace (prefixWord ++ tailWord_1034286) baseStart_1034286 baseEnd_1034286 := by
    simpa [prefixWord, tailWord_1034286, baseEnd_1034286] using wordTrace_append hprefix tailTrace_1034286
  have hstable : (prefixWord ++ tailWord_1034286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034286).length < 2 ^ (prefixWord ++ tailWord_1034286).sum := by decide
  have hdescent : baseEnd_1034286 < baseStart_1034286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034297 : List Nat := [1, 2, 1, 5, 3, 1, 9]
def baseStart_1034297 : Nat := 118140960795 + 1034297 * 2 ^ 59
def prefixEnd_1034297 : Nat := 4983230072969 + 3 ^ 40 * 1034297 * 2
def baseEnd_1034297 : Nat := 13113370382801112146441

theorem tailTrace_1034297 : CollatzResearch.WordTrace tailWord_1034297 prefixEnd_1034297 13113370382801112146441 := by
  unfold tailWord_1034297
  simp only [CollatzResearch.WordTrace]
  refine ⟨37723910733926087709373145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25149273822617391806248763 37723910733926087709373145)
  ·
    refine ⟨28292933050444565782029859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37723910733926087709373145 28292933050444565782029859)
    ·
      refine ⟨42439399575666848673044789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28292933050444565782029859 42439399575666848673044789)
      ·
        refine ⟨3978693710218767063097949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42439399575666848673044789 3978693710218767063097949)
        ·
          refine ⟨1492010141332037648661731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3978693710218767063097949 1492010141332037648661731)
          ·
            refine ⟨2238015211998056472992597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492010141332037648661731 2238015211998056472992597)
            ·
              refine ⟨13113370382801112146441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2238015211998056472992597 13113370382801112146441)
              ·
                rfl

theorem cell22_1034297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 9].length) (baseStart_1034297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034297 prefixEnd_1034297 := by exact prefixLift 1034297
  have htrace : WordTrace (prefixWord ++ tailWord_1034297) baseStart_1034297 baseEnd_1034297 := by
    simpa [prefixWord, tailWord_1034297, baseEnd_1034297] using wordTrace_append hprefix tailTrace_1034297
  have hstable : (prefixWord ++ tailWord_1034297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034297).length < 2 ^ (prefixWord ++ tailWord_1034297).sum := by decide
  have hdescent : baseEnd_1034297 < baseStart_1034297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034376 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_1034376 : Nat := 118140960795 + 1034376 * 2 ^ 59
def prefixEnd_1034376 : Nat := 4983230072969 + 3 ^ 40 * 1034376 * 2
def baseEnd_1034376 : Nat := 118029347883366718409555

theorem tailTrace_1034376 : CollatzResearch.WordTrace tailWord_1034376 prefixEnd_1034376 118029347883366718409555 := by
  unfold tailWord_1034376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863396050319942100749491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25151194733759922800999321 18863396050319942100749491)
  ·
    refine ⟨28295094075479913151124237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18863396050319942100749491 28295094075479913151124237)
    ·
      refine ⟨10610660278304967431671589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28295094075479913151124237 10610660278304967431671589)
      ·
        refine ⟨1989498802182181393438423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10610660278304967431671589 1989498802182181393438423)
        ·
          refine ⟨2984248203273272090157635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989498802182181393438423 2984248203273272090157635)
          ·
            refine ⟨4476372304909908135236453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984248203273272090157635 4476372304909908135236453)
            ·
              refine ⟨839319807170607775356835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4476372304909908135236453 839319807170607775356835)
              ·
                refine ⟨1258979710755911663035253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839319807170607775356835 1258979710755911663035253)
                ·
                  refine ⟨118029347883366718409555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1258979710755911663035253 118029347883366718409555)
                  ·
                    rfl

theorem cell22_1034376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_1034376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034376 prefixEnd_1034376 := by exact prefixLift 1034376
  have htrace : WordTrace (prefixWord ++ tailWord_1034376) baseStart_1034376 baseEnd_1034376 := by
    simpa [prefixWord, tailWord_1034376, baseEnd_1034376] using wordTrace_append hprefix tailTrace_1034376
  have hstable : (prefixWord ++ tailWord_1034376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034376).length < 2 ^ (prefixWord ++ tailWord_1034376).sum := by decide
  have hdescent : baseEnd_1034376 < baseStart_1034376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034414 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1034414 : Nat := 118140960795 + 1034414 * 2 ^ 59
def prefixEnd_1034414 : Nat := 4983230072969 + 3 ^ 40 * 1034414 * 2
def baseEnd_1034414 : Nat := 354101051826680722778549

theorem tailTrace_1034414 : CollatzResearch.WordTrace tailWord_1034414 prefixEnd_1034414 354101051826680722778549 := by
  unfold tailWord_1034414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716022259312777086422787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25152118716334811127588197 4716022259312777086422787)
  ·
    refine ⟨7074033388969165629634181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716022259312777086422787 7074033388969165629634181)
    ·
      refine ⟨1326381260431718555556409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7074033388969165629634181 1326381260431718555556409)
      ·
        refine ⟨994785945323788916667307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1326381260431718555556409 994785945323788916667307)
        ·
          refine ⟨1492178917985683375000961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994785945323788916667307 1492178917985683375000961)
          ·
            refine ⟨1119134188489262531250721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492178917985683375000961 1119134188489262531250721)
            ·
              refine ⟨839350641366946898438041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119134188489262531250721 839350641366946898438041)
              ·
                refine ⟨629512981025210173828531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839350641366946898438041 629512981025210173828531)
                ·
                  refine ⟨944269471537815260742797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629512981025210173828531 944269471537815260742797)
                  ·
                    refine ⟨354101051826680722778549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944269471537815260742797 354101051826680722778549)
                    ·
                      rfl

theorem cell22_1034414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1034414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034414 prefixEnd_1034414 := by exact prefixLift 1034414
  have htrace : WordTrace (prefixWord ++ tailWord_1034414) baseStart_1034414 baseEnd_1034414 := by
    simpa [prefixWord, tailWord_1034414, baseEnd_1034414] using wordTrace_append hprefix tailTrace_1034414
  have hstable : (prefixWord ++ tailWord_1034414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034414).length < 2 ^ (prefixWord ++ tailWord_1034414).sum := by decide
  have hdescent : baseEnd_1034414 < baseStart_1034414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034436 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1034436 : Nat := 118140960795 + 1034436 * 2 ^ 59
def prefixEnd_1034436 : Nat := 4983230072969 + 3 ^ 40 * 1034436 * 2
def baseEnd_1034436 : Nat := 354108582876279998728481

theorem tailTrace_1034436 : CollatzResearch.WordTrace tailWord_1034436 prefixEnd_1034436 354108582876279998728481 := by
  unfold tailWord_1034436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864490240211257224341581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25152653653615009632455441 18864490240211257224341581)
  ·
    refine ⟨7074183840079221459128093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18864490240211257224341581 7074183840079221459128093)
    ·
      refine ⟨2652818940029708047173035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7074183840079221459128093 2652818940029708047173035)
      ·
        refine ⟨3979228410044562070759553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652818940029708047173035 3979228410044562070759553)
        ·
          refine ⟨2984421307533421553069665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979228410044562070759553 2984421307533421553069665)
          ·
            refine ⟨2238315980650066164802249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984421307533421553069665 2238315980650066164802249)
            ·
              refine ⟨1678736985487549623601687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238315980650066164802249 1678736985487549623601687)
              ·
                refine ⟨2518105478231324435402531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678736985487549623601687 2518105478231324435402531)
                ·
                  refine ⟨3777158217346986653103797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518105478231324435402531 3777158217346986653103797)
                  ·
                    refine ⟨354108582876279998728481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3777158217346986653103797 354108582876279998728481)
                    ·
                      rfl

theorem cell22_1034436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1034436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034436 prefixEnd_1034436 := by exact prefixLift 1034436
  have htrace : WordTrace (prefixWord ++ tailWord_1034436) baseStart_1034436 baseEnd_1034436 := by
    simpa [prefixWord, tailWord_1034436, baseEnd_1034436] using wordTrace_append hprefix tailTrace_1034436
  have hstable : (prefixWord ++ tailWord_1034436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034436).length < 2 ^ (prefixWord ++ tailWord_1034436).sum := by decide
  have hdescent : baseEnd_1034436 < baseStart_1034436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034464 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_1034464 : Nat := 118140960795 + 1034464 * 2 ^ 59
def prefixEnd_1034464 : Nat := 4983230072969 + 3 ^ 40 * 1034464 * 2
def baseEnd_1034464 : Nat := 354118167848497259028395

theorem tailTrace_1034464 : CollatzResearch.WordTrace tailWord_1034464 prefixEnd_1034464 354118167848497259028395 := by
  unfold tailWord_1034464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865000862160537615351223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25153334482880716820468297 18865000862160537615351223)
  ·
    refine ⟨28297501293240806423026835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18865000862160537615351223 28297501293240806423026835)
    ·
      refine ⟨42446251939861209634540253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28297501293240806423026835 42446251939861209634540253)
      ·
        refine ⟨15917344477447953612952595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42446251939861209634540253 15917344477447953612952595)
        ·
          refine ⟨23876016716171930419428893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15917344477447953612952595 23876016716171930419428893)
          ·
            refine ⟨8953506268564473907285835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23876016716171930419428893 8953506268564473907285835)
            ·
              refine ⟨13430259402846710860928753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953506268564473907285835 13430259402846710860928753)
              ·
                refine ⟨10072694552135033145696565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13430259402846710860928753 10072694552135033145696565)
                ·
                  refine ⟨944315114262659357409053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10072694552135033145696565 944315114262659357409053)
                  ·
                    refine ⟨354118167848497259028395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944315114262659357409053 354118167848497259028395)
                    ·
                      rfl

theorem cell22_1034464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_1034464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034464 prefixEnd_1034464 := by exact prefixLift 1034464
  have htrace : WordTrace (prefixWord ++ tailWord_1034464) baseStart_1034464 baseEnd_1034464 := by
    simpa [prefixWord, tailWord_1034464, baseEnd_1034464] using wordTrace_append hprefix tailTrace_1034464
  have hstable : (prefixWord ++ tailWord_1034464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034464).length < 2 ^ (prefixWord ++ tailWord_1034464).sum := by decide
  have hdescent : baseEnd_1034464 < baseStart_1034464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034498 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1034498 : Nat := 118140960795 + 1034498 * 2 ^ 59
def prefixEnd_1034498 : Nat := 4983230072969 + 3 ^ 40 * 1034498 * 2
def baseEnd_1034498 : Nat := 354129806743332503678291

theorem tailTrace_1034498 : CollatzResearch.WordTrace tailWord_1034498 prefixEnd_1034498 354129806743332503678291 := by
  unfold tailWord_1034498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432810451549474759360037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25154161204131932691626765 9432810451549474759360037)
  ·
    refine ⟨1768651959665526517380007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9432810451549474759360037 1768651959665526517380007)
    ·
      refine ⟨2652977939498289776070011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768651959665526517380007 2652977939498289776070011)
      ·
        refine ⟨3979466909247434664105017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652977939498289776070011 3979466909247434664105017)
        ·
          refine ⟨2984600181935575998078763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979466909247434664105017 2984600181935575998078763)
          ·
            refine ⟨4476900272903363997118145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984600181935575998078763 4476900272903363997118145)
            ·
              refine ⟨3357675204677522997838609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476900272903363997118145 3357675204677522997838609)
              ·
                refine ⟨2518256403508142248378957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3357675204677522997838609 2518256403508142248378957)
                ·
                  refine ⟨944346151315553343142109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2518256403508142248378957 944346151315553343142109)
                  ·
                    refine ⟨354129806743332503678291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944346151315553343142109 354129806743332503678291)
                    ·
                      rfl

theorem cell22_1034498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1034498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034498 prefixEnd_1034498 := by exact prefixLift 1034498
  have htrace : WordTrace (prefixWord ++ tailWord_1034498) baseStart_1034498 baseEnd_1034498 := by
    simpa [prefixWord, tailWord_1034498, baseEnd_1034498] using wordTrace_append hprefix tailTrace_1034498
  have hstable : (prefixWord ++ tailWord_1034498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034498).length < 2 ^ (prefixWord ++ tailWord_1034498).sum := by decide
  have hdescent : baseEnd_1034498 < baseStart_1034498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1034524 : Nat := 118140960795 + 1034524 * 2 ^ 59
def prefixEnd_1034524 : Nat := 4983230072969 + 3 ^ 40 * 1034524 * 2
def baseEnd_1034524 : Nat := 354138707074677102528211

theorem tailTrace_1034524 : CollatzResearch.WordTrace tailWord_1034524 prefixEnd_1034524 354138707074677102528211 := by
  unfold tailWord_1034524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18866095052051852738943313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25154793402735803651924417 18866095052051852738943313)
  ·
    refine ⟨14149571289038889554207485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18866095052051852738943313 14149571289038889554207485)
    ·
      refine ⟨5306089233389583582827807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14149571289038889554207485 5306089233389583582827807)
      ·
        refine ⟨7959133850084375374241711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306089233389583582827807 7959133850084375374241711)
        ·
          refine ⟨11938700775126563061362567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959133850084375374241711 11938700775126563061362567)
          ·
            refine ⟨17908051162689844592043851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938700775126563061362567 17908051162689844592043851)
            ·
              refine ⟨26862076744034766888065777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17908051162689844592043851 26862076744034766888065777)
              ·
                refine ⟨20146557558026075166049333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26862076744034766888065777 20146557558026075166049333)
                ·
                  refine ⟨1888739771064944546817125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20146557558026075166049333 1888739771064944546817125)
                  ·
                    refine ⟨354138707074677102528211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888739771064944546817125 354138707074677102528211)
                    ·
                      rfl

theorem cell22_1034524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1034524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034524 prefixEnd_1034524 := by exact prefixLift 1034524
  have htrace : WordTrace (prefixWord ++ tailWord_1034524) baseStart_1034524 baseEnd_1034524 := by
    simpa [prefixWord, tailWord_1034524, baseEnd_1034524] using wordTrace_append hprefix tailTrace_1034524
  have hstable : (prefixWord ++ tailWord_1034524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034524).length < 2 ^ (prefixWord ++ tailWord_1034524).sum := by decide
  have hdescent : baseEnd_1034524 < baseStart_1034524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034545 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 5]
def baseStart_1034545 : Nat := 118140960795 + 1034545 * 2 ^ 59
def prefixEnd_1034545 : Nat := 4983230072969 + 3 ^ 40 * 1034545 * 2
def baseEnd_1034545 : Nat := 118048631934613349251049

theorem tailTrace_1034545 : CollatzResearch.WordTrace tailWord_1034545 prefixEnd_1034545 118048631934613349251049 := by
  unfold tailWord_1034545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37732956037027626064401089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25155304024685084042934059 37732956037027626064401089)
  ·
    refine ⟨28299717027770719548300817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37732956037027626064401089 28299717027770719548300817)
    ·
      refine ⟨21224787770828039661225613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28299717027770719548300817 21224787770828039661225613)
      ·
        refine ⟨7959295414060514872959605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21224787770828039661225613 7959295414060514872959605)
        ·
          refine ⟨746183945068173269339963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7959295414060514872959605 746183945068173269339963)
          ·
            refine ⟨1119275917602259904009945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746183945068173269339963 1119275917602259904009945)
            ·
              refine ⟨839456938201694928007459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119275917602259904009945 839456938201694928007459)
              ·
                refine ⟨1259185407302542392011189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839456938201694928007459 1259185407302542392011189)
                ·
                  refine ⟨118048631934613349251049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259185407302542392011189 118048631934613349251049)
                  ·
                    rfl

theorem cell22_1034545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_1034545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034545 prefixEnd_1034545 := by exact prefixLift 1034545
  have htrace : WordTrace (prefixWord ++ tailWord_1034545) baseStart_1034545 baseEnd_1034545 := by
    simpa [prefixWord, tailWord_1034545, baseEnd_1034545] using wordTrace_append hprefix tailTrace_1034545
  have hstable : (prefixWord ++ tailWord_1034545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034545).length < 2 ^ (prefixWord ++ tailWord_1034545).sum := by decide
  have hdescent : baseEnd_1034545 < baseStart_1034545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034558 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1034558 : Nat := 118140960795 + 1034558 * 2 ^ 59
def prefixEnd_1034558 : Nat := 4983230072969 + 3 ^ 40 * 1034558 * 2
def baseEnd_1034558 : Nat := 354150345969512347178107

theorem tailTrace_1034558 : CollatzResearch.WordTrace tailWord_1034558 prefixEnd_1034558 354150345969512347178107 := by
  unfold tailWord_1034558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716678773247566160578041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25155620123987019523082885 4716678773247566160578041)
  ·
    refine ⟨3537509079935674620433531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4716678773247566160578041 3537509079935674620433531)
    ·
      refine ⟨5306263619903511930650297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3537509079935674620433531 5306263619903511930650297)
      ·
        refine ⟨3979697714927633947987723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5306263619903511930650297 3979697714927633947987723)
        ·
          refine ⟨5969546572391450921981585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979697714927633947987723 5969546572391450921981585)
          ·
            refine ⟨4477159929293588191486189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5969546572391450921981585 4477159929293588191486189)
            ·
              refine ⟨1678934973485095571807321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4477159929293588191486189 1678934973485095571807321)
              ·
                refine ⟨1259201230113821678855491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678934973485095571807321 1259201230113821678855491)
                ·
                  refine ⟨1888801845170732518283237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259201230113821678855491 1888801845170732518283237)
                  ·
                    refine ⟨354150345969512347178107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888801845170732518283237 354150345969512347178107)
                    ·
                      rfl

theorem cell22_1034558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1034558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034558 prefixEnd_1034558 := by exact prefixLift 1034558
  have htrace : WordTrace (prefixWord ++ tailWord_1034558) baseStart_1034558 baseEnd_1034558 := by
    simpa [prefixWord, tailWord_1034558, baseEnd_1034558] using wordTrace_append hprefix tailTrace_1034558
  have hstable : (prefixWord ++ tailWord_1034558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034558).length < 2 ^ (prefixWord ++ tailWord_1034558).sum := by decide
  have hdescent : baseEnd_1034558 < baseStart_1034558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034629 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1034629 : Nat := 118140960795 + 1034629 * 2 ^ 59
def prefixEnd_1034629 : Nat := 4983230072969 + 3 ^ 40 * 1034629 * 2
def baseEnd_1034629 : Nat := 118058216906830609550963

theorem tailTrace_1034629 : CollatzResearch.WordTrace tailWord_1034629 prefixEnd_1034629 118058216906830609550963 := by
  unfold tailWord_1034629
  simp only [CollatzResearch.WordTrace]
  refine ⟨37736019768723308410458941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25157346512482205606972627 37736019768723308410458941)
  ·
    refine ⟨14151007413271240653922103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37736019768723308410458941 14151007413271240653922103)
    ·
      refine ⟨21226511119906860980883155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14151007413271240653922103 21226511119906860980883155)
      ·
        refine ⟨31839766679860291471324733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21226511119906860980883155 31839766679860291471324733)
        ·
          refine ⟨11939912504947609301746775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31839766679860291471324733 11939912504947609301746775)
          ·
            refine ⟨17909868757421413952620163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11939912504947609301746775 17909868757421413952620163)
            ·
              refine ⟨26864803136132120928930245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17909868757421413952620163 26864803136132120928930245)
              ·
                refine ⟨5037150588024772674174421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26864803136132120928930245 5037150588024772674174421)
                ·
                  refine ⟨118058216906830609550963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5037150588024772674174421 118058216906830609550963)
                  ·
                    rfl

theorem cell22_1034629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1034629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034629 prefixEnd_1034629 := by exact prefixLift 1034629
  have htrace : WordTrace (prefixWord ++ tailWord_1034629) baseStart_1034629 baseEnd_1034629 := by
    simpa [prefixWord, tailWord_1034629, baseEnd_1034629] using wordTrace_append hprefix tailTrace_1034629
  have hstable : (prefixWord ++ tailWord_1034629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034629).length < 2 ^ (prefixWord ++ tailWord_1034629).sum := by decide
  have hdescent : baseEnd_1034629 < baseStart_1034629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034650 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_1034650 : Nat := 118140960795 + 1034650 * 2 ^ 59
def prefixEnd_1034650 : Nat := 4983230072969 + 3 ^ 40 * 1034650 * 2
def baseEnd_1034650 : Nat := 354181839449654773877825

theorem tailTrace_1034650 : CollatzResearch.WordTrace tailWord_1034650 prefixEnd_1034650 354181839449654773877825 := by
  unfold tailWord_1034650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434196425411807249243351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25157857134431485997982269 9434196425411807249243351)
  ·
    refine ⟨14151294638117710873865027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9434196425411807249243351 14151294638117710873865027)
    ·
      refine ⟨21226941957176566310797541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14151294638117710873865027 21226941957176566310797541)
      ·
        refine ⟨3980051616970606183274539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21226941957176566310797541 3980051616970606183274539)
        ·
          refine ⟨5970077425455909274911809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980051616970606183274539 5970077425455909274911809)
          ·
            refine ⟨4477558069091931956183857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5970077425455909274911809 4477558069091931956183857)
            ·
              refine ⟨3358168551818948967137893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477558069091931956183857 3358168551818948967137893)
              ·
                refine ⟨629656603466052931338355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3358168551818948967137893 629656603466052931338355)
                ·
                  refine ⟨944484905199079397007533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629656603466052931338355 944484905199079397007533)
                  ·
                    refine ⟨354181839449654773877825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944484905199079397007533 354181839449654773877825)
                    ·
                      rfl

theorem cell22_1034650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_1034650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034650 prefixEnd_1034650 := by exact prefixLift 1034650
  have htrace : WordTrace (prefixWord ++ tailWord_1034650) baseStart_1034650 baseEnd_1034650 := by
    simpa [prefixWord, tailWord_1034650, baseEnd_1034650] using wordTrace_append hprefix tailTrace_1034650
  have hstable : (prefixWord ++ tailWord_1034650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034650).length < 2 ^ (prefixWord ++ tailWord_1034650).sum := by decide
  have hdescent : baseEnd_1034650 < baseStart_1034650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034708 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1034708 : Nat := 118140960795 + 1034708 * 2 ^ 59
def prefixEnd_1034708 : Nat := 4983230072969 + 3 ^ 40 * 1034708 * 2
def baseEnd_1034708 : Nat := 118067231344987318642549

theorem tailTrace_1034708 : CollatzResearch.WordTrace tailWord_1034708 prefixEnd_1034708 118067231344987318642549 := by
  unfold tailWord_1034708
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869450567718552451292389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25159267423624736601723185 18869450567718552451292389)
  ·
    refine ⟨3538021981447228584617323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18869450567718552451292389 3538021981447228584617323)
    ·
      refine ⟨5307032972170842876925985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538021981447228584617323 5307032972170842876925985)
      ·
        refine ⟨3980274729128132157694489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5307032972170842876925985 3980274729128132157694489)
        ·
          refine ⟨2985206046846099118270867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3980274729128132157694489 2985206046846099118270867)
          ·
            refine ⟨4477809070269148677406301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985206046846099118270867 4477809070269148677406301)
            ·
              refine ⟨1679178401350930754027363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4477809070269148677406301 1679178401350930754027363)
              ·
                refine ⟨2518767602026396131041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679178401350930754027363 2518767602026396131041045)
                ·
                  refine ⟨118067231344987318642549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2518767602026396131041045 118067231344987318642549)
                  ·
                    rfl

theorem cell22_1034708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1034708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034708 prefixEnd_1034708 := by exact prefixLift 1034708
  have htrace : WordTrace (prefixWord ++ tailWord_1034708) baseStart_1034708 baseEnd_1034708 := by
    simpa [prefixWord, tailWord_1034708, baseEnd_1034708] using wordTrace_append hprefix tailTrace_1034708
  have hstable : (prefixWord ++ tailWord_1034708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034708).length < 2 ^ (prefixWord ++ tailWord_1034708).sum := by decide
  have hdescent : baseEnd_1034708 < baseStart_1034708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034721 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1034721 : Nat := 118140960795 + 1034721 * 2 ^ 59
def prefixEnd_1034721 : Nat := 4983230072969 + 3 ^ 40 * 1034721 * 2
def baseEnd_1034721 : Nat := 354206144200634255352607

theorem tailTrace_1034721 : CollatzResearch.WordTrace tailWord_1034721 prefixEnd_1034721 354206144200634255352607 := by
  unfold tailWord_1034721
  simp only [CollatzResearch.WordTrace]
  refine ⟨37739375284390008122808017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25159583522926672081872011 37739375284390008122808017)
  ·
    refine ⟨28304531463292506092106013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37739375284390008122808017 28304531463292506092106013)
    ·
      refine ⟨10614199298734689784539755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28304531463292506092106013 10614199298734689784539755)
      ·
        refine ⟨15921298948102034676809633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614199298734689784539755 15921298948102034676809633)
        ·
          refine ⟨11940974211076526007607225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15921298948102034676809633 11940974211076526007607225)
          ·
            refine ⟨8955730658307394505705419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11940974211076526007607225 8955730658307394505705419)
            ·
              refine ⟨13433595987461091758558129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955730658307394505705419 13433595987461091758558129)
              ·
                refine ⟨10075196990595818818918597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433595987461091758558129 10075196990595818818918597)
                ·
                  refine ⟨1889099435736716028547237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10075196990595818818918597 1889099435736716028547237)
                  ·
                    refine ⟨354206144200634255352607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1889099435736716028547237 354206144200634255352607)
                    ·
                      rfl

theorem cell22_1034721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1034721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034721 prefixEnd_1034721 := by exact prefixLift 1034721
  have htrace : WordTrace (prefixWord ++ tailWord_1034721) baseStart_1034721 baseEnd_1034721 := by
    simpa [prefixWord, tailWord_1034721, baseEnd_1034721] using wordTrace_append hprefix tailTrace_1034721
  have hstable : (prefixWord ++ tailWord_1034721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034721).length < 2 ^ (prefixWord ++ tailWord_1034721).sum := by decide
  have hdescent : baseEnd_1034721 < baseStart_1034721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034759 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 4]
def baseStart_1034759 : Nat := 118140960795 + 1034759 * 2 ^ 59
def prefixEnd_1034759 : Nat := 4983230072969 + 3 ^ 40 * 1034759 * 2
def baseEnd_1034759 : Nat := 118073050792404940967497

theorem tailTrace_1034759 : CollatzResearch.WordTrace tailWord_1034759 prefixEnd_1034759 118073050792404940967497 := by
  unfold tailWord_1034759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37740761258252340612691331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25160507505501560408460887 37740761258252340612691331)
  ·
    refine ⟨56611141887378510919036997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37740761258252340612691331 56611141887378510919036997)
    ·
      refine ⟨10614589103883470797319437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56611141887378510919036997 10614589103883470797319437)
      ·
        refine ⟨3980470913956301548994789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10614589103883470797319437 3980470913956301548994789)
        ·
          refine ⟨746338296366806540436523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3980470913956301548994789 746338296366806540436523)
          ·
            refine ⟨1119507444550209810654785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746338296366806540436523 1119507444550209810654785)
            ·
              refine ⟨839630583412657357991089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119507444550209810654785 839630583412657357991089)
              ·
                refine ⟨629722937559493018493317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839630583412657357991089 629722937559493018493317)
                ·
                  refine ⟨118073050792404940967497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629722937559493018493317 118073050792404940967497)
                  ·
                    rfl

theorem cell22_1034759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 4].length) (baseStart_1034759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034759 prefixEnd_1034759 := by exact prefixLift 1034759
  have htrace : WordTrace (prefixWord ++ tailWord_1034759) baseStart_1034759 baseEnd_1034759 := by
    simpa [prefixWord, tailWord_1034759, baseEnd_1034759] using wordTrace_append hprefix tailTrace_1034759
  have hstable : (prefixWord ++ tailWord_1034759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034759).length < 2 ^ (prefixWord ++ tailWord_1034759).sum := by decide
  have hdescent : baseEnd_1034759 < baseStart_1034759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034813 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1034813 : Nat := 118140960795 + 1034813 * 2 ^ 59
def prefixEnd_1034813 : Nat := 4983230072969 + 3 ^ 40 * 1034813 * 2
def baseEnd_1034813 : Nat := 354237637680776682052325

theorem tailTrace_1034813 : CollatzResearch.WordTrace tailWord_1034813 prefixEnd_1034813 354237637680776682052325 := by
  unfold tailWord_1034813
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742730800056707835157093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25161820533371138556771395 37742730800056707835157093)
  ·
    refine ⟨7076762025010632719091955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37742730800056707835157093 7076762025010632719091955)
    ·
      refine ⟨10615143037515949078637933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076762025010632719091955 10615143037515949078637933)
      ·
        refine ⟨3980678639068480904489225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10615143037515949078637933 3980678639068480904489225)
        ·
          refine ⟨2985508979301360678366919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3980678639068480904489225 2985508979301360678366919)
          ·
            refine ⟨4478263468952041017550379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985508979301360678366919 4478263468952041017550379)
            ·
              refine ⟨6717395203428061526325569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478263468952041017550379 6717395203428061526325569)
              ·
                refine ⟨5038046402571046144744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717395203428061526325569 5038046402571046144744177)
                ·
                  refine ⟨3778534801928284608558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038046402571046144744177 3778534801928284608558133)
                  ·
                    refine ⟨354237637680776682052325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3778534801928284608558133 354237637680776682052325)
                    ·
                      rfl

theorem cell22_1034813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1034813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034813 prefixEnd_1034813 := by exact prefixLift 1034813
  have htrace : WordTrace (prefixWord ++ tailWord_1034813) baseStart_1034813 baseEnd_1034813 := by
    simpa [prefixWord, tailWord_1034813, baseEnd_1034813] using wordTrace_append hprefix tailTrace_1034813
  have hstable : (prefixWord ++ tailWord_1034813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034813).length < 2 ^ (prefixWord ++ tailWord_1034813).sum := by decide
  have hdescent : baseEnd_1034813 < baseStart_1034813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034858 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1034858 : Nat := 118140960795 + 1034858 * 2 ^ 59
def prefixEnd_1034858 : Nat := 4983230072969 + 3 ^ 40 * 1034858 * 2
def baseEnd_1034858 : Nat := 354253042100411564677187

theorem tailTrace_1034858 : CollatzResearch.WordTrace tailWord_1034858 prefixEnd_1034858 354253042100411564677187 := by
  unfold tailWord_1034858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436093021223420130136307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25162914723262453680363485 9436093021223420130136307)
  ·
    refine ⟨14154139531835130195204461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9436093021223420130136307 14154139531835130195204461)
    ·
      refine ⟨5307802324438173823201673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14154139531835130195204461 5307802324438173823201673)
      ·
        refine ⟨3980851743328630367401255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5307802324438173823201673 3980851743328630367401255)
        ·
          refine ⟨5971277614992945551101883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980851743328630367401255 5971277614992945551101883)
          ·
            refine ⟨8956916422489418326652825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971277614992945551101883 8956916422489418326652825)
            ·
              refine ⟨6717687316867063744989619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8956916422489418326652825 6717687316867063744989619)
              ·
                refine ⟨10076530975300595617484429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717687316867063744989619 10076530975300595617484429)
                ·
                  refine ⟨3778699115737723356556661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10076530975300595617484429 3778699115737723356556661)
                  ·
                    refine ⟨354253042100411564677187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3778699115737723356556661 354253042100411564677187)
                    ·
                      rfl

theorem cell22_1034858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1034858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034858 prefixEnd_1034858 := by exact prefixLift 1034858
  have htrace : WordTrace (prefixWord ++ tailWord_1034858) baseStart_1034858 baseEnd_1034858 := by
    simpa [prefixWord, tailWord_1034858, baseEnd_1034858] using wordTrace_append hprefix tailTrace_1034858
  have hstable : (prefixWord ++ tailWord_1034858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034858).length < 2 ^ (prefixWord ++ tailWord_1034858).sum := by decide
  have hdescent : baseEnd_1034858 < baseStart_1034858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034860 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_1034860 : Nat := 118140960795 + 1034860 * 2 ^ 59
def prefixEnd_1034860 : Nat := 4983230072969 + 3 ^ 40 * 1034860 * 2
def baseEnd_1034860 : Nat := 118084575580428075375727

theorem tailTrace_1034860 : CollatzResearch.WordTrace tailWord_1034860 prefixEnd_1034860 118084575580428075375727 := by
  unfold tailWord_1034860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872222515443217431059017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25162963353924289908078689 18872222515443217431059017)
  ·
    refine ⟨14154166886582413073294263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18872222515443217431059017 14154166886582413073294263)
    ·
      refine ⟨21231250329873619609941395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154166886582413073294263 21231250329873619609941395)
      ·
        refine ⟨31846875494810429414912093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21231250329873619609941395 31846875494810429414912093)
        ·
          refine ⟨11942578310553911030592035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31846875494810429414912093 11942578310553911030592035)
          ·
            refine ⟨17913867465830866545888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942578310553911030592035 17913867465830866545888053)
            ·
              refine ⟨1679425074921643738677005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17913867465830866545888053 1679425074921643738677005)
              ·
                refine ⟨629784403095616402003877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679425074921643738677005 629784403095616402003877)
                ·
                  refine ⟨118084575580428075375727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629784403095616402003877 118084575580428075375727)
                  ·
                    rfl

theorem cell22_1034860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_1034860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034860 prefixEnd_1034860 := by exact prefixLift 1034860
  have htrace : WordTrace (prefixWord ++ tailWord_1034860) baseStart_1034860 baseEnd_1034860 := by
    simpa [prefixWord, tailWord_1034860, baseEnd_1034860] using wordTrace_append hprefix tailTrace_1034860
  have hstable : (prefixWord ++ tailWord_1034860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034860).length < 2 ^ (prefixWord ++ tailWord_1034860).sum := by decide
  have hdescent : baseEnd_1034860 < baseStart_1034860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034871 : List Nat := [1, 1, 3, 1, 1, 3, 12]
def baseStart_1034871 : Nat := 118140960795 + 1034871 * 2 ^ 59
def prefixEnd_1034871 : Nat := 4983230072969 + 3 ^ 40 * 1034871 * 2
def baseEnd_1034871 : Nat := 13120647861706809781561

theorem tailTrace_1034871 : CollatzResearch.WordTrace tailWord_1034871 prefixEnd_1034871 13120647861706809781561 := by
  unfold tailWord_1034871
  simp only [CollatzResearch.WordTrace]
  refine ⟨37744846233846583740768467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25163230822564389160512311 37744846233846583740768467)
  ·
    refine ⟨56617269350769875611152701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37744846233846583740768467 56617269350769875611152701)
    ·
      refine ⟨21231476006538703354182263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56617269350769875611152701 21231476006538703354182263)
      ·
        refine ⟨31847214009808055031273395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21231476006538703354182263 31847214009808055031273395)
        ·
          refine ⟨47770821014712082546910093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847214009808055031273395 47770821014712082546910093)
          ·
            refine ⟨17914057880517030955091285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47770821014712082546910093 17914057880517030955091285)
            ·
              refine ⟨13120647861706809781561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 17914057880517030955091285 13120647861706809781561)
              ·
                rfl

theorem cell22_1034871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 12].length) (baseStart_1034871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034871 prefixEnd_1034871 := by exact prefixLift 1034871
  have htrace : WordTrace (prefixWord ++ tailWord_1034871) baseStart_1034871 baseEnd_1034871 := by
    simpa [prefixWord, tailWord_1034871, baseEnd_1034871] using wordTrace_append hprefix tailTrace_1034871
  have hstable : (prefixWord ++ tailWord_1034871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034871).length < 2 ^ (prefixWord ++ tailWord_1034871).sum := by decide
  have hdescent : baseEnd_1034871 < baseStart_1034871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034873 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_1034873 : Nat := 118140960795 + 1034873 * 2 ^ 59
def prefixEnd_1034873 : Nat := 4983230072969 + 3 ^ 40 * 1034873 * 2
def baseEnd_1034873 : Nat := 354258176906956525552141

theorem tailTrace_1034873 : CollatzResearch.WordTrace tailWord_1034873 prefixEnd_1034873 354258176906956525552141 := by
  unfold tailWord_1034873
  simp only [CollatzResearch.WordTrace]
  refine ⟨37744919179839338082341273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25163279453226225388227515 37744919179839338082341273)
  ·
    refine ⟨28308689384879503561755955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37744919179839338082341273 28308689384879503561755955)
    ·
      refine ⟨42463034077319255342633933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28308689384879503561755955 42463034077319255342633933)
      ·
        refine ⟨15923637778994720753487725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42463034077319255342633933 15923637778994720753487725)
        ·
          refine ⟨5971364167123020282557897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15923637778994720753487725 5971364167123020282557897)
          ·
            refine ⟨4478523125342265211918423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971364167123020282557897 4478523125342265211918423)
            ·
              refine ⟨6717784688013397817877635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478523125342265211918423 6717784688013397817877635)
              ·
                refine ⟨10076677032020096726816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717784688013397817877635 10076677032020096726816453)
                ·
                  refine ⟨1889376943503768136278085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10076677032020096726816453 1889376943503768136278085)
                  ·
                    refine ⟨354258176906956525552141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1889376943503768136278085 354258176906956525552141)
                    ·
                      rfl

theorem cell22_1034873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_1034873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034873 prefixEnd_1034873 := by exact prefixLift 1034873
  have htrace : WordTrace (prefixWord ++ tailWord_1034873) baseStart_1034873 baseEnd_1034873 := by
    simpa [prefixWord, tailWord_1034873, baseEnd_1034873] using wordTrace_append hprefix tailTrace_1034873
  have hstable : (prefixWord ++ tailWord_1034873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034873).length < 2 ^ (prefixWord ++ tailWord_1034873).sum := by decide
  have hdescent : baseEnd_1034873 < baseStart_1034873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034877 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1034877 : Nat := 118140960795 + 1034877 * 2 ^ 59
def prefixEnd_1034877 : Nat := 4983230072969 + 3 ^ 40 * 1034877 * 2
def baseEnd_1034877 : Nat := 118086515396233949484043

theorem tailTrace_1034877 : CollatzResearch.WordTrace tailWord_1034877 prefixEnd_1034877 118086515396233949484043 := by
  unfold tailWord_1034877
  simp only [CollatzResearch.WordTrace]
  refine ⟨37745065071824846765486885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25163376714549897843657923 37745065071824846765486885)
  ·
    refine ⟨7077199700967158768528791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37745065071824846765486885 7077199700967158768528791)
    ·
      refine ⟨10615799551450738152793187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7077199700967158768528791 10615799551450738152793187)
      ·
        refine ⟨15923699327176107229189781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10615799551450738152793187 15923699327176107229189781)
        ·
          refine ⟨746423405961380026368271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15923699327176107229189781 746423405961380026368271)
          ·
            refine ⟨1119635108942070039552407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746423405961380026368271 1119635108942070039552407)
            ·
              refine ⟨1679452663413105059328611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119635108942070039552407 1679452663413105059328611)
              ·
                refine ⟨2519178995119657588992917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679452663413105059328611 2519178995119657588992917)
                ·
                  refine ⟨118086515396233949484043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2519178995119657588992917 118086515396233949484043)
                  ·
                    rfl

theorem cell22_1034877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1034877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034877 prefixEnd_1034877 := by exact prefixLift 1034877
  have htrace : WordTrace (prefixWord ++ tailWord_1034877) baseStart_1034877 baseEnd_1034877 := by
    simpa [prefixWord, tailWord_1034877, baseEnd_1034877] using wordTrace_append hprefix tailTrace_1034877
  have hstable : (prefixWord ++ tailWord_1034877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034877).length < 2 ^ (prefixWord ++ tailWord_1034877).sum := by decide
  have hdescent : baseEnd_1034877 < baseStart_1034877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034922 : List Nat := [3, 1, 5, 2, 2, 9]
def baseStart_1034922 : Nat := 118140960795 + 1034922 * 2 ^ 59
def prefixEnd_1034922 : Nat := 4983230072969 + 3 ^ 40 * 1034922 * 2
def baseEnd_1034922 : Nat := 4373764822325144828111

theorem tailTrace_1034922 : CollatzResearch.WordTrace tailWord_1034922 prefixEnd_1034922 4373764822325144828111 := by
  unfold tailWord_1034922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436676589165454862718755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25164470904441212967250013 9436676589165454862718755)
  ·
    refine ⟨14155014883748182294078133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9436676589165454862718755 14155014883748182294078133)
    ·
      refine ⟨1327032645351392090069825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14155014883748182294078133 1327032645351392090069825)
      ·
        refine ⟨995274484013544067552369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1327032645351392090069825 995274484013544067552369)
        ·
          refine ⟨746455863010158050664277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995274484013544067552369 746455863010158050664277)
          ·
            refine ⟨4373764822325144828111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 746455863010158050664277 4373764822325144828111)
            ·
              rfl

theorem cell22_1034922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 9].length) (baseStart_1034922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034922 prefixEnd_1034922 := by exact prefixLift 1034922
  have htrace : WordTrace (prefixWord ++ tailWord_1034922) baseStart_1034922 baseEnd_1034922 := by
    simpa [prefixWord, tailWord_1034922, baseEnd_1034922] using wordTrace_append hprefix tailTrace_1034922
  have hstable : (prefixWord ++ tailWord_1034922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034922).length < 2 ^ (prefixWord ++ tailWord_1034922).sum := by decide
  have hdescent : baseEnd_1034922 < baseStart_1034922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034984 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_1034984 : Nat := 118140960795 + 1034984 * 2 ^ 59
def prefixEnd_1034984 : Nat := 4983230072969 + 3 ^ 40 * 1034984 * 2
def baseEnd_1034984 : Nat := 118098724825129745342267

theorem tailTrace_1034984 : CollatzResearch.WordTrace tailWord_1034984 prefixEnd_1034984 118098724825129745342267 := by
  unfold tailWord_1034984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874483841218602019816003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25165978454958136026421337 18874483841218602019816003)
  ·
    refine ⟨28311725761827903029724005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18874483841218602019816003 28311725761827903029724005)
    ·
      refine ⟨5308448580342731818073251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28311725761827903029724005 5308448580342731818073251)
      ·
        refine ⟨7962672870514097727109877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308448580342731818073251 7962672870514097727109877)
        ·
          refine ⟨746500581610696661916551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7962672870514097727109877 746500581610696661916551)
          ·
            refine ⟨1119750872416044992874827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746500581610696661916551 1119750872416044992874827)
            ·
              refine ⟨1679626308624067489312241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119750872416044992874827 1679626308624067489312241)
              ·
                refine ⟨1259719731468050616984181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679626308624067489312241 1259719731468050616984181)
                ·
                  refine ⟨118098724825129745342267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259719731468050616984181 118098724825129745342267)
                  ·
                    rfl

theorem cell22_1034984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_1034984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1034984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1034984 prefixEnd_1034984 := by exact prefixLift 1034984
  have htrace : WordTrace (prefixWord ++ tailWord_1034984) baseStart_1034984 baseEnd_1034984 := by
    simpa [prefixWord, tailWord_1034984, baseEnd_1034984] using wordTrace_append hprefix tailTrace_1034984
  have hstable : (prefixWord ++ tailWord_1034984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034984).length < 2 ^ (prefixWord ++ tailWord_1034984).sum := by decide
  have hdescent : baseEnd_1034984 < baseStart_1034984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035023 : List Nat := [1, 1, 2, 1, 1, 1, 7, 8]
def baseStart_1035023 : Nat := 118140960795 + 1035023 * 2 ^ 59
def prefixEnd_1035023 : Nat := 4983230072969 + 3 ^ 40 * 1035023 * 2
def baseEnd_1035023 : Nat := 39367724996934014922409

theorem tailTrace_1035023 : CollatzResearch.WordTrace tailWord_1035023 prefixEnd_1035023 39367724996934014922409 := by
  unfold tailWord_1035023
  simp only [CollatzResearch.WordTrace]
  refine ⟨37750390129295913700301723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25166926752863942466867815 37750390129295913700301723)
  ·
    refine ⟨56625585193943870550452585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37750390129295913700301723 56625585193943870550452585)
    ·
      refine ⟨42469188895457902912839439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56625585193943870550452585 42469188895457902912839439)
      ·
        refine ⟨63703783343186854369259159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42469188895457902912839439 63703783343186854369259159)
        ·
          refine ⟨95555675014780281553888739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63703783343186854369259159 95555675014780281553888739)
          ·
            refine ⟨143333512522170422330833109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95555675014780281553888739 143333512522170422330833109)
            ·
              refine ⟨3359379199738369273378901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 143333512522170422330833109 3359379199738369273378901)
              ·
                refine ⟨39367724996934014922409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3359379199738369273378901 39367724996934014922409)
                ·
                  rfl

theorem cell22_1035023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 8].length) (baseStart_1035023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035023 prefixEnd_1035023 := by exact prefixLift 1035023
  have htrace : WordTrace (prefixWord ++ tailWord_1035023) baseStart_1035023 baseEnd_1035023 := by
    simpa [prefixWord, tailWord_1035023, baseEnd_1035023] using wordTrace_append hprefix tailTrace_1035023
  have hstable : (prefixWord ++ tailWord_1035023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035023).length < 2 ^ (prefixWord ++ tailWord_1035023).sum := by decide
  have hdescent : baseEnd_1035023 < baseStart_1035023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035040 : List Nat := [2, 1, 1, 5, 1, 4, 8]
def baseStart_1035040 : Nat := 118140960795 + 1035040 * 2 ^ 59
def prefixEnd_1035040 : Nat := 4983230072969 + 3 ^ 40 * 1035040 * 2
def baseEnd_1035040 : Nat := 13122790534067546541727

theorem tailTrace_1035040 : CollatzResearch.WordTrace tailWord_1035040 prefixEnd_1035040 13122790534067546541727 := by
  unfold tailWord_1035040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18875505085117162801835287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25167340113489550402447049 18875505085117162801835287)
  ·
    refine ⟨28313257627675744202752931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18875505085117162801835287 28313257627675744202752931)
    ·
      refine ⟨42469886441513616304129397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28313257627675744202752931 42469886441513616304129397)
      ·
        refine ⟨3981551853891901528512131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42469886441513616304129397 3981551853891901528512131)
        ·
          refine ⟨5972327780837852292768197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981551853891901528512131 5972327780837852292768197)
          ·
            refine ⟨1119811458907097304894037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5972327780837852292768197 1119811458907097304894037)
            ·
              refine ⟨13122790534067546541727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1119811458907097304894037 13122790534067546541727)
              ·
                rfl

theorem cell22_1035040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 8].length) (baseStart_1035040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035040 prefixEnd_1035040 := by exact prefixLift 1035040
  have htrace : WordTrace (prefixWord ++ tailWord_1035040) baseStart_1035040 baseEnd_1035040 := by
    simpa [prefixWord, tailWord_1035040, baseEnd_1035040] using wordTrace_append hprefix tailTrace_1035040
  have hstable : (prefixWord ++ tailWord_1035040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035040).length < 2 ^ (prefixWord ++ tailWord_1035040).sum := by decide
  have hdescent : baseEnd_1035040 < baseStart_1035040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035042 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1035042 : Nat := 118140960795 + 1035042 * 2 ^ 59
def prefixEnd_1035042 : Nat := 4983230072969 + 3 ^ 40 * 1035042 * 2
def baseEnd_1035042 : Nat := 354316029060696418076623

theorem tailTrace_1035042 : CollatzResearch.WordTrace tailWord_1035042 prefixEnd_1035042 354316029060696418076623 := by
  unfold tailWord_1035042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437770779056769986310845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25167388744151386630162253 9437770779056769986310845)
  ·
    refine ⟨3539164042146288744866567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9437770779056769986310845 3539164042146288744866567)
    ·
      refine ⟨5308746063219433117299851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539164042146288744866567 5308746063219433117299851)
      ·
        refine ⟨7963119094829149675949777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308746063219433117299851 7963119094829149675949777)
        ·
          refine ⟨5972339321121862256962333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963119094829149675949777 5972339321121862256962333)
          ·
            refine ⟨2239627245420698346360875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5972339321121862256962333 2239627245420698346360875)
            ·
              refine ⟨3359440868131047519541313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239627245420698346360875 3359440868131047519541313)
              ·
                refine ⟨2519580651098285639655985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359440868131047519541313 2519580651098285639655985)
                ·
                  refine ⟨1889685488323714229741989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519580651098285639655985 1889685488323714229741989)
                  ·
                    refine ⟨354316029060696418076623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1889685488323714229741989 354316029060696418076623)
                    ·
                      rfl

theorem cell22_1035042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1035042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035042 prefixEnd_1035042 := by exact prefixLift 1035042
  have htrace : WordTrace (prefixWord ++ tailWord_1035042) baseStart_1035042 baseEnd_1035042 := by
    simpa [prefixWord, tailWord_1035042, baseEnd_1035042] using wordTrace_append hprefix tailTrace_1035042
  have hstable : (prefixWord ++ tailWord_1035042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035042).length < 2 ^ (prefixWord ++ tailWord_1035042).sum := by decide
  have hdescent : baseEnd_1035042 < baseStart_1035042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035061 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1035061 : Nat := 118140960795 + 1035061 * 2 ^ 59
def prefixEnd_1035061 : Nat := 4983230072969 + 3 ^ 40 * 1035061 * 2
def baseEnd_1035061 : Nat := 354322533148986701851565

theorem tailTrace_1035061 : CollatzResearch.WordTrace tailWord_1035061 prefixEnd_1035061 354322533148986701851565 := by
  unfold tailWord_1035061
  simp only [CollatzResearch.WordTrace]
  refine ⟨37751776103158246190185037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25167850735438830793456691 37751776103158246190185037)
  ·
    refine ⟨14156916038684342321319389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37751776103158246190185037 14156916038684342321319389)
    ·
      refine ⟨5308843514506628370494771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14156916038684342321319389 5308843514506628370494771)
      ·
        refine ⟨7963265271759942555742157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308843514506628370494771 7963265271759942555742157)
        ·
          refine ⟨2986224476909978458403309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7963265271759942555742157 2986224476909978458403309)
          ·
            refine ⟨1119834178841241921901241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2986224476909978458403309 1119834178841241921901241)
            ·
              refine ⟨839875634130931441425931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119834178841241921901241 839875634130931441425931)
              ·
                refine ⟨1259813451196397162138897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839875634130931441425931 1259813451196397162138897)
                ·
                  refine ⟨944860088397297871604173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1259813451196397162138897 944860088397297871604173)
                  ·
                    refine ⟨354322533148986701851565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944860088397297871604173 354322533148986701851565)
                    ·
                      rfl

theorem cell22_1035061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1035061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035061 prefixEnd_1035061 := by exact prefixLift 1035061
  have htrace : WordTrace (prefixWord ++ tailWord_1035061) baseStart_1035061 baseEnd_1035061 := by
    simpa [prefixWord, tailWord_1035061, baseEnd_1035061] using wordTrace_append hprefix tailTrace_1035061
  have hstable : (prefixWord ++ tailWord_1035061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035061).length < 2 ^ (prefixWord ++ tailWord_1035061).sum := by decide
  have hdescent : baseEnd_1035061 < baseStart_1035061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035076 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1035076 : Nat := 118140960795 + 1035076 * 2 ^ 59
def prefixEnd_1035076 : Nat := 4983230072969 + 3 ^ 40 * 1035076 * 2
def baseEnd_1035076 : Nat := 354327667955531662726519

theorem tailTrace_1035076 : CollatzResearch.WordTrace tailWord_1035076 prefixEnd_1035076 354327667955531662726519 := by
  unfold tailWord_1035076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876161599051951875990541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25168215465402602501320721 18876161599051951875990541)
  ·
    refine ⟨7078560599644481953496453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18876161599051951875990541 7078560599644481953496453)
    ·
      refine ⟨1327230112433340366280585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7078560599644481953496453 1327230112433340366280585)
      ·
        refine ⟨995422584325005274710439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1327230112433340366280585 995422584325005274710439)
        ·
          refine ⟨1493133876487507912065659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995422584325005274710439 1493133876487507912065659)
          ·
            refine ⟨2239700814731261868098489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493133876487507912065659 2239700814731261868098489)
            ·
              refine ⟨1679775611048446401073867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239700814731261868098489 1679775611048446401073867)
              ·
                refine ⟨2519663416572669601610801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679775611048446401073867 2519663416572669601610801)
                ·
                  refine ⟨1889747562429502201208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519663416572669601610801 1889747562429502201208101)
                  ·
                    refine ⟨354327667955531662726519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1889747562429502201208101 354327667955531662726519)
                    ·
                      rfl

theorem cell22_1035076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1035076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035076 prefixEnd_1035076 := by exact prefixLift 1035076
  have htrace : WordTrace (prefixWord ++ tailWord_1035076) baseStart_1035076 baseEnd_1035076 := by
    simpa [prefixWord, tailWord_1035076, baseEnd_1035076] using wordTrace_append hprefix tailTrace_1035076
  have hstable : (prefixWord ++ tailWord_1035076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035076).length < 2 ^ (prefixWord ++ tailWord_1035076).sum := by decide
  have hdescent : baseEnd_1035076 < baseStart_1035076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035115 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_1035115 : Nat := 118140960795 + 1035115 * 2 ^ 59
def prefixEnd_1035115 : Nat := 4983230072969 + 3 ^ 40 * 1035115 * 2
def baseEnd_1035115 : Nat := 354341018452548561001399

theorem tailTrace_1035115 : CollatzResearch.WordTrace tailWord_1035115 prefixEnd_1035115 354341018452548561001399 := by
  unfold tailWord_1035115
  simp only [CollatzResearch.WordTrace]
  refine ⟨37753745644962613412650799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25169163763308408941767199 37753745644962613412650799)
  ·
    refine ⟨56630618467443920118976199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37753745644962613412650799 56630618467443920118976199)
    ·
      refine ⟨84945927701165880178464299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56630618467443920118976199 84945927701165880178464299)
      ·
        refine ⟨127418891551748820267696449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84945927701165880178464299 127418891551748820267696449)
        ·
          refine ⟨95564168663811615200772337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127418891551748820267696449 95564168663811615200772337)
          ·
            refine ⟨71673126497858711400579253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95564168663811615200772337 71673126497858711400579253)
            ·
              refine ⟨6719355609174254193804305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71673126497858711400579253 6719355609174254193804305)
              ·
                refine ⟨5039516706880690645353229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719355609174254193804305 5039516706880690645353229)
                ·
                  refine ⟨1889818765080258992007461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5039516706880690645353229 1889818765080258992007461)
                  ·
                    refine ⟨354341018452548561001399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1889818765080258992007461 354341018452548561001399)
                    ·
                      rfl

theorem cell22_1035115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_1035115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035115 prefixEnd_1035115 := by exact prefixLift 1035115
  have htrace : WordTrace (prefixWord ++ tailWord_1035115) baseStart_1035115 baseEnd_1035115 := by
    simpa [prefixWord, tailWord_1035115, baseEnd_1035115] using wordTrace_append hprefix tailTrace_1035115
  have hstable : (prefixWord ++ tailWord_1035115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035115).length < 2 ^ (prefixWord ++ tailWord_1035115).sum := by decide
  have hdescent : baseEnd_1035115 < baseStart_1035115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035147 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 4]
def baseStart_1035147 : Nat := 118140960795 + 1035147 * 2 ^ 59
def prefixEnd_1035147 : Nat := 4983230072969 + 3 ^ 40 * 1035147 * 2
def baseEnd_1035147 : Nat := 118117324235503714733767

theorem tailTrace_1035147 : CollatzResearch.WordTrace tailWord_1035147 prefixEnd_1035147 118117324235503714733767 := by
  unfold tailWord_1035147
  simp only [CollatzResearch.WordTrace]
  refine ⟨37754912780846682877815695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25169941853897788585210463 37754912780846682877815695)
  ·
    refine ⟨56632369171270024316723543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37754912780846682877815695 56632369171270024316723543)
    ·
      refine ⟨84948553756905036475085315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56632369171270024316723543 84948553756905036475085315)
      ·
        refine ⟨127422830635357554712627973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84948553756905036475085315 127422830635357554712627973)
        ·
          refine ⟨23891780744129541508617745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127422830635357554712627973 23891780744129541508617745)
          ·
            refine ⟨17918835558097156131463309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23891780744129541508617745 17918835558097156131463309)
            ·
              refine ⟨6719563334286433549298741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17918835558097156131463309 6719563334286433549298741)
              ·
                refine ⟨629959062589353145246757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6719563334286433549298741 629959062589353145246757)
                ·
                  refine ⟨118117324235503714733767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629959062589353145246757 118117324235503714733767)
                  ·
                    rfl

theorem cell22_1035147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 4].length) (baseStart_1035147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035147 prefixEnd_1035147 := by exact prefixLift 1035147
  have htrace : WordTrace (prefixWord ++ tailWord_1035147) baseStart_1035147 baseEnd_1035147 := by
    simpa [prefixWord, tailWord_1035147, baseEnd_1035147] using wordTrace_append hprefix tailTrace_1035147
  have hstable : (prefixWord ++ tailWord_1035147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035147).length < 2 ^ (prefixWord ++ tailWord_1035147).sum := by decide
  have hdescent : baseEnd_1035147 < baseStart_1035147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035164 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_1035164 : Nat := 118140960795 + 1035164 * 2 ^ 59
def prefixEnd_1035164 : Nat := 4983230072969 + 3 ^ 40 * 1035164 * 2
def baseEnd_1035164 : Nat := 118119264051309588842083

theorem tailTrace_1035164 : CollatzResearch.WordTrace tailWord_1035164 prefixEnd_1035164 118119264051309588842083 := by
  unfold tailWord_1035164
  simp only [CollatzResearch.WordTrace]
  refine ⟨18877766410892547390592273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25170355214523396520789697 18877766410892547390592273)
  ·
    refine ⟨14158324808169410542944205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18877766410892547390592273 14158324808169410542944205)
    ·
      refine ⟨5309371803063528953604077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14158324808169410542944205 5309371803063528953604077)
      ·
        refine ⟨1991014426148823357601529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5309371803063528953604077 1991014426148823357601529)
        ·
          refine ⟨1493260819611617518201147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991014426148823357601529 1493260819611617518201147)
          ·
            refine ⟨2239891229417426277301721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493260819611617518201147 2239891229417426277301721)
            ·
              refine ⟨1679918422063069707976291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239891229417426277301721 1679918422063069707976291)
              ·
                refine ⟨2519877633094604561964437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679918422063069707976291 2519877633094604561964437)
                ·
                  refine ⟨118119264051309588842083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2519877633094604561964437 118119264051309588842083)
                  ·
                    rfl

theorem cell22_1035164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_1035164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035164 prefixEnd_1035164 := by exact prefixLift 1035164
  have htrace : WordTrace (prefixWord ++ tailWord_1035164) baseStart_1035164 baseEnd_1035164 := by
    simpa [prefixWord, tailWord_1035164, baseEnd_1035164] using wordTrace_append hprefix tailTrace_1035164
  have hstable : (prefixWord ++ tailWord_1035164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035164).length < 2 ^ (prefixWord ++ tailWord_1035164).sum := by decide
  have hdescent : baseEnd_1035164 < baseStart_1035164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035192 : List Nat := [2, 1, 2, 1, 2, 4, 4, 6]
def baseStart_1035192 : Nat := 118140960795 + 1035192 * 2 ^ 59
def prefixEnd_1035192 : Nat := 4983230072969 + 3 ^ 40 * 1035192 * 2
def baseEnd_1035192 : Nat := 39374153014016225202907

theorem tailTrace_1035192 : CollatzResearch.WordTrace tailWord_1035192 prefixEnd_1035192 39374153014016225202907 := by
  unfold tailWord_1035192
  simp only [CollatzResearch.WordTrace]
  refine ⟨18878277032841827781601915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25171036043789103708802553 18878277032841827781601915)
  ·
    refine ⟨28317415549262741672402873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18878277032841827781601915 28317415549262741672402873)
    ·
      refine ⟨21238061661947056254302155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28317415549262741672402873 21238061661947056254302155)
      ·
        refine ⟨31857092492920584381453233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21238061661947056254302155 31857092492920584381453233)
        ·
          refine ⟨23892819369690438286089925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31857092492920584381453233 23892819369690438286089925)
          ·
            refine ⟨4479903631816957178641861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23892819369690438286089925 4479903631816957178641861)
            ·
              refine ⟨839981930965679470995349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4479903631816957178641861 839981930965679470995349)
              ·
                refine ⟨39374153014016225202907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 839981930965679470995349 39374153014016225202907)
                ·
                  rfl

theorem cell22_1035192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_1035192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035192 prefixEnd_1035192 := by exact prefixLift 1035192
  have htrace : WordTrace (prefixWord ++ tailWord_1035192) baseStart_1035192 baseEnd_1035192 := by
    simpa [prefixWord, tailWord_1035192, baseEnd_1035192] using wordTrace_append hprefix tailTrace_1035192
  have hstable : (prefixWord ++ tailWord_1035192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035192).length < 2 ^ (prefixWord ++ tailWord_1035192).sum := by decide
  have hdescent : baseEnd_1035192 < baseStart_1035192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035207 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 5, 3]
def baseStart_1035207 : Nat := 118140960795 + 1035207 * 2 ^ 59
def prefixEnd_1035207 : Nat := 4983230072969 + 3 ^ 40 * 1035207 * 2
def baseEnd_1035207 : Nat := 354372511932690987701117

theorem tailTrace_1035207 : CollatzResearch.WordTrace tailWord_1035207 prefixEnd_1035207 354372511932690987701117 := by
  unfold tailWord_1035207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757101160629313124999875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25171400773752875416666583 37757101160629313124999875)
  ·
    refine ⟨56635651740943969687499813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37757101160629313124999875 56635651740943969687499813)
    ·
      refine ⟨10619184701426994316406215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56635651740943969687499813 10619184701426994316406215)
      ·
        refine ⟨15928777052140491474609323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619184701426994316406215 15928777052140491474609323)
        ·
          refine ⟨23893165578210737211913985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928777052140491474609323 23893165578210737211913985)
          ·
            refine ⟨17919874183658052908935489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23893165578210737211913985 17919874183658052908935489)
            ·
              refine ⟨13439905637743539681701617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17919874183658052908935489 13439905637743539681701617)
              ·
                refine ⟨10079929228307654761276213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13439905637743539681701617 10079929228307654761276213)
                ·
                  refine ⟨944993365153842633869645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10079929228307654761276213 944993365153842633869645)
                  ·
                    refine ⟨354372511932690987701117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944993365153842633869645 354372511932690987701117)
                    ·
                      rfl

theorem cell22_1035207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_1035207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035207 prefixEnd_1035207 := by exact prefixLift 1035207
  have htrace : WordTrace (prefixWord ++ tailWord_1035207) baseStart_1035207 baseEnd_1035207 := by
    simpa [prefixWord, tailWord_1035207, baseEnd_1035207] using wordTrace_append hprefix tailTrace_1035207
  have hstable : (prefixWord ++ tailWord_1035207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035207).length < 2 ^ (prefixWord ++ tailWord_1035207).sum := by decide
  have hdescent : baseEnd_1035207 < baseStart_1035207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035224 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_1035224 : Nat := 118140960795 + 1035224 * 2 ^ 59
def prefixEnd_1035224 : Nat := 4983230072969 + 3 ^ 40 * 1035224 * 2
def baseEnd_1035224 : Nat := 354378331380108610026065

theorem tailTrace_1035224 : CollatzResearch.WordTrace tailWord_1035224 prefixEnd_1035224 354378331380108610026065 := by
  unfold tailWord_1035224
  simp only [CollatzResearch.WordTrace]
  refine ⟨18878860600783862514184363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25171814134378483352245817 18878860600783862514184363)
  ·
    refine ⟨28318290901175793771276545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18878860600783862514184363 28318290901175793771276545)
    ·
      refine ⟨21238718175881845328457409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28318290901175793771276545 21238718175881845328457409)
      ·
        refine ⟨15929038631911383996343057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21238718175881845328457409 15929038631911383996343057)
        ·
          refine ⟨11946778973933537997257293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15929038631911383996343057 11946778973933537997257293)
          ·
            refine ⟨4480042115225076748971485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11946778973933537997257293 4480042115225076748971485)
            ·
              refine ⟨1680015793209403780864307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4480042115225076748971485 1680015793209403780864307)
              ·
                refine ⟨2520023689814105671296461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680015793209403780864307 2520023689814105671296461)
                ·
                  refine ⟨945008883680289626736173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2520023689814105671296461 945008883680289626736173)
                  ·
                    refine ⟨354378331380108610026065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945008883680289626736173 354378331380108610026065)
                    ·
                      rfl

theorem cell22_1035224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_1035224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035224 prefixEnd_1035224 := by exact prefixLift 1035224
  have htrace : WordTrace (prefixWord ++ tailWord_1035224) baseStart_1035224 baseEnd_1035224 := by
    simpa [prefixWord, tailWord_1035224, baseEnd_1035224] using wordTrace_append hprefix tailTrace_1035224
  have hstable : (prefixWord ++ tailWord_1035224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035224).length < 2 ^ (prefixWord ++ tailWord_1035224).sum := by decide
  have hdescent : baseEnd_1035224 < baseStart_1035224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035312 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_1035312 : Nat := 118140960795 + 1035312 * 2 ^ 59
def prefixEnd_1035312 : Nat := 4983230072969 + 3 ^ 40 * 1035312 * 2
def baseEnd_1035312 : Nat := 354408455578505713825795

theorem tailTrace_1035312 : CollatzResearch.WordTrace tailWord_1035312 prefixEnd_1035312 354408455578505713825795 := by
  unfold tailWord_1035312
  simp only [CollatzResearch.WordTrace]
  refine ⟨18880465412624458028786095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25173953883499277371714793 18880465412624458028786095)
  ·
    refine ⟨28320698118936687043179143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18880465412624458028786095 28320698118936687043179143)
    ·
      refine ⟨42481047178405030564768715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28320698118936687043179143 42481047178405030564768715)
      ·
        refine ⟨63721570767607545847153073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42481047178405030564768715 63721570767607545847153073)
        ·
          refine ⟨47791178075705659385364805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63721570767607545847153073 47791178075705659385364805)
          ·
            refine ⟨8960845889194811134755901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47791178075705659385364805 8960845889194811134755901)
            ·
              refine ⟨3360317208448054175533463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8960845889194811134755901 3360317208448054175533463)
              ·
                refine ⟨5040475812672081263300195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360317208448054175533463 5040475812672081263300195)
                ·
                  refine ⟨7560713719008121894950293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040475812672081263300195 7560713719008121894950293)
                  ·
                    refine ⟨354408455578505713825795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7560713719008121894950293 354408455578505713825795)
                    ·
                      rfl

theorem cell22_1035312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_1035312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035312 prefixEnd_1035312 := by exact prefixLift 1035312
  have htrace : WordTrace (prefixWord ++ tailWord_1035312) baseStart_1035312 baseEnd_1035312 := by
    simpa [prefixWord, tailWord_1035312, baseEnd_1035312] using wordTrace_append hprefix tailTrace_1035312
  have hstable : (prefixWord ++ tailWord_1035312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035312).length < 2 ^ (prefixWord ++ tailWord_1035312).sum := by decide
  have hdescent : baseEnd_1035312 < baseStart_1035312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035314 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1035314 : Nat := 118140960795 + 1035314 * 2 ^ 59
def prefixEnd_1035314 : Nat := 4983230072969 + 3 ^ 40 * 1035314 * 2
def baseEnd_1035314 : Nat := 354409140219378375275789

theorem tailTrace_1035314 : CollatzResearch.WordTrace tailWord_1035314 prefixEnd_1035314 354409140219378375275789 := by
  unfold tailWord_1035314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440250942810417599786249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25174002514161113599429997 9440250942810417599786249)
  ·
    refine ⟨7080188207107813199839687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9440250942810417599786249 7080188207107813199839687)
    ·
      refine ⟨10620282310661719799759531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7080188207107813199839687 10620282310661719799759531)
      ·
        refine ⟨15930423465992579699639297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620282310661719799759531 15930423465992579699639297)
        ·
          refine ⟨11947817599494434774729473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15930423465992579699639297 11947817599494434774729473)
          ·
            refine ⟨8960863199620826081047105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11947817599494434774729473 8960863199620826081047105)
            ·
              refine ⟨6720647399715619560785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8960863199620826081047105 6720647399715619560785329)
              ·
                refine ⟨5040485549786714670588997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720647399715619560785329 5040485549786714670588997)
                ·
                  refine ⟨945091040585009000735437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5040485549786714670588997 945091040585009000735437)
                  ·
                    refine ⟨354409140219378375275789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945091040585009000735437 354409140219378375275789)
                    ·
                      rfl

theorem cell22_1035314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1035314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035314 prefixEnd_1035314 := by exact prefixLift 1035314
  have htrace : WordTrace (prefixWord ++ tailWord_1035314) baseStart_1035314 baseEnd_1035314 := by
    simpa [prefixWord, tailWord_1035314, baseEnd_1035314] using wordTrace_append hprefix tailTrace_1035314
  have hstable : (prefixWord ++ tailWord_1035314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035314).length < 2 ^ (prefixWord ++ tailWord_1035314).sum := by decide
  have hdescent : baseEnd_1035314 < baseStart_1035314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035318 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1035318 : Nat := 118140960795 + 1035318 * 2 ^ 59
def prefixEnd_1035318 : Nat := 4983230072969 + 3 ^ 40 * 1035318 * 2
def baseEnd_1035318 : Nat := 354410509501123698175777

theorem tailTrace_1035318 : CollatzResearch.WordTrace tailWord_1035318 prefixEnd_1035318 354410509501123698175777 := by
  unfold tailWord_1035318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360071853951698692643163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25174099775484786054860405 2360071853951698692643163)
  ·
    refine ⟨3540107780927548038964745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2360071853951698692643163 3540107780927548038964745)
    ·
      refine ⟨2655080835695661029223559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3540107780927548038964745 2655080835695661029223559)
      ·
        refine ⟨3982621253543491543835339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655080835695661029223559 3982621253543491543835339)
        ·
          refine ⟨5973931880315237315753009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3982621253543491543835339 5973931880315237315753009)
          ·
            refine ⟨4480448910236427986814757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5973931880315237315753009 4480448910236427986814757)
            ·
              refine ⟨840084170669330247527767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4480448910236427986814757 840084170669330247527767)
              ·
                refine ⟨1260126256003995371291651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840084170669330247527767 1260126256003995371291651)
                ·
                  refine ⟨1890189384005993056937477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260126256003995371291651 1890189384005993056937477)
                  ·
                    refine ⟨354410509501123698175777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890189384005993056937477 354410509501123698175777)
                    ·
                      rfl

theorem cell22_1035318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1035318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035318 prefixEnd_1035318 := by exact prefixLift 1035318
  have htrace : WordTrace (prefixWord ++ tailWord_1035318) baseStart_1035318 baseEnd_1035318 := by
    simpa [prefixWord, tailWord_1035318, baseEnd_1035318] using wordTrace_append hprefix tailTrace_1035318
  have hstable : (prefixWord ++ tailWord_1035318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035318).length < 2 ^ (prefixWord ++ tailWord_1035318).sum := by decide
  have hdescent : baseEnd_1035318 < baseStart_1035318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035359 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 3, 3]
def baseStart_1035359 : Nat := 118140960795 + 1035359 * 2 ^ 59
def prefixEnd_1035359 : Nat := 4983230072969 + 3 ^ 40 * 1035359 * 2
def baseEnd_1035359 : Nat := 354424544639013257900651

theorem tailTrace_1035359 : CollatzResearch.WordTrace tailWord_1035359 prefixEnd_1035359 354424544639013257900651 := by
  unfold tailWord_1035359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37762645056078643084533131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175096704052428723022087 37762645056078643084533131)
  ·
    refine ⟨56643967584117964626799697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37762645056078643084533131 56643967584117964626799697)
    ·
      refine ⟨42482975688088473470099773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56643967584117964626799697 42482975688088473470099773)
      ·
        refine ⟨15931115883033177551287415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42482975688088473470099773 15931115883033177551287415)
        ·
          refine ⟨23896673824549766326931123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15931115883033177551287415 23896673824549766326931123)
          ·
            refine ⟨35845010736824649490396685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23896673824549766326931123 35845010736824649490396685)
            ·
              refine ⟨13441879026309243558898757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35845010736824649490396685 13441879026309243558898757)
              ·
                refine ⟨2520352317432983167293517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13441879026309243558898757 2520352317432983167293517)
                ·
                  refine ⟨945132119037368687735069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2520352317432983167293517 945132119037368687735069)
                  ·
                    refine ⟨354424544639013257900651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945132119037368687735069 354424544639013257900651)
                    ·
                      rfl

theorem cell22_1035359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_1035359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035359 prefixEnd_1035359 := by exact prefixLift 1035359
  have htrace : WordTrace (prefixWord ++ tailWord_1035359) baseStart_1035359 baseEnd_1035359 := by
    simpa [prefixWord, tailWord_1035359, baseEnd_1035359] using wordTrace_append hprefix tailTrace_1035359
  have hstable : (prefixWord ++ tailWord_1035359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035359).length < 2 ^ (prefixWord ++ tailWord_1035359).sum := by decide
  have hdescent : baseEnd_1035359 < baseStart_1035359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035372 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_1035372 : Nat := 118140960795 + 1035372 * 2 ^ 59
def prefixEnd_1035372 : Nat := 4983230072969 + 3 ^ 40 * 1035372 * 2
def baseEnd_1035372 : Nat := 118142998268228519108537

theorem tailTrace_1035372 : CollatzResearch.WordTrace tailWord_1035372 prefixEnd_1035372 118142998268228519108537 := by
  unfold tailWord_1035372
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881559602515773152378185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25175412803354364203170913 18881559602515773152378185)
  ·
    refine ⟨14161169701886829864283639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18881559602515773152378185 14161169701886829864283639)
    ·
      refine ⟨21241754552830244796425459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14161169701886829864283639 21241754552830244796425459)
      ·
        refine ⟨31862631829245367194638189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21241754552830244796425459 31862631829245367194638189)
        ·
          refine ⟨11948486935967012697989321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31862631829245367194638189 11948486935967012697989321)
          ·
            refine ⟨8961365201975259523491991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11948486935967012697989321 8961365201975259523491991)
            ·
              refine ⟨13442047802962889285237987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961365201975259523491991 13442047802962889285237987)
              ·
                refine ⟨20163071704444333927856981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442047802962889285237987 20163071704444333927856981)
                ·
                  refine ⟨118142998268228519108537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20163071704444333927856981 118142998268228519108537)
                  ·
                    rfl

theorem cell22_1035372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_1035372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035372 prefixEnd_1035372 := by exact prefixLift 1035372
  have htrace : WordTrace (prefixWord ++ tailWord_1035372) baseStart_1035372 baseEnd_1035372 := by
    simpa [prefixWord, tailWord_1035372, baseEnd_1035372] using wordTrace_append hprefix tailTrace_1035372
  have hstable : (prefixWord ++ tailWord_1035372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035372).length < 2 ^ (prefixWord ++ tailWord_1035372).sum := by decide
  have hdescent : baseEnd_1035372 < baseStart_1035372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035387 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_1035387 : Nat := 118140960795 + 1035387 * 2 ^ 59
def prefixEnd_1035387 : Nat := 4983230072969 + 3 ^ 40 * 1035387 * 2
def baseEnd_1035387 : Nat := 354434129611230518200565

theorem tailTrace_1035387 : CollatzResearch.WordTrace tailWord_1035387 prefixEnd_1035387 354434129611230518200565 := by
  unfold tailWord_1035387
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763666299977203866552415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175777533318135911034943 37763666299977203866552415)
  ·
    refine ⟨56645499449965805799828623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37763666299977203866552415 56645499449965805799828623)
    ·
      refine ⟨84968249174948708699742935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56645499449965805799828623 84968249174948708699742935)
      ·
        refine ⟨127452373762423063049614403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84968249174948708699742935 127452373762423063049614403)
        ·
          refine ⟨191178560643634594574421605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127452373762423063049614403 191178560643634594574421605)
          ·
            refine ⟨35845980120681486482704051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191178560643634594574421605 35845980120681486482704051)
            ·
              refine ⟨53768970181022229724056077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35845980120681486482704051 53768970181022229724056077)
              ·
                refine ⟨20163363817883336146521029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53768970181022229724056077 20163363817883336146521029)
                ·
                  refine ⟨3780630715853125527472693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20163363817883336146521029 3780630715853125527472693)
                  ·
                    refine ⟨354434129611230518200565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3780630715853125527472693 354434129611230518200565)
                    ·
                      rfl

theorem cell22_1035387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_1035387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035387 prefixEnd_1035387 := by exact prefixLift 1035387
  have htrace : WordTrace (prefixWord ++ tailWord_1035387) baseStart_1035387 baseEnd_1035387 := by
    simpa [prefixWord, tailWord_1035387, baseEnd_1035387] using wordTrace_append hprefix tailTrace_1035387
  have hstable : (prefixWord ++ tailWord_1035387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035387).length < 2 ^ (prefixWord ++ tailWord_1035387).sum := by decide
  have hdescent : baseEnd_1035387 < baseStart_1035387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035389 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 5]
def baseStart_1035389 : Nat := 118140960795 + 1035389 * 2 ^ 59
def prefixEnd_1035389 : Nat := 4983230072969 + 3 ^ 40 * 1035389 * 2
def baseEnd_1035389 : Nat := 118144938084034393216853

theorem tailTrace_1035389 : CollatzResearch.WordTrace tailWord_1035389 prefixEnd_1035389 118144938084034393216853 := by
  unfold tailWord_1035389
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763739245969958208125221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175826163979972138750147 37763739245969958208125221)
  ·
    refine ⟨7080701108619367164023479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37763739245969958208125221 7080701108619367164023479)
    ·
      refine ⟨10621051662929050746035219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7080701108619367164023479 10621051662929050746035219)
      ·
        refine ⟨15931577494393576119052829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621051662929050746035219 15931577494393576119052829)
        ·
          refine ⟨5974341560397591044644811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15931577494393576119052829 5974341560397591044644811)
          ·
            refine ⟨8961512340596386566967217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974341560397591044644811 8961512340596386566967217)
            ·
              refine ⟨6721134255447289925225413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961512340596386566967217 6721134255447289925225413)
              ·
                refine ⟨1260212672896366860979765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6721134255447289925225413 1260212672896366860979765)
                ·
                  refine ⟨118144938084034393216853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1260212672896366860979765 118144938084034393216853)
                  ·
                    rfl

theorem cell22_1035389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_1035389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035389 prefixEnd_1035389 := by exact prefixLift 1035389
  have htrace : WordTrace (prefixWord ++ tailWord_1035389) baseStart_1035389 baseEnd_1035389 := by
    simpa [prefixWord, tailWord_1035389, baseEnd_1035389] using wordTrace_append hprefix tailTrace_1035389
  have hstable : (prefixWord ++ tailWord_1035389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035389).length < 2 ^ (prefixWord ++ tailWord_1035389).sum := by decide
  have hdescent : baseEnd_1035389 < baseStart_1035389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035393 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1035393 : Nat := 118140960795 + 1035393 * 2 ^ 59
def prefixEnd_1035393 : Nat := 4983230072969 + 3 ^ 40 * 1035393 * 2
def baseEnd_1035393 : Nat := 354436183533848502550547

theorem tailTrace_1035393 : CollatzResearch.WordTrace tailWord_1035393 prefixEnd_1035393 354436183533848502550547 := by
  unfold tailWord_1035393
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763885137955466891270833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175923425303644594180555 37763885137955466891270833)
  ·
    refine ⟨28322913853466600168453125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37763885137955466891270833 28322913853466600168453125)
    ·
      refine ⟨5310546347524987531584961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28322913853466600168453125 5310546347524987531584961)
      ·
        refine ⟨3982909760643740648688721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5310546347524987531584961 3982909760643740648688721)
        ·
          refine ⟨2987182320482805486516541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982909760643740648688721 2987182320482805486516541)
          ·
            refine ⟨1120193370181052057443703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2987182320482805486516541 1120193370181052057443703)
            ·
              refine ⟨1680290055271578086165555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120193370181052057443703 1680290055271578086165555)
              ·
                refine ⟨2520435082907367129248333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680290055271578086165555 2520435082907367129248333)
                ·
                  refine ⟨945163156090262673468125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2520435082907367129248333 945163156090262673468125)
                  ·
                    refine ⟨354436183533848502550547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945163156090262673468125 354436183533848502550547)
                    ·
                      rfl

theorem cell22_1035393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1035393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035393 prefixEnd_1035393 := by exact prefixLift 1035393
  have htrace : WordTrace (prefixWord ++ tailWord_1035393) baseStart_1035393 baseEnd_1035393 := by
    simpa [prefixWord, tailWord_1035393, baseEnd_1035393] using wordTrace_append hprefix tailTrace_1035393
  have hstable : (prefixWord ++ tailWord_1035393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035393).length < 2 ^ (prefixWord ++ tailWord_1035393).sum := by decide
  have hdescent : baseEnd_1035393 < baseStart_1035393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035406 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1035406 : Nat := 118140960795 + 1035406 * 2 ^ 59
def prefixEnd_1035406 : Nat := 4983230072969 + 3 ^ 40 * 1035406 * 2
def baseEnd_1035406 : Nat := 118146877899840267325169

theorem tailTrace_1035406 : CollatzResearch.WordTrace tailWord_1035406 prefixEnd_1035406 118146877899840267325169 := by
  unfold tailWord_1035406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720544910863546263936759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25176239524605580074329381 4720544910863546263936759)
  ·
    refine ⟨7080817366295319395905139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720544910863546263936759 7080817366295319395905139)
    ·
      refine ⟨10621226049442979093857709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7080817366295319395905139 10621226049442979093857709)
      ·
        refine ⟨3982959768541117160196641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10621226049442979093857709 3982959768541117160196641)
        ·
          refine ⟨2987219826405837870147481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982959768541117160196641 2987219826405837870147481)
          ·
            refine ⟨2240414869804378402610611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987219826405837870147481 2240414869804378402610611)
            ·
              refine ⟨3360622304706567603915917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240414869804378402610611 3360622304706567603915917)
              ·
                refine ⟨1260233364264962851468469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3360622304706567603915917 1260233364264962851468469)
                ·
                  refine ⟨118146877899840267325169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1260233364264962851468469 118146877899840267325169)
                  ·
                    rfl

theorem cell22_1035406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1035406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035406 prefixEnd_1035406 := by exact prefixLift 1035406
  have htrace : WordTrace (prefixWord ++ tailWord_1035406) baseStart_1035406 baseEnd_1035406 := by
    simpa [prefixWord, tailWord_1035406, baseEnd_1035406] using wordTrace_append hprefix tailTrace_1035406
  have hstable : (prefixWord ++ tailWord_1035406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035406).length < 2 ^ (prefixWord ++ tailWord_1035406).sum := by decide
  have hdescent : baseEnd_1035406 < baseStart_1035406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035464 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1035464 : Nat := 118140960795 + 1035464 * 2 ^ 59
def prefixEnd_1035464 : Nat := 4983230072969 + 3 ^ 40 * 1035464 * 2
def baseEnd_1035464 : Nat := 354460488284827984025329

theorem tailTrace_1035464 : CollatzResearch.WordTrace tailWord_1035464 prefixEnd_1035464 354460488284827984025329 := by
  unfold tailWord_1035464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883237360349123008552723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25177649813798830678070297 18883237360349123008552723)
  ·
    refine ⟨28324856040523684512829085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18883237360349123008552723 28324856040523684512829085)
    ·
      refine ⟨10621821015196381692310907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28324856040523684512829085 10621821015196381692310907)
      ·
        refine ⟨15932731522794572538466361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621821015196381692310907 15932731522794572538466361)
        ·
          refine ⟨11949548642095929403849771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15932731522794572538466361 11949548642095929403849771)
          ·
            refine ⟨17924322963143894105774657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949548642095929403849771 17924322963143894105774657)
            ·
              refine ⟨13443242222357920579330993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17924322963143894105774657 13443242222357920579330993)
              ·
                refine ⟨10082431666768440434498245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443242222357920579330993 10082431666768440434498245)
                ·
                  refine ⟨1890455937519082581468421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10082431666768440434498245 1890455937519082581468421)
                  ·
                    refine ⟨354460488284827984025329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890455937519082581468421 354460488284827984025329)
                    ·
                      rfl

theorem cell22_1035464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1035464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035464 prefixEnd_1035464 := by exact prefixLift 1035464
  have htrace : WordTrace (prefixWord ++ tailWord_1035464) baseStart_1035464 baseEnd_1035464 := by
    simpa [prefixWord, tailWord_1035464, baseEnd_1035464] using wordTrace_append hprefix tailTrace_1035464
  have hstable : (prefixWord ++ tailWord_1035464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035464).length < 2 ^ (prefixWord ++ tailWord_1035464).sum := by decide
  have hdescent : baseEnd_1035464 < baseStart_1035464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035466 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1035466 : Nat := 118140960795 + 1035466 * 2 ^ 59
def prefixEnd_1035466 : Nat := 4983230072969 + 3 ^ 40 * 1035466 * 2
def baseEnd_1035466 : Nat := 354461172925700645475323

theorem tailTrace_1035466 : CollatzResearch.WordTrace tailWord_1035466 prefixEnd_1035466 354461172925700645475323 := by
  unfold tailWord_1035466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441636916672750089669563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25177698444460666905785501 9441636916672750089669563)
  ·
    refine ⟨14162455375009125134504345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441636916672750089669563 14162455375009125134504345)
    ·
      refine ⟨10621841531256843850878259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14162455375009125134504345 10621841531256843850878259)
      ·
        refine ⟨15932762296885265776317389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621841531256843850878259 15932762296885265776317389)
        ·
          refine ⟨5974785861331974666119021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15932762296885265776317389 5974785861331974666119021)
          ·
            refine ⟨2240544697999490499794633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5974785861331974666119021 2240544697999490499794633)
            ·
              refine ⟨1680408523499617874845975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240544697999490499794633 1680408523499617874845975)
              ·
                refine ⟨2520612785249426812268963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680408523499617874845975 2520612785249426812268963)
                ·
                  refine ⟨3780919177874140218403445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520612785249426812268963 3780919177874140218403445)
                  ·
                    refine ⟨354461172925700645475323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3780919177874140218403445 354461172925700645475323)
                    ·
                      rfl

theorem cell22_1035466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1035466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035466 prefixEnd_1035466 := by exact prefixLift 1035466
  have htrace : WordTrace (prefixWord ++ tailWord_1035466) baseStart_1035466 baseEnd_1035466 := by
    simpa [prefixWord, tailWord_1035466, baseEnd_1035466] using wordTrace_append hprefix tailTrace_1035466
  have hstable : (prefixWord ++ tailWord_1035466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035466).length < 2 ^ (prefixWord ++ tailWord_1035466).sum := by decide
  have hdescent : baseEnd_1035466 < baseStart_1035466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035485 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 4]
def baseStart_1035485 : Nat := 118140960795 + 1035485 * 2 ^ 59
def prefixEnd_1035485 : Nat := 4983230072969 + 3 ^ 40 * 1035485 * 2
def baseEnd_1035485 : Nat := 118155892337996976416755

theorem tailTrace_1035485 : CollatzResearch.WordTrace tailWord_1035485 prefixEnd_1035485 118155892337996976416755 := by
  unfold tailWord_1035485
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767240653622166603619909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25178160435748111069079939 37767240653622166603619909)
  ·
    refine ⟨7081357622554156238178733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37767240653622166603619909 7081357622554156238178733)
    ·
      refine ⟨2655509108457808589317025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7081357622554156238178733 2655509108457808589317025)
      ·
        refine ⟨1991631831343356441987769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655509108457808589317025 1991631831343356441987769)
        ·
          refine ⟨1493723873507517331490827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991631831343356441987769 1493723873507517331490827)
          ·
            refine ⟨2240585810261275997236241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493723873507517331490827 2240585810261275997236241)
            ·
              refine ⟨1680439357695956997927181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240585810261275997236241 1680439357695956997927181)
              ·
                refine ⟨630164759135983874222693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680439357695956997927181 630164759135983874222693)
                ·
                  refine ⟨118155892337996976416755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630164759135983874222693 118155892337996976416755)
                  ·
                    rfl

theorem cell22_1035485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_1035485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035485 prefixEnd_1035485 := by exact prefixLift 1035485
  have htrace : WordTrace (prefixWord ++ tailWord_1035485) baseStart_1035485 baseEnd_1035485 := by
    simpa [prefixWord, tailWord_1035485, baseEnd_1035485] using wordTrace_append hprefix tailTrace_1035485
  have hstable : (prefixWord ++ tailWord_1035485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035485).length < 2 ^ (prefixWord ++ tailWord_1035485).sum := by decide
  have hdescent : baseEnd_1035485 < baseStart_1035485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035599 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1035599 : Nat := 118140960795 + 1035599 * 2 ^ 59
def prefixEnd_1035599 : Nat := 4983230072969 + 3 ^ 40 * 1035599 * 2
def baseEnd_1035599 : Nat := 354506701543732631899915

theorem tailTrace_1035599 : CollatzResearch.WordTrace tailWord_1035599 prefixEnd_1035599 354506701543732631899915 := by
  unfold tailWord_1035599
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771398575209164073269851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25180932383472776048846567 37771398575209164073269851)
  ·
    refine ⟨56657097862813746109904777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37771398575209164073269851 56657097862813746109904777)
    ·
      refine ⟨42492823397110309582428583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56657097862813746109904777 42492823397110309582428583)
      ·
        refine ⟨63739235095665464373642875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42492823397110309582428583 63739235095665464373642875)
        ·
          refine ⟨95608852643498196560464313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63739235095665464373642875 95608852643498196560464313)
          ·
            refine ⟨71706639482623647420348235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95608852643498196560464313 71706639482623647420348235)
            ·
              refine ⟨107559959223935471130522353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71706639482623647420348235 107559959223935471130522353)
              ·
                refine ⟨80669969417951603347891765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107559959223935471130522353 80669969417951603347891765)
                ·
                  refine ⟨7562809632932962813864853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80669969417951603347891765 7562809632932962813864853)
                  ·
                    refine ⟨354506701543732631899915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7562809632932962813864853 354506701543732631899915)
                    ·
                      rfl

theorem cell22_1035599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1035599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035599 prefixEnd_1035599 := by exact prefixLift 1035599
  have htrace : WordTrace (prefixWord ++ tailWord_1035599) baseStart_1035599 baseEnd_1035599 := by
    simpa [prefixWord, tailWord_1035599, baseEnd_1035599] using wordTrace_append hprefix tailTrace_1035599
  have hstable : (prefixWord ++ tailWord_1035599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035599).length < 2 ^ (prefixWord ++ tailWord_1035599).sum := by decide
  have hdescent : baseEnd_1035599 < baseStart_1035599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035601 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_1035601 : Nat := 118140960795 + 1035601 * 2 ^ 59
def prefixEnd_1035601 : Nat := 4983230072969 + 3 ^ 40 * 1035601 * 2
def baseEnd_1035601 : Nat := 354507386184605293349909

theorem tailTrace_1035601 : CollatzResearch.WordTrace tailWord_1035601 prefixEnd_1035601 354507386184605293349909 := by
  unfold tailWord_1035601
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771471521201918414842657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25180981014134612276561771 37771471521201918414842657)
  ·
    refine ⟨28328603640901438811131993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37771471521201918414842657 28328603640901438811131993)
    ·
      refine ⟨21246452730676079108348995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28328603640901438811131993 21246452730676079108348995)
      ·
        refine ⟨31869679096014118662523493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21246452730676079108348995 31869679096014118662523493)
        ·
          refine ⟨5975564830502647249223155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31869679096014118662523493 5975564830502647249223155)
          ·
            refine ⟨8963347245753970873834733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975564830502647249223155 8963347245753970873834733)
            ·
              refine ⟨3361255217157739077688025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8963347245753970873834733 3361255217157739077688025)
              ·
                refine ⟨2520941412868304308266019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361255217157739077688025 2520941412868304308266019)
                ·
                  refine ⟨3781412119302456462399029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520941412868304308266019 3781412119302456462399029)
                  ·
                    refine ⟨354507386184605293349909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3781412119302456462399029 354507386184605293349909)
                    ·
                      rfl

theorem cell22_1035601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_1035601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035601 prefixEnd_1035601 := by exact prefixLift 1035601
  have htrace : WordTrace (prefixWord ++ tailWord_1035601) baseStart_1035601 baseEnd_1035601 := by
    simpa [prefixWord, tailWord_1035601, baseEnd_1035601] using wordTrace_append hprefix tailTrace_1035601
  have hstable : (prefixWord ++ tailWord_1035601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035601).length < 2 ^ (prefixWord ++ tailWord_1035601).sum := by decide
  have hdescent : baseEnd_1035601 < baseStart_1035601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035605 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_1035605 : Nat := 118140960795 + 1035605 * 2 ^ 59
def prefixEnd_1035605 : Nat := 4983230072969 + 3 ^ 40 * 1035605 * 2
def baseEnd_1035605 : Nat := 354508755466350616249897

theorem tailTrace_1035605 : CollatzResearch.WordTrace tailWord_1035605 prefixEnd_1035605 354508755466350616249897 := by
  unfold tailWord_1035605
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771617413187427097988269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181078275458284731992179 37771617413187427097988269)
  ·
    refine ⟨14164356529945285161745601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37771617413187427097988269 14164356529945285161745601)
    ·
      refine ⟨10623267397458963871309201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14164356529945285161745601 10623267397458963871309201)
      ·
        refine ⟨7967450548094222903481901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10623267397458963871309201 7967450548094222903481901)
        ·
          refine ⟨2987793955535333588805713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7967450548094222903481901 2987793955535333588805713)
          ·
            refine ⟨2240845466651500191604285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987793955535333588805713 2240845466651500191604285)
            ·
              refine ⟨840317049994312571851607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2240845466651500191604285 840317049994312571851607)
              ·
                refine ⟨1260475574991468857777411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840317049994312571851607 1260475574991468857777411)
                ·
                  refine ⟨1890713362487203286666117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260475574991468857777411 1890713362487203286666117)
                  ·
                    refine ⟨354508755466350616249897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890713362487203286666117 354508755466350616249897)
                    ·
                      rfl

theorem cell22_1035605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_1035605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035605 prefixEnd_1035605 := by exact prefixLift 1035605
  have htrace : WordTrace (prefixWord ++ tailWord_1035605) baseStart_1035605 baseEnd_1035605 := by
    simpa [prefixWord, tailWord_1035605, baseEnd_1035605] using wordTrace_append hprefix tailTrace_1035605
  have hstable : (prefixWord ++ tailWord_1035605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035605).length < 2 ^ (prefixWord ++ tailWord_1035605).sum := by decide
  have hdescent : baseEnd_1035605 < baseStart_1035605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035613 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1035613 : Nat := 118140960795 + 1035613 * 2 ^ 59
def prefixEnd_1035613 : Nat := 4983230072969 + 3 ^ 40 * 1035613 * 2
def baseEnd_1035613 : Nat := 354511494029841262049873

theorem tailTrace_1035613 : CollatzResearch.WordTrace tailWord_1035613 prefixEnd_1035613 354511494029841262049873 := by
  unfold tailWord_1035613
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771909197158444464279493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181272798105629642852995 37771909197158444464279493)
  ·
    refine ⟨7082232974467208337052405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37771909197158444464279493 7082232974467208337052405)
    ·
      refine ⟨663959341356300781598663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7082232974467208337052405 663959341356300781598663)
      ·
        refine ⟨995939012034451172397995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663959341356300781598663 995939012034451172397995)
        ·
          refine ⟨1493908518051676758596993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995939012034451172397995 1493908518051676758596993)
          ·
            refine ⟨1120431388538757568947745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493908518051676758596993 1120431388538757568947745)
            ·
              refine ⟨840323541404068176710809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120431388538757568947745 840323541404068176710809)
              ·
                refine ⟨630242656053051132533107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840323541404068176710809 630242656053051132533107)
                ·
                  refine ⟨945363984079576698799661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630242656053051132533107 945363984079576698799661)
                  ·
                    refine ⟨354511494029841262049873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945363984079576698799661 354511494029841262049873)
                    ·
                      rfl

theorem cell22_1035613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1035613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035613 prefixEnd_1035613 := by exact prefixLift 1035613
  have htrace : WordTrace (prefixWord ++ tailWord_1035613) baseStart_1035613 baseEnd_1035613 := by
    simpa [prefixWord, tailWord_1035613, baseEnd_1035613] using wordTrace_append hprefix tailTrace_1035613
  have hstable : (prefixWord ++ tailWord_1035613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035613).length < 2 ^ (prefixWord ++ tailWord_1035613).sum := by decide
  have hdescent : baseEnd_1035613 < baseStart_1035613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035620 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_1035620 : Nat := 118140960795 + 1035620 * 2 ^ 59
def prefixEnd_1035620 : Nat := 4983230072969 + 3 ^ 40 * 1035620 * 2
def baseEnd_1035620 : Nat := 118171296757631859041617

theorem tailTrace_1035620 : CollatzResearch.WordTrace tailWord_1035620 prefixEnd_1035620 118171296757631859041617 := by
  unfold tailWord_1035620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886082254066542329892157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25181443005422056439856209 18886082254066542329892157)
  ·
    refine ⟨7082280845274953373709559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18886082254066542329892157 7082280845274953373709559)
    ·
      refine ⟨10623421267912430060564339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082280845274953373709559 10623421267912430060564339)
      ·
        refine ⟨15935131901868645090846509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10623421267912430060564339 15935131901868645090846509)
        ·
          refine ⟨5975674463200741909067441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15935131901868645090846509 5975674463200741909067441)
          ·
            refine ⟨4481755847400556431800581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5975674463200741909067441 4481755847400556431800581)
            ·
              refine ⟨840329221387604330962609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4481755847400556431800581 840329221387604330962609)
              ·
                refine ⟨630246916040703248221957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840329221387604330962609 630246916040703248221957)
                ·
                  refine ⟨118171296757631859041617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630246916040703248221957 118171296757631859041617)
                  ·
                    rfl

theorem cell22_1035620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_1035620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035620 prefixEnd_1035620 := by exact prefixLift 1035620
  have htrace : WordTrace (prefixWord ++ tailWord_1035620) baseStart_1035620 baseEnd_1035620 := by
    simpa [prefixWord, tailWord_1035620, baseEnd_1035620] using wordTrace_append hprefix tailTrace_1035620
  have hstable : (prefixWord ++ tailWord_1035620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035620).length < 2 ^ (prefixWord ++ tailWord_1035620).sum := by decide
  have hdescent : baseEnd_1035620 < baseStart_1035620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035650 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1035650 : Nat := 118140960795 + 1035650 * 2 ^ 59
def prefixEnd_1035650 : Nat := 4983230072969 + 3 ^ 40 * 1035650 * 2
def baseEnd_1035650 : Nat := 354524159885985498874759

theorem tailTrace_1035650 : CollatzResearch.WordTrace tailWord_1035650 prefixEnd_1035650 354524159885985498874759 := by
  unfold tailWord_1035650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443314674506099945844101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25182172465349599855584269 9443314674506099945844101)
  ·
    refine ⟨1770621501469893739845769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9443314674506099945844101 1770621501469893739845769)
    ·
      refine ⟨1327966126102420304884327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1770621501469893739845769 1327966126102420304884327)
      ·
        refine ⟨1991949189153630457326491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327966126102420304884327 1991949189153630457326491)
        ·
          refine ⟨2987923783730445685989737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991949189153630457326491 2987923783730445685989737)
          ·
            refine ⟨2240942837797834264492303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987923783730445685989737 2240942837797834264492303)
            ·
              refine ⟨3361414256696751396738455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240942837797834264492303 3361414256696751396738455)
              ·
                refine ⟨5042121385045127095107683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361414256696751396738455 5042121385045127095107683)
                ·
                  refine ⟨7563182077567690642661525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042121385045127095107683 7563182077567690642661525)
                  ·
                    refine ⟨354524159885985498874759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7563182077567690642661525 354524159885985498874759)
                    ·
                      rfl

theorem cell22_1035650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1035650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035650 prefixEnd_1035650 := by exact prefixLift 1035650
  have htrace : WordTrace (prefixWord ++ tailWord_1035650) baseStart_1035650 baseEnd_1035650 := by
    simpa [prefixWord, tailWord_1035650, baseEnd_1035650] using wordTrace_append hprefix tailTrace_1035650
  have hstable : (prefixWord ++ tailWord_1035650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035650).length < 2 ^ (prefixWord ++ tailWord_1035650).sum := by decide
  have hdescent : baseEnd_1035650 < baseStart_1035650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035680 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 1, 3]
def baseStart_1035680 : Nat := 118140960795 + 1035680 * 2 ^ 59
def prefixEnd_1035680 : Nat := 4983230072969 + 3 ^ 40 * 1035680 * 2
def baseEnd_1035680 : Nat := 354534429499075420624667

theorem tailTrace_1035680 : CollatzResearch.WordTrace tailWord_1035680 prefixEnd_1035680 354534429499075420624667 := by
  unfold tailWord_1035680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887176443957857453484247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25182901925277143271312329 18887176443957857453484247)
  ·
    refine ⟨28330764665936786180226371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18887176443957857453484247 28330764665936786180226371)
    ·
      refine ⟨42496146998905179270339557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330764665936786180226371 42496146998905179270339557)
      ·
        refine ⟨7968027562294721113188667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42496146998905179270339557 7968027562294721113188667)
        ·
          refine ⟨11952041343442081669783001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968027562294721113188667 11952041343442081669783001)
          ·
            refine ⟨8964031007581561252337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11952041343442081669783001 8964031007581561252337251)
            ·
              refine ⟨13446046511372341878505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964031007581561252337251 13446046511372341878505877)
              ·
                refine ⟨630283430220578525554963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13446046511372341878505877 630283430220578525554963)
                ·
                  refine ⟨945425145330867788332445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630283430220578525554963 945425145330867788332445)
                  ·
                    refine ⟨354534429499075420624667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945425145330867788332445 354534429499075420624667)
                    ·
                      rfl

theorem cell22_1035680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_1035680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035680 prefixEnd_1035680 := by exact prefixLift 1035680
  have htrace : WordTrace (prefixWord ++ tailWord_1035680) baseStart_1035680 baseEnd_1035680 := by
    simpa [prefixWord, tailWord_1035680, baseEnd_1035680] using wordTrace_append hprefix tailTrace_1035680
  have hstable : (prefixWord ++ tailWord_1035680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035680).length < 2 ^ (prefixWord ++ tailWord_1035680).sum := by decide
  have hdescent : baseEnd_1035680 < baseStart_1035680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035723 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 1, 4]
def baseStart_1035723 : Nat := 118140960795 + 1035723 * 2 ^ 59
def prefixEnd_1035723 : Nat := 4983230072969 + 3 ^ 40 * 1035723 * 2
def baseEnd_1035723 : Nat := 354549149277837641799535

theorem tailTrace_1035723 : CollatzResearch.WordTrace tailWord_1035723 prefixEnd_1035723 354549149277837641799535 := by
  unfold tailWord_1035723
  simp only [CollatzResearch.WordTrace]
  refine ⟨37775921226759933250783823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25183947484506622167189215 37775921226759933250783823)
  ·
    refine ⟨56663881840139899876175735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37775921226759933250783823 56663881840139899876175735)
    ·
      refine ⟨84995822760209849814263603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56663881840139899876175735 84995822760209849814263603)
      ·
        refine ⟨127493734140314774721395405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84995822760209849814263603 127493734140314774721395405)
        ·
          refine ⟨47810150302618040520523277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127493734140314774721395405 47810150302618040520523277)
          ·
            refine ⟨17928806363481765195196229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47810150302618040520523277 17928806363481765195196229)
            ·
              refine ⟨3361651193152830974099293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17928806363481765195196229 3361651193152830974099293)
              ·
                refine ⟨1260619197432311615287235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361651193152830974099293 1260619197432311615287235)
                ·
                  refine ⟨1890928796148467422930853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260619197432311615287235 1890928796148467422930853)
                  ·
                    refine ⟨354549149277837641799535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890928796148467422930853 354549149277837641799535)
                    ·
                      rfl

theorem cell22_1035723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4].length) (baseStart_1035723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035723 prefixEnd_1035723 := by exact prefixLift 1035723
  have htrace : WordTrace (prefixWord ++ tailWord_1035723) baseStart_1035723 baseEnd_1035723 := by
    simpa [prefixWord, tailWord_1035723, baseEnd_1035723] using wordTrace_append hprefix tailTrace_1035723
  have hstable : (prefixWord ++ tailWord_1035723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035723).length < 2 ^ (prefixWord ++ tailWord_1035723).sum := by decide
  have hdescent : baseEnd_1035723 < baseStart_1035723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035738 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_1035738 : Nat := 118140960795 + 1035738 * 2 ^ 59
def prefixEnd_1035738 : Nat := 4983230072969 + 3 ^ 40 * 1035738 * 2
def baseEnd_1035738 : Nat := 118184761361460867558163

theorem tailTrace_1035738 : CollatzResearch.WordTrace tailWord_1035738 prefixEnd_1035738 118184761361460867558163 := by
  unfold tailWord_1035738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444117080426397703144967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25184312214470393875053245 9444117080426397703144967)
  ·
    refine ⟨14166175620639596554717451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9444117080426397703144967 14166175620639596554717451)
    ·
      refine ⟨21249263430959394832076177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14166175620639596554717451 21249263430959394832076177)
      ·
        refine ⟨15936947573219546124057133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21249263430959394832076177 15936947573219546124057133)
        ·
          refine ⟨5976355339957329796521425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15936947573219546124057133 5976355339957329796521425)
          ·
            refine ⟨4482266504967997347391069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976355339957329796521425 4482266504967997347391069)
            ·
              refine ⟨1680849939362999005271651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4482266504967997347391069 1680849939362999005271651)
              ·
                refine ⟨2521274909044498507907477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680849939362999005271651 2521274909044498507907477)
                ·
                  refine ⟨118184761361460867558163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2521274909044498507907477 118184761361460867558163)
                  ·
                    rfl

theorem cell22_1035738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_1035738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035738 prefixEnd_1035738 := by exact prefixLift 1035738
  have htrace : WordTrace (prefixWord ++ tailWord_1035738) baseStart_1035738 baseEnd_1035738 := by
    simpa [prefixWord, tailWord_1035738, baseEnd_1035738] using wordTrace_append hprefix tailTrace_1035738
  have hstable : (prefixWord ++ tailWord_1035738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035738).length < 2 ^ (prefixWord ++ tailWord_1035738).sum := by decide
  have hdescent : baseEnd_1035738 < baseStart_1035738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035768 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1035768 : Nat := 118140960795 + 1035768 * 2 ^ 59
def prefixEnd_1035768 : Nat := 4983230072969 + 3 ^ 40 * 1035768 * 2
def baseEnd_1035768 : Nat := 354564553697472524424397

theorem tailTrace_1035768 : CollatzResearch.WordTrace tailWord_1035768 prefixEnd_1035768 354564553697472524424397 := by
  unfold tailWord_1035768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888781255798452968085979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25185041674397937290781305 18888781255798452968085979)
  ·
    refine ⟨28333171883697679452128969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888781255798452968085979 28333171883697679452128969)
    ·
      refine ⟨21249878912773259589096727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28333171883697679452128969 21249878912773259589096727)
      ·
        refine ⟨31874818369159889383645091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21249878912773259589096727 31874818369159889383645091)
        ·
          refine ⟨47812227553739834075467637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31874818369159889383645091 47812227553739834075467637)
          ·
            refine ⟨4482396333163109444575091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47812227553739834075467637 4482396333163109444575091)
            ·
              refine ⟨6723594499744664166862637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482396333163109444575091 6723594499744664166862637)
              ·
                refine ⟨2521347937404249062573489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723594499744664166862637 2521347937404249062573489)
                ·
                  refine ⟨1891010953053186796930117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521347937404249062573489 1891010953053186796930117)
                  ·
                    refine ⟨354564553697472524424397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891010953053186796930117 354564553697472524424397)
                    ·
                      rfl

theorem cell22_1035768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1035768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035768 prefixEnd_1035768 := by exact prefixLift 1035768
  have htrace : WordTrace (prefixWord ++ tailWord_1035768) baseStart_1035768 baseEnd_1035768 := by
    simpa [prefixWord, tailWord_1035768, baseEnd_1035768] using wordTrace_append hprefix tailTrace_1035768
  have hstable : (prefixWord ++ tailWord_1035768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035768).length < 2 ^ (prefixWord ++ tailWord_1035768).sum := by decide
  have hdescent : baseEnd_1035768 < baseStart_1035768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035782 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1035782 : Nat := 118140960795 + 1035782 * 2 ^ 59
def prefixEnd_1035782 : Nat := 4983230072969 + 3 ^ 40 * 1035782 * 2
def baseEnd_1035782 : Nat := 354569346183581154574355

theorem tailTrace_1035782 : CollatzResearch.WordTrace tailWord_1035782 prefixEnd_1035782 354569346183581154574355 := by
  unfold tailWord_1035782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180564785423318322724425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25185382089030790884787733 1180564785423318322724425)
  ·
    refine ⟨885423589067488742043319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1180564785423318322724425 885423589067488742043319)
    ·
      refine ⟨1328135383601233113064979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885423589067488742043319 1328135383601233113064979)
      ·
        refine ⟨1992203075401849669597469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328135383601233113064979 1992203075401849669597469)
        ·
          refine ⟨747076153275693626099051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1992203075401849669597469 747076153275693626099051)
          ·
            refine ⟨1120614229913540439148577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747076153275693626099051 1120614229913540439148577)
            ·
              refine ⟨840460672435155329361433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120614229913540439148577 840460672435155329361433)
              ·
                refine ⟨630345504326366497021075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840460672435155329361433 630345504326366497021075)
                ·
                  refine ⟨945518256489549745531613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630345504326366497021075 945518256489549745531613)
                  ·
                    refine ⟨354569346183581154574355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945518256489549745531613 354569346183581154574355)
                    ·
                      rfl

theorem cell22_1035782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1035782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035782 prefixEnd_1035782 := by exact prefixLift 1035782
  have htrace : WordTrace (prefixWord ++ tailWord_1035782) baseStart_1035782 baseEnd_1035782 := by
    simpa [prefixWord, tailWord_1035782, baseEnd_1035782] using wordTrace_append hprefix tailTrace_1035782
  have hstable : (prefixWord ++ tailWord_1035782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035782).length < 2 ^ (prefixWord ++ tailWord_1035782).sum := by decide
  have hdescent : baseEnd_1035782 < baseStart_1035782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035787 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 2, 3]
def baseStart_1035787 : Nat := 118140960795 + 1035787 * 2 ^ 59
def prefixEnd_1035787 : Nat := 4983230072969 + 3 ^ 40 * 1035787 * 2
def baseEnd_1035787 : Nat := 354571057785762808199339

theorem tailTrace_1035787 : CollatzResearch.WordTrace tailWord_1035787 prefixEnd_1035787 354571057785762808199339 := by
  unfold tailWord_1035787
  simp only [CollatzResearch.WordTrace]
  refine ⟨37778255498528072181113615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25185503665685381454075743 37778255498528072181113615)
  ·
    refine ⟨56667383247792108271670423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37778255498528072181113615 56667383247792108271670423)
    ·
      refine ⟨85001074871688162407505635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56667383247792108271670423 85001074871688162407505635)
      ·
        refine ⟨127501612307532243611258453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85001074871688162407505635 127501612307532243611258453)
        ·
          refine ⟨1494159519228893479819435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 127501612307532243611258453 1494159519228893479819435)
          ·
            refine ⟨2241239278843340219729153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494159519228893479819435 2241239278843340219729153)
            ·
              refine ⟨1680929459132505164796865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241239278843340219729153 1680929459132505164796865)
              ·
                refine ⟨1260697094349378873597649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680929459132505164796865 1260697094349378873597649)
                ·
                  refine ⟨945522820762034155198237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1260697094349378873597649 945522820762034155198237)
                  ·
                    refine ⟨354571057785762808199339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945522820762034155198237 354571057785762808199339)
                    ·
                      rfl

theorem cell22_1035787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3].length) (baseStart_1035787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035787 prefixEnd_1035787 := by exact prefixLift 1035787
  have htrace : WordTrace (prefixWord ++ tailWord_1035787) baseStart_1035787 baseEnd_1035787 := by
    simpa [prefixWord, tailWord_1035787, baseEnd_1035787] using wordTrace_append hprefix tailTrace_1035787
  have hstable : (prefixWord ++ tailWord_1035787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035787).length < 2 ^ (prefixWord ++ tailWord_1035787).sum := by decide
  have hdescent : baseEnd_1035787 < baseStart_1035787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035800 : List Nat := [2, 1, 2, 3, 4, 2, 1, 7]
def baseStart_1035800 : Nat := 118140960795 + 1035800 * 2 ^ 59
def prefixEnd_1035800 : Nat := 4983230072969 + 3 ^ 40 * 1035800 * 2
def baseEnd_1035800 : Nat := 39397278661270567513811

theorem tailTrace_1035800 : CollatzResearch.WordTrace tailWord_1035800 prefixEnd_1035800 39397278661270567513811 := by
  unfold tailWord_1035800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889364823740487700668427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25185819764987316934224569 18889364823740487700668427)
  ·
    refine ⟨28334047235610731551002641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889364823740487700668427 28334047235610731551002641)
    ·
      refine ⟨21250535426708048663251981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28334047235610731551002641 21250535426708048663251981)
      ·
        refine ⟨7968950785015518248719493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21250535426708048663251981 7968950785015518248719493)
        ·
          refine ⟨1494178272190409671634905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7968950785015518248719493 1494178272190409671634905)
          ·
            refine ⟨1120633704142807253726179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494178272190409671634905 1120633704142807253726179)
            ·
              refine ⟨1680950556214210880589269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120633704142807253726179 1680950556214210880589269)
              ·
                refine ⟨39397278661270567513811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1680950556214210880589269 39397278661270567513811)
                ·
                  rfl

theorem cell22_1035800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_1035800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035800 prefixEnd_1035800 := by exact prefixLift 1035800
  have htrace : WordTrace (prefixWord ++ tailWord_1035800) baseStart_1035800 baseEnd_1035800 := by
    simpa [prefixWord, tailWord_1035800, baseEnd_1035800] using wordTrace_append hprefix tailTrace_1035800
  have hstable : (prefixWord ++ tailWord_1035800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035800).length < 2 ^ (prefixWord ++ tailWord_1035800).sum := by decide
  have hdescent : baseEnd_1035800 < baseStart_1035800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035832 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 1, 3]
def baseStart_1035832 : Nat := 118140960795 + 1035832 * 2 ^ 59
def prefixEnd_1035832 : Nat := 4983230072969 + 3 ^ 40 * 1035832 * 2
def baseEnd_1035832 : Nat := 354586462205397690824201

theorem tailTrace_1035832 : CollatzResearch.WordTrace tailWord_1035832 prefixEnd_1035832 354586462205397690824201 := by
  unfold tailWord_1035832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889948391682522433250875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25186597855576696577667833 18889948391682522433250875)
  ·
    refine ⟨28334922587523783649876313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889948391682522433250875 28334922587523783649876313)
    ·
      refine ⟨21251191940642837737407235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28334922587523783649876313 21251191940642837737407235)
      ·
        refine ⟨31876787910964256606110853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21251191940642837737407235 31876787910964256606110853)
        ·
          refine ⟨5976897733305798113645785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31876787910964256606110853 5976897733305798113645785)
          ·
            refine ⟨4482673299979348585234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976897733305798113645785 4482673299979348585234339)
            ·
              refine ⟨6724009949969022877851509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482673299979348585234339 6724009949969022877851509)
              ·
                refine ⟨630375932809595894798579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6724009949969022877851509 630375932809595894798579)
                ·
                  refine ⟨945563899214393842197869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630375932809595894798579 945563899214393842197869)
                  ·
                    refine ⟨354586462205397690824201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945563899214393842197869 354586462205397690824201)
                    ·
                      rfl

theorem cell22_1035832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_1035832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035832 prefixEnd_1035832 := by exact prefixLift 1035832
  have htrace : WordTrace (prefixWord ++ tailWord_1035832) baseStart_1035832 baseEnd_1035832 := by
    simpa [prefixWord, tailWord_1035832, baseEnd_1035832] using wordTrace_append hprefix tailTrace_1035832
  have hstable : (prefixWord ++ tailWord_1035832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035832).length < 2 ^ (prefixWord ++ tailWord_1035832).sum := by decide
  have hdescent : baseEnd_1035832 < baseStart_1035832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035873 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 6]
def baseStart_1035873 : Nat := 118140960795 + 1035873 * 2 ^ 59
def prefixEnd_1035873 : Nat := 4983230072969 + 3 ^ 40 * 1035873 * 2
def baseEnd_1035873 : Nat := 118200165781095750183025

theorem tailTrace_1035873 : CollatzResearch.WordTrace tailWord_1035873 prefixEnd_1035873 118200165781095750183025 := by
  unfold tailWord_1035873
  simp only [CollatzResearch.WordTrace]
  refine ⟨37781392176216508868744273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25187594784144339245829515 37781392176216508868744273)
  ·
    refine ⟨28336044132162381651558205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37781392176216508868744273 28336044132162381651558205)
    ·
      refine ⟨10626016549560893119334327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28336044132162381651558205 10626016549560893119334327)
      ·
        refine ⟨15939024824341339679001491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626016549560893119334327 15939024824341339679001491)
        ·
          refine ⟨23908537236512009518502237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15939024824341339679001491 23908537236512009518502237)
          ·
            refine ⟨8965701463692003569438339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23908537236512009518502237 8965701463692003569438339)
            ·
              refine ⟨13448552195538005354157509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965701463692003569438339 13448552195538005354157509)
              ·
                refine ⟨2521603536663376003904533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13448552195538005354157509 2521603536663376003904533)
                ·
                  refine ⟨118200165781095750183025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2521603536663376003904533 118200165781095750183025)
                  ·
                    rfl

theorem cell22_1035873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_1035873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035873 prefixEnd_1035873 := by exact prefixLift 1035873
  have htrace : WordTrace (prefixWord ++ tailWord_1035873) baseStart_1035873 baseEnd_1035873 := by
    simpa [prefixWord, tailWord_1035873, baseEnd_1035873] using wordTrace_append hprefix tailTrace_1035873
  have hstable : (prefixWord ++ tailWord_1035873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035873).length < 2 ^ (prefixWord ++ tailWord_1035873).sum := by decide
  have hdescent : baseEnd_1035873 < baseStart_1035873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035875 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 1, 4]
def baseStart_1035875 : Nat := 118140960795 + 1035875 * 2 ^ 59
def prefixEnd_1035875 : Nat := 4983230072969 + 3 ^ 40 * 1035875 * 2
def baseEnd_1035875 : Nat := 354601181984159911999069

theorem tailTrace_1035875 : CollatzResearch.WordTrace tailWord_1035875 prefixEnd_1035875 354601181984159911999069 := by
  unfold tailWord_1035875
  simp only [CollatzResearch.WordTrace]
  refine ⟨37781465122209263210317079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25187643414806175473544719 37781465122209263210317079)
  ·
    refine ⟨56672197683313894815475619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37781465122209263210317079 56672197683313894815475619)
    ·
      refine ⟨85008296524970842223213429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56672197683313894815475619 85008296524970842223213429)
      ·
        refine ⟨7969527799216016458426259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85008296524970842223213429 7969527799216016458426259)
        ·
          refine ⟨11954291698824024687639389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969527799216016458426259 11954291698824024687639389)
          ·
            refine ⟨4482859387059009257864771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11954291698824024687639389 4482859387059009257864771)
            ·
              refine ⟨6724289080588513886797157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482859387059009257864771 6724289080588513886797157)
              ·
                refine ⟨1260804202610346353774467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6724289080588513886797157 1260804202610346353774467)
                ·
                  refine ⟨1891206303915519530661701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260804202610346353774467 1891206303915519530661701)
                  ·
                    refine ⟨354601181984159911999069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891206303915519530661701 354601181984159911999069)
                    ·
                      rfl

theorem cell22_1035875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4].length) (baseStart_1035875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035875 prefixEnd_1035875 := by exact prefixLift 1035875
  have htrace : WordTrace (prefixWord ++ tailWord_1035875) baseStart_1035875 baseEnd_1035875 := by
    simpa [prefixWord, tailWord_1035875, baseEnd_1035875] using wordTrace_append hprefix tailTrace_1035875
  have hstable : (prefixWord ++ tailWord_1035875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035875).length < 2 ^ (prefixWord ++ tailWord_1035875).sum := by decide
  have hdescent : baseEnd_1035875 < baseStart_1035875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035937 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1035937 : Nat := 118140960795 + 1035937 * 2 ^ 59
def prefixEnd_1035937 : Nat := 4983230072969 + 3 ^ 40 * 1035937 * 2
def baseEnd_1035937 : Nat := 354622405851212416948879

theorem tailTrace_1035937 : CollatzResearch.WordTrace tailWord_1035937 prefixEnd_1035937 354622405851212416948879 := by
  unfold tailWord_1035937
  simp only [CollatzResearch.WordTrace]
  refine ⟨37783726447984647799074065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25189150965323098532716043 37783726447984647799074065)
  ·
    refine ⟨28337794835988485849305549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37783726447984647799074065 28337794835988485849305549)
    ·
      refine ⟨10626673063495682193489581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28337794835988485849305549 10626673063495682193489581)
      ·
        refine ⟨3985002398810880822558593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10626673063495682193489581 3985002398810880822558593)
        ·
          refine ⟨2988751799108160616918945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3985002398810880822558593 2988751799108160616918945)
          ·
            refine ⟨2241563849331120462689209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2988751799108160616918945 2241563849331120462689209)
            ·
              refine ⟨1681172886998340347016907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241563849331120462689209 1681172886998340347016907)
              ·
                refine ⟨2521759330497510520525361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681172886998340347016907 2521759330497510520525361)
                ·
                  refine ⟨1891319497873132890394021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521759330497510520525361 1891319497873132890394021)
                  ·
                    refine ⟨354622405851212416948879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891319497873132890394021 354622405851212416948879)
                    ·
                      rfl

theorem cell22_1035937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1035937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035937 prefixEnd_1035937 := by exact prefixLift 1035937
  have htrace : WordTrace (prefixWord ++ tailWord_1035937) baseStart_1035937 baseEnd_1035937 := by
    simpa [prefixWord, tailWord_1035937, baseEnd_1035937] using wordTrace_append hprefix tailTrace_1035937
  have hstable : (prefixWord ++ tailWord_1035937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035937).length < 2 ^ (prefixWord ++ tailWord_1035937).sum := by decide
  have hdescent : baseEnd_1035937 < baseStart_1035937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035948 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1035948 : Nat := 118140960795 + 1035948 * 2 ^ 59
def prefixEnd_1035948 : Nat := 4983230072969 + 3 ^ 40 * 1035948 * 2
def baseEnd_1035948 : Nat := 354626171376012054923845

theorem tailTrace_1035948 : CollatzResearch.WordTrace tailWord_1035948 prefixEnd_1035948 354626171376012054923845 := by
  unfold tailWord_1035948
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892063825472398338862249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25189418433963197785149665 18892063825472398338862249)
  ·
    refine ⟨14169047869104298754146687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18892063825472398338862249 14169047869104298754146687)
    ·
      refine ⟨21253571803656448131220031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14169047869104298754146687 21253571803656448131220031)
      ·
        refine ⟨31880357705484672196830047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253571803656448131220031 31880357705484672196830047)
        ·
          refine ⟨47820536558227008295245071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31880357705484672196830047 47820536558227008295245071)
          ·
            refine ⟨71730804837340512442867607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47820536558227008295245071 71730804837340512442867607)
            ·
              refine ⟨107596207256010768664301411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71730804837340512442867607 107596207256010768664301411)
              ·
                refine ⟨161394310884016152996452117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107596207256010768664301411 161394310884016152996452117)
                ·
                  refine ⟨7565358322688257171708693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161394310884016152996452117 7565358322688257171708693)
                  ·
                    refine ⟨354626171376012054923845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7565358322688257171708693 354626171376012054923845)
                    ·
                      rfl

theorem cell22_1035948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1035948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035948 prefixEnd_1035948 := by exact prefixLift 1035948
  have htrace : WordTrace (prefixWord ++ tailWord_1035948) baseStart_1035948 baseEnd_1035948 := by
    simpa [prefixWord, tailWord_1035948, baseEnd_1035948] using wordTrace_append hprefix tailTrace_1035948
  have hstable : (prefixWord ++ tailWord_1035948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035948).length < 2 ^ (prefixWord ++ tailWord_1035948).sum := by decide
  have hdescent : baseEnd_1035948 < baseStart_1035948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035958 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1035958 : Nat := 118140960795 + 1035958 * 2 ^ 59
def prefixEnd_1035958 : Nat := 4983230072969 + 3 ^ 40 * 1035958 * 2
def baseEnd_1035958 : Nat := 118209864860125120724605

theorem tailTrace_1035958 : CollatzResearch.WordTrace tailWord_1035958 prefixEnd_1035958 118209864860125120724605 := by
  unfold tailWord_1035958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361530773806785524099283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25189661587272378923725685 2361530773806785524099283)
  ·
    refine ⟨3542296160710178286148925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361530773806785524099283 3542296160710178286148925)
    ·
      refine ⟨1328361060266316857305847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3542296160710178286148925 1328361060266316857305847)
      ·
        refine ⟨1992541590399475285958771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328361060266316857305847 1992541590399475285958771)
        ·
          refine ⟨2988812385599212928938157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992541590399475285958771 2988812385599212928938157)
          ·
            refine ⟨1120804644599704848351809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2988812385599212928938157 1120804644599704848351809)
            ·
              refine ⟨840603483449778636263857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120804644599704848351809 840603483449778636263857)
              ·
                refine ⟨630452612587333977197893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840603483449778636263857 630452612587333977197893)
                ·
                  refine ⟨118209864860125120724605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630452612587333977197893 118209864860125120724605)
                  ·
                    rfl

theorem cell22_1035958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1035958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035958 prefixEnd_1035958 := by exact prefixLift 1035958
  have htrace : WordTrace (prefixWord ++ tailWord_1035958) baseStart_1035958 baseEnd_1035958 := by
    simpa [prefixWord, tailWord_1035958, baseEnd_1035958] using wordTrace_append hprefix tailTrace_1035958
  have hstable : (prefixWord ++ tailWord_1035958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035958).length < 2 ^ (prefixWord ++ tailWord_1035958).sum := by decide
  have hdescent : baseEnd_1035958 < baseStart_1035958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035963 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 7]
def baseStart_1035963 : Nat := 118140960795 + 1035963 * 2 ^ 59
def prefixEnd_1035963 : Nat := 4983230072969 + 3 ^ 40 * 1035963 * 2
def baseEnd_1035963 : Nat := 118210435394185671932933

theorem tailTrace_1035963 : CollatzResearch.WordTrace tailWord_1035963 prefixEnd_1035963 118210435394185671932933 := by
  unfold tailWord_1035963
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784674745890454239520543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25189783163926969493013695 37784674745890454239520543)
  ·
    refine ⟨56677012118835681359280815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37784674745890454239520543 56677012118835681359280815)
    ·
      refine ⟨85015518178253522038921223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56677012118835681359280815 85015518178253522038921223)
      ·
        refine ⟨127523277267380283058381835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85015518178253522038921223 127523277267380283058381835)
        ·
          refine ⟨191284915901070424587572753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127523277267380283058381835 191284915901070424587572753)
          ·
            refine ⟨143463686925802818440679565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191284915901070424587572753 143463686925802818440679565)
            ·
              refine ⟨53798882597176056915254837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143463686925802818440679565 53798882597176056915254837)
              ·
                refine ⟨5043645243485255335805141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53798882597176056915254837 5043645243485255335805141)
                ·
                  refine ⟨118210435394185671932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5043645243485255335805141 118210435394185671932933)
                  ·
                    rfl

theorem cell22_1035963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_1035963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1035963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1035963 prefixEnd_1035963 := by exact prefixLift 1035963
  have htrace : WordTrace (prefixWord ++ tailWord_1035963) baseStart_1035963 baseEnd_1035963 := by
    simpa [prefixWord, tailWord_1035963, baseEnd_1035963] using wordTrace_append hprefix tailTrace_1035963
  have hstable : (prefixWord ++ tailWord_1035963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035963).length < 2 ^ (prefixWord ++ tailWord_1035963).sum := by decide
  have hdescent : baseEnd_1035963 < baseStart_1035963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036001 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 1, 3]
def baseStart_1036001 : Nat := 118140960795 + 1036001 * 2 ^ 59
def prefixEnd_1036001 : Nat := 4983230072969 + 3 ^ 40 * 1036001 * 2
def baseEnd_1036001 : Nat := 354644314359137583348683

theorem tailTrace_1036001 : CollatzResearch.WordTrace tailWord_1036001 prefixEnd_1036001 354644314359137583348683 := by
  unfold tailWord_1036001
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786060719752786729403857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25190707146501857819602571 37786060719752786729403857)
  ·
    refine ⟨28339545539814590047052893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37786060719752786729403857 28339545539814590047052893)
    ·
      refine ⟨10627329577430471267644835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28339545539814590047052893 10627329577430471267644835)
      ·
        refine ⟨15940994366145706901467253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627329577430471267644835 15940994366145706901467253)
        ·
          refine ⟨1494468221826160022012555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15940994366145706901467253 1494468221826160022012555)
          ·
            refine ⟨2241702332739240033018833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494468221826160022012555 2241702332739240033018833)
            ·
              refine ⟨1681276749554430024764125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241702332739240033018833 1681276749554430024764125)
              ·
                refine ⟨630478781082911259286547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681276749554430024764125 630478781082911259286547)
                ·
                  refine ⟨945718171624366888929821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630478781082911259286547 945718171624366888929821)
                  ·
                    refine ⟨354644314359137583348683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945718171624366888929821 354644314359137583348683)
                    ·
                      rfl

theorem cell22_1036001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_1036001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036001 prefixEnd_1036001 := by exact prefixLift 1036001
  have htrace : WordTrace (prefixWord ++ tailWord_1036001) baseStart_1036001 baseEnd_1036001 := by
    simpa [prefixWord, tailWord_1036001, baseEnd_1036001] using wordTrace_append hprefix tailTrace_1036001
  have hstable : (prefixWord ++ tailWord_1036001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036001).length < 2 ^ (prefixWord ++ tailWord_1036001).sum := by decide
  have hdescent : baseEnd_1036001 < baseStart_1036001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036052 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1036052 : Nat := 118140960795 + 1036052 * 2 ^ 59
def prefixEnd_1036052 : Nat := 4983230072969 + 3 ^ 40 * 1036052 * 2
def baseEnd_1036052 : Nat := 354661772701390450323527

theorem tailTrace_1036052 : CollatzResearch.WordTrace tailWord_1036052 prefixEnd_1036052 354661772701390450323527 := by
  unfold tailWord_1036052
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893960421284011219755205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25191947228378681626340273 18893960421284011219755205)
  ·
    refine ⟨3542617578990752103704101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18893960421284011219755205 3542617578990752103704101)
    ·
      refine ⟨664240796060766019444519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3542617578990752103704101 664240796060766019444519)
      ·
        refine ⟨996361194091149029166779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664240796060766019444519 996361194091149029166779)
        ·
          refine ⟨1494541791136723543750169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996361194091149029166779 1494541791136723543750169)
          ·
            refine ⟨1120906343352542657812627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494541791136723543750169 1120906343352542657812627)
            ·
              refine ⟨1681359515028813986718941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120906343352542657812627 1681359515028813986718941)
              ·
                refine ⟨630509818135805245019603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681359515028813986718941 630509818135805245019603)
                ·
                  refine ⟨945764727203707867529405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630509818135805245019603 945764727203707867529405)
                  ·
                    refine ⟨354661772701390450323527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945764727203707867529405 354661772701390450323527)
                    ·
                      rfl

theorem cell22_1036052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1036052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036052 prefixEnd_1036052 := by exact prefixLift 1036052
  have htrace : WordTrace (prefixWord ++ tailWord_1036052) baseStart_1036052 baseEnd_1036052 := by
    simpa [prefixWord, tailWord_1036052, baseEnd_1036052] using wordTrace_append hprefix tailTrace_1036052
  have hstable : (prefixWord ++ tailWord_1036052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036052).length < 2 ^ (prefixWord ++ tailWord_1036052).sum := by decide
  have hdescent : baseEnd_1036052 < baseStart_1036052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036072 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1036072 : Nat := 118140960795 + 1036072 * 2 ^ 59
def prefixEnd_1036072 : Nat := 4983230072969 + 3 ^ 40 * 1036072 * 2
def baseEnd_1036072 : Nat := 354668619110117064823465

theorem tailTrace_1036072 : CollatzResearch.WordTrace tailWord_1036072 prefixEnd_1036072 354668619110117064823465 := by
  unfold tailWord_1036072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894325151247782927619235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25192433534997043903492313 18894325151247782927619235)
  ·
    refine ⟨28341487726871674391428853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18894325151247782927619235 28341487726871674391428853)
    ·
      refine ⟨2657014474394219474196455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28341487726871674391428853 2657014474394219474196455)
      ·
        refine ⟨3985521711591329211294683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657014474394219474196455 3985521711591329211294683)
        ·
          refine ⟨5978282567386993816942025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985521711591329211294683 5978282567386993816942025)
          ·
            refine ⟨4483711925540245362706519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978282567386993816942025 4483711925540245362706519)
            ·
              refine ⟨6725567888310368044059779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483711925540245362706519 6725567888310368044059779)
              ·
                refine ⟨10088351832465552066089669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725567888310368044059779 10088351832465552066089669)
                ·
                  refine ⟨1891565968587291012391813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10088351832465552066089669 1891565968587291012391813)
                  ·
                    refine ⟨354668619110117064823465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891565968587291012391813 354668619110117064823465)
                    ·
                      rfl

theorem cell22_1036072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1036072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036072 prefixEnd_1036072 := by exact prefixLift 1036072
  have htrace : WordTrace (prefixWord ++ tailWord_1036072) baseStart_1036072 baseEnd_1036072 := by
    simpa [prefixWord, tailWord_1036072, baseEnd_1036072] using wordTrace_append hprefix tailTrace_1036072
  have hstable : (prefixWord ++ tailWord_1036072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036072).length < 2 ^ (prefixWord ++ tailWord_1036072).sum := by decide
  have hdescent : baseEnd_1036072 < baseStart_1036072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036136 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1036136 : Nat := 118140960795 + 1036136 * 2 ^ 59
def prefixEnd_1036136 : Nat := 4983230072969 + 3 ^ 40 * 1036136 * 2
def baseEnd_1036136 : Nat := 354690527618042231223269

theorem tailTrace_1036136 : CollatzResearch.WordTrace tailWord_1036136 prefixEnd_1036136 354690527618042231223269 := by
  unfold tailWord_1036136
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895492287131852392784131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25193989716175803190378841 18895492287131852392784131)
  ·
    refine ⟨28343238430697778589176197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18895492287131852392784131 28343238430697778589176197)
    ·
      refine ⟨5314357205755833485470537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28343238430697778589176197 5314357205755833485470537)
      ·
        refine ⟨3985767904316875114102903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5314357205755833485470537 3985767904316875114102903)
        ·
          refine ⟨5978651856475312671154355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985767904316875114102903 5978651856475312671154355)
          ·
            refine ⟨8967977784712969006731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978651856475312671154355 8967977784712969006731533)
            ·
              refine ⟨3362991669267363377524325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8967977784712969006731533 3362991669267363377524325)
              ·
                refine ⟨630560937987630633285811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3362991669267363377524325 630560937987630633285811)
                ·
                  refine ⟨945841406981445949928717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630560937987630633285811 945841406981445949928717)
                  ·
                    refine ⟨354690527618042231223269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945841406981445949928717 354690527618042231223269)
                    ·
                      rfl

theorem cell22_1036136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1036136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036136 prefixEnd_1036136 := by exact prefixLift 1036136
  have htrace : WordTrace (prefixWord ++ tailWord_1036136) baseStart_1036136 baseEnd_1036136 := by
    simpa [prefixWord, tailWord_1036136, baseEnd_1036136] using wordTrace_append hprefix tailTrace_1036136
  have hstable : (prefixWord ++ tailWord_1036136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036136).length < 2 ^ (prefixWord ++ tailWord_1036136).sum := by decide
  have hdescent : baseEnd_1036136 < baseStart_1036136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036175 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1036175 : Nat := 118140960795 + 1036175 * 2 ^ 59
def prefixEnd_1036175 : Nat := 4983230072969 + 3 ^ 40 * 1036175 * 2
def baseEnd_1036175 : Nat := 354703878115059129498149

theorem tailTrace_1036175 : CollatzResearch.WordTrace tailWord_1036175 prefixEnd_1036175 354703878115059129498149 := by
  unfold tailWord_1036175
  simp only [CollatzResearch.WordTrace]
  refine ⟨37792407021122414446237979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25194938014081609630825319 37792407021122414446237979)
  ·
    refine ⟨56688610531683621669356969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37792407021122414446237979 56688610531683621669356969)
    ·
      refine ⟨42516457898762716252017727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56688610531683621669356969 42516457898762716252017727)
      ·
        refine ⟨63774686848144074378026591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42516457898762716252017727 63774686848144074378026591)
        ·
          refine ⟨95662030272216111567039887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63774686848144074378026591 95662030272216111567039887)
          ·
            refine ⟨143493045408324167350559831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95662030272216111567039887 143493045408324167350559831)
            ·
              refine ⟨215239568112486251025839747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143493045408324167350559831 215239568112486251025839747)
              ·
                refine ⟨322859352168729376538759621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215239568112486251025839747 322859352168729376538759621)
                ·
                  refine ⟨60536128531636758101017429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322859352168729376538759621 60536128531636758101017429)
                  ·
                    refine ⟨354703878115059129498149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60536128531636758101017429 354703878115059129498149)
                    ·
                      rfl

theorem cell22_1036175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1036175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036175 prefixEnd_1036175 := by exact prefixLift 1036175
  have htrace : WordTrace (prefixWord ++ tailWord_1036175) baseStart_1036175 baseEnd_1036175 := by
    simpa [prefixWord, tailWord_1036175, baseEnd_1036175] using wordTrace_append hprefix tailTrace_1036175
  have hstable : (prefixWord ++ tailWord_1036175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036175).length < 2 ^ (prefixWord ++ tailWord_1036175).sum := by decide
  have hdescent : baseEnd_1036175 < baseStart_1036175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036209 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1036209 : Nat := 118140960795 + 1036209 * 2 ^ 59
def prefixEnd_1036209 : Nat := 4983230072969 + 3 ^ 40 * 1036209 * 2
def baseEnd_1036209 : Nat := 354715517009894374148045

theorem tailTrace_1036209 : CollatzResearch.WordTrace tailWord_1036209 prefixEnd_1036209 354715517009894374148045 := by
  unfold tailWord_1036209
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793647102999238252975681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25195764735332825501983787 37793647102999238252975681)
  ·
    refine ⟨28345235327249428689731761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37793647102999238252975681 28345235327249428689731761)
    ·
      refine ⟨21258926495437071517298821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28345235327249428689731761 21258926495437071517298821)
      ·
        refine ⟨3986048717894450909493529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21258926495437071517298821 3986048717894450909493529)
        ·
          refine ⟨2989536538420838182120147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986048717894450909493529 2989536538420838182120147)
          ·
            refine ⟨4484304807631257273180221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989536538420838182120147 4484304807631257273180221)
            ·
              refine ⟨1681614302861721477442583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4484304807631257273180221 1681614302861721477442583)
              ·
                refine ⟨2522421454292582216163875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681614302861721477442583 2522421454292582216163875)
                ·
                  refine ⟨3783632181438873324245813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522421454292582216163875 3783632181438873324245813)
                  ·
                    refine ⟨354715517009894374148045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3783632181438873324245813 354715517009894374148045)
                    ·
                      rfl

theorem cell22_1036209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1036209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036209 prefixEnd_1036209 := by exact prefixLift 1036209
  have htrace : WordTrace (prefixWord ++ tailWord_1036209) baseStart_1036209 baseEnd_1036209 := by
    simpa [prefixWord, tailWord_1036209, baseEnd_1036209] using wordTrace_append hprefix tailTrace_1036209
  have hstable : (prefixWord ++ tailWord_1036209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036209).length < 2 ^ (prefixWord ++ tailWord_1036209).sum := by decide
  have hdescent : baseEnd_1036209 < baseStart_1036209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036282 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1036282 : Nat := 118140960795 + 1036282 * 2 ^ 59
def prefixEnd_1036282 : Nat := 4983230072969 + 3 ^ 40 * 1036282 * 2
def baseEnd_1036282 : Nat := 354740506401746517072821

theorem tailTrace_1036282 : CollatzResearch.WordTrace tailWord_1036282 prefixEnd_1036282 354740506401746517072821 := by
  unfold tailWord_1036282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449077407933692930095775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25197539754489847813588733 9449077407933692930095775)
  ·
    refine ⟨14173616111900539395143663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9449077407933692930095775 14173616111900539395143663)
    ·
      refine ⟨21260424167850809092715495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14173616111900539395143663 21260424167850809092715495)
      ·
        refine ⟨31890636251776213639073243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21260424167850809092715495 31890636251776213639073243)
        ·
          refine ⟨47835954377664320458609865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31890636251776213639073243 47835954377664320458609865)
          ·
            refine ⟨35876965783248240343957399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47835954377664320458609865 35876965783248240343957399)
            ·
              refine ⟨53815448674872360515936099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35876965783248240343957399 53815448674872360515936099)
              ·
                refine ⟨80723173012308540773904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53815448674872360515936099 80723173012308540773904149)
                ·
                  refine ⟨3783898734951962848776757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80723173012308540773904149 3783898734951962848776757)
                  ·
                    refine ⟨354740506401746517072821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3783898734951962848776757 354740506401746517072821)
                    ·
                      rfl

theorem cell22_1036282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1036282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036282 prefixEnd_1036282 := by exact prefixLift 1036282
  have htrace : WordTrace (prefixWord ++ tailWord_1036282) baseStart_1036282 baseEnd_1036282 := by
    simpa [prefixWord, tailWord_1036282, baseEnd_1036282] using wordTrace_append hprefix tailTrace_1036282
  have hstable : (prefixWord ++ tailWord_1036282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036282).length < 2 ^ (prefixWord ++ tailWord_1036282).sum := by decide
  have hdescent : baseEnd_1036282 < baseStart_1036282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036294 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1036294 : Nat := 118140960795 + 1036294 * 2 ^ 59
def prefixEnd_1036294 : Nat := 4983230072969 + 3 ^ 40 * 1036294 * 2
def baseEnd_1036294 : Nat := 354744614246982485772785

theorem tailTrace_1036294 : CollatzResearch.WordTrace tailWord_1036294 prefixEnd_1036294 354744614246982485772785 := by
  unfold tailWord_1036294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181148353365353055306873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25197831538460865179879957 1181148353365353055306873)
  ·
    refine ⟨885861265024014791480155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1181148353365353055306873 885861265024014791480155)
    ·
      refine ⟨1328791897536022187220233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885861265024014791480155 1328791897536022187220233)
      ·
        refine ⟨996593923152016640415175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1328791897536022187220233 996593923152016640415175)
        ·
          refine ⟨1494890884728024960622763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996593923152016640415175 1494890884728024960622763)
          ·
            refine ⟨2242336327092037440934145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494890884728024960622763 2242336327092037440934145)
            ·
              refine ⟨1681752245319028080700609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242336327092037440934145 1681752245319028080700609)
              ·
                refine ⟨1261314183989271060525457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681752245319028080700609 1261314183989271060525457)
                ·
                  refine ⟨945985637991953295394093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261314183989271060525457 945985637991953295394093)
                  ·
                    refine ⟨354744614246982485772785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 945985637991953295394093 354744614246982485772785)
                    ·
                      rfl

theorem cell22_1036294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1036294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036294 prefixEnd_1036294 := by exact prefixLift 1036294
  have htrace : WordTrace (prefixWord ++ tailWord_1036294) baseStart_1036294 baseEnd_1036294 := by
    simpa [prefixWord, tailWord_1036294, baseEnd_1036294] using wordTrace_append hprefix tailTrace_1036294
  have hstable : (prefixWord ++ tailWord_1036294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036294).length < 2 ^ (prefixWord ++ tailWord_1036294).sum := by decide
  have hdescent : baseEnd_1036294 < baseStart_1036294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036314 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1036314 : Nat := 118140960795 + 1036314 * 2 ^ 59
def prefixEnd_1036314 : Nat := 4983230072969 + 3 ^ 40 * 1036314 * 2
def baseEnd_1036314 : Nat := 354751460655709100272723

theorem tailTrace_1036314 : CollatzResearch.WordTrace tailWord_1036314 prefixEnd_1036314 354751460655709100272723 := by
  unfold tailWord_1036314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449369191904710296386999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25198317845079227457031997 9449369191904710296386999)
  ·
    refine ⟨14174053787857065444580499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9449369191904710296386999 14174053787857065444580499)
    ·
      refine ⟨21261080681785598166870749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14174053787857065444580499 21261080681785598166870749)
      ·
        refine ⟨7972905255669599312576531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21261080681785598166870749 7972905255669599312576531)
        ·
          refine ⟨11959357883504398968864797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972905255669599312576531 11959357883504398968864797)
          ·
            refine ⟨4484759206314149613324299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11959357883504398968864797 4484759206314149613324299)
            ·
              refine ⟨6727138809471224419986449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484759206314149613324299 6727138809471224419986449)
              ·
                refine ⟨5045354107103418314989837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727138809471224419986449 5045354107103418314989837)
                ·
                  refine ⟨1892007790163781868121189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5045354107103418314989837 1892007790163781868121189)
                  ·
                    refine ⟨354751460655709100272723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1892007790163781868121189 354751460655709100272723)
                    ·
                      rfl

theorem cell22_1036314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1036314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036314 prefixEnd_1036314 := by exact prefixLift 1036314
  have htrace : WordTrace (prefixWord ++ tailWord_1036314) baseStart_1036314 baseEnd_1036314 := by
    simpa [prefixWord, tailWord_1036314, baseEnd_1036314] using wordTrace_append hprefix tailTrace_1036314
  have hstable : (prefixWord ++ tailWord_1036314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036314).length < 2 ^ (prefixWord ++ tailWord_1036314).sum := by decide
  have hdescent : baseEnd_1036314 < baseStart_1036314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036359 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1036359 : Nat := 118140960795 + 1036359 * 2 ^ 59
def prefixEnd_1036359 : Nat := 4983230072969 + 3 ^ 40 * 1036359 * 2
def baseEnd_1036359 : Nat := 354766865075343982897585

theorem tailTrace_1036359 : CollatzResearch.WordTrace tailWord_1036359 prefixEnd_1036359 354766865075343982897585 := by
  unfold tailWord_1036359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37799118052455813870936131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25199412034970542580624087 37799118052455813870936131)
  ·
    refine ⟨56698677078683720806404197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37799118052455813870936131 56698677078683720806404197)
    ·
      refine ⟨10631001952253197651200787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56698677078683720806404197 10631001952253197651200787)
      ·
        refine ⟨15946502928379796476801181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631001952253197651200787 15946502928379796476801181)
        ·
          refine ⟨5979938598142423678800443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15946502928379796476801181 5979938598142423678800443)
          ·
            refine ⟨8969907897213635518200665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979938598142423678800443 8969907897213635518200665)
            ·
              refine ⟨6727430922910226638650499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969907897213635518200665 6727430922910226638650499)
              ·
                refine ⟨10091146384365339957975749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727430922910226638650499 10091146384365339957975749)
                ·
                  refine ⟨1892089947068501242120453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10091146384365339957975749 1892089947068501242120453)
                  ·
                    refine ⟨354766865075343982897585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1892089947068501242120453 354766865075343982897585)
                    ·
                      rfl

theorem cell22_1036359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1036359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036359 prefixEnd_1036359 := by exact prefixLift 1036359
  have htrace : WordTrace (prefixWord ++ tailWord_1036359) baseStart_1036359 baseEnd_1036359 := by
    simpa [prefixWord, tailWord_1036359, baseEnd_1036359] using wordTrace_append hprefix tailTrace_1036359
  have hstable : (prefixWord ++ tailWord_1036359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036359).length < 2 ^ (prefixWord ++ tailWord_1036359).sum := by decide
  have hdescent : baseEnd_1036359 < baseStart_1036359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036378 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_1036378 : Nat := 118140960795 + 1036378 * 2 ^ 59
def prefixEnd_1036378 : Nat := 4983230072969 + 3 ^ 40 * 1036378 * 2
def baseEnd_1036378 : Nat := 354773369163634266672527

theorem tailTrace_1036378 : CollatzResearch.WordTrace tailWord_1036378 prefixEnd_1036378 354773369163634266672527 := by
  unfold tailWord_1036378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449952759846745028969447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25199874026257986743918525 9449952759846745028969447)
  ·
    refine ⟨14174929139770117543454171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9449952759846745028969447 14174929139770117543454171)
    ·
      refine ⟨21262393709655176315181257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14174929139770117543454171 21262393709655176315181257)
      ·
        refine ⟨15946795282241382236385943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21262393709655176315181257 15946795282241382236385943)
        ·
          refine ⟨23920192923362073354578915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15946795282241382236385943 23920192923362073354578915)
          ·
            refine ⟨35880289385043110031868373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23920192923362073354578915 35880289385043110031868373)
            ·
              refine ⟨840944282461947891371915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35880289385043110031868373 840944282461947891371915)
              ·
                refine ⟨1261416423692921837057873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840944282461947891371915 1261416423692921837057873)
                ·
                  refine ⟨946062317769691377793405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261416423692921837057873 946062317769691377793405)
                  ·
                    refine ⟨354773369163634266672527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946062317769691377793405 354773369163634266672527)
                    ·
                      rfl

theorem cell22_1036378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_1036378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036378 prefixEnd_1036378 := by exact prefixLift 1036378
  have htrace : WordTrace (prefixWord ++ tailWord_1036378) baseStart_1036378 baseEnd_1036378 := by
    simpa [prefixWord, tailWord_1036378, baseEnd_1036378] using wordTrace_append hprefix tailTrace_1036378
  have hstable : (prefixWord ++ tailWord_1036378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036378).length < 2 ^ (prefixWord ++ tailWord_1036378).sum := by decide
  have hdescent : baseEnd_1036378 < baseStart_1036378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036382 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1036382 : Nat := 118140960795 + 1036382 * 2 ^ 59
def prefixEnd_1036382 : Nat := 4983230072969 + 3 ^ 40 * 1036382 * 2
def baseEnd_1036382 : Nat := 354774738445379589572515

theorem tailTrace_1036382 : CollatzResearch.WordTrace tailWord_1036382 prefixEnd_1036382 354774738445379589572515 := by
  unfold tailWord_1036382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724994616421561099877925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25199971287581659199348933 4724994616421561099877925)
  ·
    refine ⟨885936490579042706227111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4724994616421561099877925 885936490579042706227111)
    ·
      refine ⟨1328904735868564059340667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885936490579042706227111 1328904735868564059340667)
      ·
        refine ⟨1993357103802846089011001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328904735868564059340667 1993357103802846089011001)
        ·
          refine ⟨1495017827852134566758251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1993357103802846089011001 1495017827852134566758251)
          ·
            refine ⟨2242526741778201850137377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495017827852134566758251 2242526741778201850137377)
            ·
              refine ⟨1681895056333651387603033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242526741778201850137377 1681895056333651387603033)
              ·
                refine ⟨1261421292250238540702275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681895056333651387603033 1261421292250238540702275)
                ·
                  refine ⟨1892131938375357811053413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261421292250238540702275 1892131938375357811053413)
                  ·
                    refine ⟨354774738445379589572515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1892131938375357811053413 354774738445379589572515)
                    ·
                      rfl

theorem cell22_1036382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1036382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036382 prefixEnd_1036382 := by exact prefixLift 1036382
  have htrace : WordTrace (prefixWord ++ tailWord_1036382) baseStart_1036382 baseEnd_1036382 := by
    simpa [prefixWord, tailWord_1036382, baseEnd_1036382] using wordTrace_append hprefix tailTrace_1036382
  have hstable : (prefixWord ++ tailWord_1036382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036382).length < 2 ^ (prefixWord ++ tailWord_1036382).sum := by decide
  have hdescent : baseEnd_1036382 < baseStart_1036382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036419 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 7]
def baseStart_1036419 : Nat := 118140960795 + 1036419 * 2 ^ 59
def prefixEnd_1036419 : Nat := 4983230072969 + 3 ^ 40 * 1036419 * 2
def baseEnd_1036419 : Nat := 118262468100507942132467

theorem tailTrace_1036419 : CollatzResearch.WordTrace tailWord_1036419 prefixEnd_1036419 118262468100507942132467 := by
  unfold tailWord_1036419
  simp only [CollatzResearch.WordTrace]
  refine ⟨37801306432238444118120311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25200870954825629412080207 37801306432238444118120311)
  ·
    refine ⟨56701959648357666177180467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37801306432238444118120311 56701959648357666177180467)
    ·
      refine ⟨85052939472536499265770701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56701959648357666177180467 85052939472536499265770701)
      ·
        refine ⟨31894852302201187224664013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85052939472536499265770701 31894852302201187224664013)
        ·
          refine ⟨11960569613325445209249005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31894852302201187224664013 11960569613325445209249005)
          ·
            refine ⟨4485213604997041953468377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11960569613325445209249005 4485213604997041953468377)
            ·
              refine ⟨3363910203747781465101283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485213604997041953468377 3363910203747781465101283)
              ·
                refine ⟨5045865305621672197651925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363910203747781465101283 5045865305621672197651925)
                ·
                  refine ⟨118262468100507942132467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5045865305621672197651925 118262468100507942132467)
                  ·
                    rfl

theorem cell22_1036419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_1036419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036419 prefixEnd_1036419 := by exact prefixLift 1036419
  have htrace : WordTrace (prefixWord ++ tailWord_1036419) baseStart_1036419 baseEnd_1036419 := by
    simpa [prefixWord, tailWord_1036419, baseEnd_1036419] using wordTrace_append hprefix tailTrace_1036419
  have hstable : (prefixWord ++ tailWord_1036419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036419).length < 2 ^ (prefixWord ++ tailWord_1036419).sum := by decide
  have hdescent : baseEnd_1036419 < baseStart_1036419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036423 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1036423 : Nat := 118140960795 + 1036423 * 2 ^ 59
def prefixEnd_1036423 : Nat := 4983230072969 + 3 ^ 40 * 1036423 * 2
def baseEnd_1036423 : Nat := 354788773583269149297389

theorem tailTrace_1036423 : CollatzResearch.WordTrace tailWord_1036423 prefixEnd_1036423 354788773583269149297389 := by
  unfold tailWord_1036423
  simp only [CollatzResearch.WordTrace]
  refine ⟨37801452324223952801265923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25200968216149301867510615 37801452324223952801265923)
  ·
    refine ⟨56702178486335929201898885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37801452324223952801265923 56702178486335929201898885)
    ·
      refine ⟨10631658466187986725356041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56702178486335929201898885 10631658466187986725356041)
      ·
        refine ⟨7973743849640990044017031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10631658466187986725356041 7973743849640990044017031)
        ·
          refine ⟨11960615774461485066025547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973743849640990044017031 11960615774461485066025547)
          ·
            refine ⟨17940923661692227599038321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11960615774461485066025547 17940923661692227599038321)
            ·
              refine ⟨13455692746269170699278741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17940923661692227599038321 13455692746269170699278741)
              ·
                refine ⟨630735597481367376528691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13455692746269170699278741 630735597481367376528691)
                ·
                  refine ⟨946103396222051064793037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630735597481367376528691 946103396222051064793037)
                  ·
                    refine ⟨354788773583269149297389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946103396222051064793037 354788773583269149297389)
                    ·
                      rfl

theorem cell22_1036423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1036423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036423 prefixEnd_1036423 := by exact prefixLift 1036423
  have htrace : WordTrace (prefixWord ++ tailWord_1036423) baseStart_1036423 baseEnd_1036423 := by
    simpa [prefixWord, tailWord_1036423, baseEnd_1036423] using wordTrace_append hprefix tailTrace_1036423
  have hstable : (prefixWord ++ tailWord_1036423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036423).length < 2 ^ (prefixWord ++ tailWord_1036423).sum := by decide
  have hdescent : baseEnd_1036423 < baseStart_1036423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036479 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_1036479 : Nat := 118140960795 + 1036479 * 2 ^ 59
def prefixEnd_1036479 : Nat := 4983230072969 + 3 ^ 40 * 1036479 * 2
def baseEnd_1036479 : Nat := 354807943527703669897217

theorem tailTrace_1036479 : CollatzResearch.WordTrace tailWord_1036479 prefixEnd_1036479 354807943527703669897217 := by
  unfold tailWord_1036479
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803494812021074365304491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25202329874680716243536327 37803494812021074365304491)
  ·
    refine ⟨56705242218031611547956737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37803494812021074365304491 56705242218031611547956737)
    ·
      refine ⟨42528931663523708660967553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56705242218031611547956737 42528931663523708660967553)
      ·
        refine ⟨31896698747642781495725665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42528931663523708660967553 31896698747642781495725665)
        ·
          refine ⟨23922524060732086121794249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31896698747642781495725665 23922524060732086121794249)
          ·
            refine ⟨17941893045549064591345687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23922524060732086121794249 17941893045549064591345687)
            ·
              refine ⟨26912839568323596887018531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17941893045549064591345687 26912839568323596887018531)
              ·
                refine ⟨40369259352485395330527797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26912839568323596887018531 40369259352485395330527797)
                ·
                  refine ⟨3784618064295505812236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40369259352485395330527797 3784618064295505812236981)
                  ·
                    refine ⟨354807943527703669897217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3784618064295505812236981 354807943527703669897217)
                    ·
                      rfl

theorem cell22_1036479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_1036479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036479 prefixEnd_1036479 := by exact prefixLift 1036479
  have htrace : WordTrace (prefixWord ++ tailWord_1036479) baseStart_1036479 baseEnd_1036479 := by
    simpa [prefixWord, tailWord_1036479, baseEnd_1036479] using wordTrace_append hprefix tailTrace_1036479
  have hstable : (prefixWord ++ tailWord_1036479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036479).length < 2 ^ (prefixWord ++ tailWord_1036479).sum := by decide
  have hdescent : baseEnd_1036479 < baseStart_1036479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036530 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1036530 : Nat := 118140960795 + 1036530 * 2 ^ 59
def prefixEnd_1036530 : Nat := 4983230072969 + 3 ^ 40 * 1036530 * 2
def baseEnd_1036530 : Nat := 354825401869956536872061

theorem tailTrace_1036530 : CollatzResearch.WordTrace tailWord_1036530 prefixEnd_1036530 354825401869956536872061 := by
  unfold tailWord_1036530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451338733709077518852761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25203569956557540050274029 9451338733709077518852761)
  ·
    refine ⟨7088504050281808139139571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9451338733709077518852761 7088504050281808139139571)
    ·
      refine ⟨10632756075422712208709357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088504050281808139139571 10632756075422712208709357)
      ·
        refine ⟨3987283528283517078266009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10632756075422712208709357 3987283528283517078266009)
        ·
          refine ⟨2990462646212637808699507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3987283528283517078266009 2990462646212637808699507)
          ·
            refine ⟨4485693969318956713049261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990462646212637808699507 4485693969318956713049261)
            ·
              refine ⟨1682135238494608767393473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4485693969318956713049261 1682135238494608767393473)
              ·
                refine ⟨1261601428870956575545105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682135238494608767393473 1261601428870956575545105)
                ·
                  refine ⟨946201071653217431658829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1261601428870956575545105 946201071653217431658829)
                  ·
                    refine ⟨354825401869956536872061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946201071653217431658829 354825401869956536872061)
                    ·
                      rfl

theorem cell22_1036530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1036530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036530 prefixEnd_1036530 := by exact prefixLift 1036530
  have htrace : WordTrace (prefixWord ++ tailWord_1036530) baseStart_1036530 baseEnd_1036530 := by
    simpa [prefixWord, tailWord_1036530, baseEnd_1036530] using wordTrace_append hprefix tailTrace_1036530
  have hstable : (prefixWord ++ tailWord_1036530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036530).length < 2 ^ (prefixWord ++ tailWord_1036530).sum := by decide
  have hdescent : baseEnd_1036530 < baseStart_1036530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036558 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1036558 : Nat := 118140960795 + 1036558 * 2 ^ 59
def prefixEnd_1036558 : Nat := 4983230072969 + 3 ^ 40 * 1036558 * 2
def baseEnd_1036558 : Nat := 354834986842173797171975

theorem tailTrace_1036558 : CollatzResearch.WordTrace tailWord_1036558 prefixEnd_1036558 354834986842173797171975 := by
  unfold tailWord_1036558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725797022341858857178791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25204250785823247238286885 4725797022341858857178791)
  ·
    refine ⟨7088695533512788285768187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725797022341858857178791 7088695533512788285768187)
    ·
      refine ⟨10633043300269182428652281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088695533512788285768187 10633043300269182428652281)
      ·
        refine ⟨7974782475201886821489211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10633043300269182428652281 7974782475201886821489211)
        ·
          refine ⟨11962173712802830232233817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974782475201886821489211 11962173712802830232233817)
          ·
            refine ⟨8971630284602122674175363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11962173712802830232233817 8971630284602122674175363)
            ·
              refine ⟨13457445426903184011263045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971630284602122674175363 13457445426903184011263045)
              ·
                refine ⟨2523271017544347002111821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13457445426903184011263045 2523271017544347002111821)
                ·
                  refine ⟨946226631579130125791933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2523271017544347002111821 946226631579130125791933)
                  ·
                    refine ⟨354834986842173797171975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946226631579130125791933 354834986842173797171975)
                    ·
                      rfl

theorem cell22_1036558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1036558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036558 prefixEnd_1036558 := by exact prefixLift 1036558
  have htrace : WordTrace (prefixWord ++ tailWord_1036558) baseStart_1036558 baseEnd_1036558 := by
    simpa [prefixWord, tailWord_1036558, baseEnd_1036558] using wordTrace_append hprefix tailTrace_1036558
  have hstable : (prefixWord ++ tailWord_1036558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036558).length < 2 ^ (prefixWord ++ tailWord_1036558).sum := by decide
  have hdescent : baseEnd_1036558 < baseStart_1036558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036616 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_1036616 : Nat := 118140960795 + 1036616 * 2 ^ 59
def prefixEnd_1036616 : Nat := 4983230072969 + 3 ^ 40 * 1036616 * 2
def baseEnd_1036616 : Nat := 118284947142493659740599

theorem tailTrace_1036616 : CollatzResearch.WordTrace tailWord_1036616 prefixEnd_1036616 118284947142493659740599 := by
  unfold tailWord_1036616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904245806262373381520851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25205661075016497842027801 18904245806262373381520851)
  ·
    refine ⟨28356368709393560072281277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904245806262373381520851 28356368709393560072281277)
    ·
      refine ⟨10633638266022585027105479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28356368709393560072281277 10633638266022585027105479)
      ·
        refine ⟨15950457399033877540658219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633638266022585027105479 15950457399033877540658219)
        ·
          refine ⟨23925686098550816310987329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15950457399033877540658219 23925686098550816310987329)
          ·
            refine ⟨17944264573913112233240497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23925686098550816310987329 17944264573913112233240497)
            ·
              refine ⟨13458198430434834174930373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17944264573913112233240497 13458198430434834174930373)
              ·
                refine ⟨2523412205706531407799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13458198430434834174930373 2523412205706531407799445)
                ·
                  refine ⟨118284947142493659740599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2523412205706531407799445 118284947142493659740599)
                  ·
                    rfl

theorem cell22_1036616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_1036616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036616 prefixEnd_1036616 := by exact prefixLift 1036616
  have htrace : WordTrace (prefixWord ++ tailWord_1036616) baseStart_1036616 baseEnd_1036616 := by
    simpa [prefixWord, tailWord_1036616, baseEnd_1036616] using wordTrace_append hprefix tailTrace_1036616
  have hstable : (prefixWord ++ tailWord_1036616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036616).length < 2 ^ (prefixWord ++ tailWord_1036616).sum := by decide
  have hdescent : baseEnd_1036616 < baseStart_1036616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036633 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 4]
def baseStart_1036633 : Nat := 118140960795 + 1036633 * 2 ^ 59
def prefixEnd_1036633 : Nat := 4983230072969 + 3 ^ 40 * 1036633 * 2
def baseEnd_1036633 : Nat := 118286886958299533848915

theorem tailTrace_1036633 : CollatzResearch.WordTrace tailWord_1036633 prefixEnd_1036633 118286886958299533848915 := by
  unfold tailWord_1036633
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809111653463158666410553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25206074435642105777607035 37809111653463158666410553)
  ·
    refine ⟨28356833740097368999807915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37809111653463158666410553 28356833740097368999807915)
    ·
      refine ⟨42535250610146053499711873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28356833740097368999807915 42535250610146053499711873)
      ·
        refine ⟨31901437957609540124783905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42535250610146053499711873 31901437957609540124783905)
        ·
          refine ⟨23926078468207155093587929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31901437957609540124783905 23926078468207155093587929)
          ·
            refine ⟨17944558851155366320190947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23926078468207155093587929 17944558851155366320190947)
            ·
              refine ⟨26916838276733049480286421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944558851155366320190947 26916838276733049480286421)
              ·
                refine ⟨630863397110930847194213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26916838276733049480286421 630863397110930847194213)
                ·
                  refine ⟨118286886958299533848915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 630863397110930847194213 118286886958299533848915)
                  ·
                    rfl

theorem cell22_1036633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_1036633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036633 prefixEnd_1036633 := by exact prefixLift 1036633
  have htrace : WordTrace (prefixWord ++ tailWord_1036633) baseStart_1036633 baseEnd_1036633 := by
    simpa [prefixWord, tailWord_1036633, baseEnd_1036633] using wordTrace_append hprefix tailTrace_1036633
  have hstable : (prefixWord ++ tailWord_1036633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036633).length < 2 ^ (prefixWord ++ tailWord_1036633).sum := by decide
  have hdescent : baseEnd_1036633 < baseStart_1036633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036693 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1036693 : Nat := 118140960795 + 1036693 * 2 ^ 59
def prefixEnd_1036693 : Nat := 4983230072969 + 3 ^ 40 * 1036693 * 2
def baseEnd_1036693 : Nat := 354881200101078445046561

theorem tailTrace_1036693 : CollatzResearch.WordTrace tailWord_1036693 prefixEnd_1036693 354881200101078445046561 := by
  unfold tailWord_1036693
  simp only [CollatzResearch.WordTrace]
  refine ⟨37811300033245788913594733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25207533355497192609063155 37811300033245788913594733)
  ·
    refine ⟨14179237512467170842598025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37811300033245788913594733 14179237512467170842598025)
    ·
      refine ⟨10634428134350378131948519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14179237512467170842598025 10634428134350378131948519)
      ·
        refine ⟨15951642201525567197922779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634428134350378131948519 15951642201525567197922779)
        ·
          refine ⟨23927463302288350796884169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15951642201525567197922779 23927463302288350796884169)
          ·
            refine ⟨17945597476716263097663127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23927463302288350796884169 17945597476716263097663127)
            ·
              refine ⟨26918396215074394646494691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17945597476716263097663127 26918396215074394646494691)
              ·
                refine ⟨40377594322611591969742037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26918396215074394646494691 40377594322611591969742037)
                ·
                  refine ⟨946349866936209186790829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40377594322611591969742037 946349866936209186790829)
                  ·
                    refine ⟨354881200101078445046561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946349866936209186790829 354881200101078445046561)
                    ·
                      rfl

theorem cell22_1036693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1036693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036693 prefixEnd_1036693 := by exact prefixLift 1036693
  have htrace : WordTrace (prefixWord ++ tailWord_1036693) baseStart_1036693 baseEnd_1036693 := by
    simpa [prefixWord, tailWord_1036693, baseEnd_1036693] using wordTrace_append hprefix tailTrace_1036693
  have hstable : (prefixWord ++ tailWord_1036693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036693).length < 2 ^ (prefixWord ++ tailWord_1036693).sum := by decide
  have hdescent : baseEnd_1036693 < baseStart_1036693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036744 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 1, 3]
def baseStart_1036744 : Nat := 118140960795 + 1036744 * 2 ^ 59
def prefixEnd_1036744 : Nat := 4983230072969 + 3 ^ 40 * 1036744 * 2
def baseEnd_1036744 : Nat := 354898658443331312021405

theorem tailTrace_1036744 : CollatzResearch.WordTrace tailWord_1036744 prefixEnd_1036744 354898658443331312021405 := by
  unfold tailWord_1036744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906580078030512311850643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25208773437374016415800857 18906580078030512311850643)
  ·
    refine ⟨28359870117045768467775965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18906580078030512311850643 28359870117045768467775965)
    ·
      refine ⟨10634951293892163175415987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28359870117045768467775965 10634951293892163175415987)
      ·
        refine ⟨15952426940838244763123981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634951293892163175415987 15952426940838244763123981)
        ·
          refine ⟨5982160102814341786171493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15952426940838244763123981 5982160102814341786171493)
          ·
            refine ⟨1121655019277689084907155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5982160102814341786171493 1121655019277689084907155)
            ·
              refine ⟨1682482528916533627360733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121655019277689084907155 1682482528916533627360733)
              ·
                refine ⟨630930948343700110260275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1682482528916533627360733 630930948343700110260275)
                ·
                  refine ⟨946396422515550165390413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630930948343700110260275 946396422515550165390413)
                  ·
                    refine ⟨354898658443331312021405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946396422515550165390413 354898658443331312021405)
                    ·
                      rfl

theorem cell22_1036744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_1036744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036744 prefixEnd_1036744 := by exact prefixLift 1036744
  have htrace : WordTrace (prefixWord ++ tailWord_1036744) baseStart_1036744 baseEnd_1036744 := by
    simpa [prefixWord, tailWord_1036744, baseEnd_1036744] using wordTrace_append hprefix tailTrace_1036744
  have hstable : (prefixWord ++ tailWord_1036744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036744).length < 2 ^ (prefixWord ++ tailWord_1036744).sum := by decide
  have hdescent : baseEnd_1036744 < baseStart_1036744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036783 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_1036783 : Nat := 118140960795 + 1036783 * 2 ^ 59
def prefixEnd_1036783 : Nat := 4983230072969 + 3 ^ 40 * 1036783 * 2
def baseEnd_1036783 : Nat := 354912008940348210296285

theorem tailTrace_1036783 : CollatzResearch.WordTrace tailWord_1036783 prefixEnd_1036783 354912008940348210296285 := by
  unfold tailWord_1036783
  simp only [CollatzResearch.WordTrace]
  refine ⟨37814582602919734284371003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25209721735279822856247335 37814582602919734284371003)
  ·
    refine ⟨56721873904379601426556505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37814582602919734284371003 56721873904379601426556505)
    ·
      refine ⟨42541405428284701069917379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56721873904379601426556505 42541405428284701069917379)
      ·
        refine ⟨63812108142427051604876069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42541405428284701069917379 63812108142427051604876069)
        ·
          refine ⟨11964770276705072175914263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63812108142427051604876069 11964770276705072175914263)
          ·
            refine ⟨17947155415057608263871395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964770276705072175914263 17947155415057608263871395)
            ·
              refine ⟨26920733122586412395807093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17947155415057608263871395 26920733122586412395807093)
              ·
                refine ⟨2523818730242476162106915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26920733122586412395807093 2523818730242476162106915)
                ·
                  refine ⟨3785728095363714243160373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523818730242476162106915 3785728095363714243160373)
                  ·
                    refine ⟨354912008940348210296285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3785728095363714243160373 354912008940348210296285)
                    ·
                      rfl

theorem cell22_1036783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_1036783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036783 prefixEnd_1036783 := by exact prefixLift 1036783
  have htrace : WordTrace (prefixWord ++ tailWord_1036783) baseStart_1036783 baseEnd_1036783 := by
    simpa [prefixWord, tailWord_1036783, baseEnd_1036783] using wordTrace_append hprefix tailTrace_1036783
  have hstable : (prefixWord ++ tailWord_1036783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036783).length < 2 ^ (prefixWord ++ tailWord_1036783).sum := by decide
  have hdescent : baseEnd_1036783 < baseStart_1036783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036804 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1036804 : Nat := 118140960795 + 1036804 * 2 ^ 59
def prefixEnd_1036804 : Nat := 4983230072969 + 3 ^ 40 * 1036804 * 2
def baseEnd_1036804 : Nat := 354919197669511155521221

theorem tailTrace_1036804 : CollatzResearch.WordTrace tailWord_1036804 prefixEnd_1036804 354919197669511155521221 := by
  unfold tailWord_1036804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907674267921827435442733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25210232357229103247256977 18907674267921827435442733)
  ·
    refine ⟨7090377850470685288291025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18907674267921827435442733 7090377850470685288291025)
    ·
      refine ⟨5317783387853013966218269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7090377850470685288291025 5317783387853013966218269)
      ·
        refine ⟨1994168770444880237331851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5317783387853013966218269 1994168770444880237331851)
        ·
          refine ⟨2991253155667320355997777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994168770444880237331851 2991253155667320355997777)
          ·
            refine ⟨2243439866750490266998333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991253155667320355997777 2243439866750490266998333)
            ·
              refine ⟨841289950031433850124375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2243439866750490266998333 841289950031433850124375)
              ·
                refine ⟨1261934925047150775186563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841289950031433850124375 1261934925047150775186563)
                ·
                  refine ⟨1892902387570726162779845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261934925047150775186563 1892902387570726162779845)
                  ·
                    refine ⟨354919197669511155521221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1892902387570726162779845 354919197669511155521221)
                    ·
                      rfl

theorem cell22_1036804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1036804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036804 prefixEnd_1036804 := by exact prefixLift 1036804
  have htrace : WordTrace (prefixWord ++ tailWord_1036804) baseStart_1036804 baseEnd_1036804 := by
    simpa [prefixWord, tailWord_1036804, baseEnd_1036804] using wordTrace_append hprefix tailTrace_1036804
  have hstable : (prefixWord ++ tailWord_1036804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036804).length < 2 ^ (prefixWord ++ tailWord_1036804).sum := by decide
  have hdescent : baseEnd_1036804 < baseStart_1036804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036875 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 5]
def baseStart_1036875 : Nat := 118140960795 + 1036875 * 2 ^ 59
def prefixEnd_1036875 : Nat := 4983230072969 + 3 ^ 40 * 1036875 * 2
def baseEnd_1036875 : Nat := 118314500806830212332001

theorem tailTrace_1036875 : CollatzResearch.WordTrace tailWord_1036875 prefixEnd_1036875 118314500806830212332001 := by
  unfold tailWord_1036875
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817938118586433996720079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25211958745724289331146719 37817938118586433996720079)
  ·
    refine ⟨56726907177879650995080119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37817938118586433996720079 56726907177879650995080119)
    ·
      refine ⟨85090360766819476492620179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56726907177879650995080119 85090360766819476492620179)
      ·
        refine ⟨127635541150229214738930269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85090360766819476492620179 127635541150229214738930269)
        ·
          refine ⟨47863327931335955527098851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127635541150229214738930269 47863327931335955527098851)
          ·
            refine ⟨71794991897003933290648277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47863327931335955527098851 71794991897003933290648277)
            ·
              refine ⟨1682695122586029686499569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71794991897003933290648277 1682695122586029686499569)
              ·
                refine ⟨1262021341939522264874677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682695122586029686499569 1262021341939522264874677)
                ·
                  refine ⟨118314500806830212332001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1262021341939522264874677 118314500806830212332001)
                  ·
                    rfl

theorem cell22_1036875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 5].length) (baseStart_1036875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036875 prefixEnd_1036875 := by exact prefixLift 1036875
  have htrace : WordTrace (prefixWord ++ tailWord_1036875) baseStart_1036875 baseEnd_1036875 := by
    simpa [prefixWord, tailWord_1036875, baseEnd_1036875] using wordTrace_append hprefix tailTrace_1036875
  have hstable : (prefixWord ++ tailWord_1036875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036875).length < 2 ^ (prefixWord ++ tailWord_1036875).sum := by decide
  have hdescent : baseEnd_1036875 < baseStart_1036875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036930 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1036930 : Nat := 118140960795 + 1036930 * 2 ^ 59
def prefixEnd_1036930 : Nat := 4983230072969 + 3 ^ 40 * 1036930 * 2
def baseEnd_1036930 : Nat := 354962330044488826870835

theorem tailTrace_1036930 : CollatzResearch.WordTrace tailWord_1036930 prefixEnd_1036930 354962330044488826870835 := by
  unfold tailWord_1036930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454986033346794597493061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25213296088924785593314829 9454986033346794597493061)
  ·
    refine ⟨1772809881252523987029949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9454986033346794597493061 1772809881252523987029949)
    ·
      refine ⟨664803705469696495136231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1772809881252523987029949 664803705469696495136231)
      ·
        refine ⟨997205558204544742704347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664803705469696495136231 997205558204544742704347)
        ·
          refine ⟨1495808337306817114056521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997205558204544742704347 1495808337306817114056521)
          ·
            refine ⟨1121856252980112835542391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495808337306817114056521 1121856252980112835542391)
            ·
              refine ⟨1682784379470169253313587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121856252980112835542391 1682784379470169253313587)
              ·
                refine ⟨2524176569205253879970381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682784379470169253313587 2524176569205253879970381)
                ·
                  refine ⟨946566213451970204988893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2524176569205253879970381 946566213451970204988893)
                  ·
                    refine ⟨354962330044488826870835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946566213451970204988893 354962330044488826870835)
                    ·
                      rfl

theorem cell22_1036930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1036930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036930 prefixEnd_1036930 := by exact prefixLift 1036930
  have htrace : WordTrace (prefixWord ++ tailWord_1036930) baseStart_1036930 baseEnd_1036930 := by
    simpa [prefixWord, tailWord_1036930, baseEnd_1036930] using wordTrace_append hprefix tailTrace_1036930
  have hstable : (prefixWord ++ tailWord_1036930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036930).length < 2 ^ (prefixWord ++ tailWord_1036930).sum := by decide
  have hdescent : baseEnd_1036930 < baseStart_1036930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036982 : List Nat := [5, 1, 3, 1, 12]
def baseStart_1036982 : Nat := 118140960795 + 1036982 * 2 ^ 59
def prefixEnd_1036982 : Nat := 4983230072969 + 3 ^ 40 * 1036982 * 2
def baseEnd_1036982 : Nat := 1460823583157111212225

theorem tailTrace_1036982 : CollatzResearch.WordTrace tailWord_1036982 prefixEnd_1036982 1460823583157111212225 := by
  unfold tailWord_1036982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363865045574924454429075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25214560486132527513910133 2363865045574924454429075)
  ·
    refine ⟨3545797568362386681643613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363865045574924454429075 3545797568362386681643613)
    ·
      refine ⟨1329674088135895005616355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3545797568362386681643613 1329674088135895005616355)
      ·
        refine ⟨1994511132203842508424533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329674088135895005616355 1994511132203842508424533)
        ·
          refine ⟨1460823583157111212225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1994511132203842508424533 1460823583157111212225)
          ·
            rfl

theorem cell22_1036982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 12].length) (baseStart_1036982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1036982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1036982 prefixEnd_1036982 := by exact prefixLift 1036982
  have htrace : WordTrace (prefixWord ++ tailWord_1036982) baseStart_1036982 baseEnd_1036982 := by
    simpa [prefixWord, tailWord_1036982, baseEnd_1036982] using wordTrace_append hprefix tailTrace_1036982
  have hstable : (prefixWord ++ tailWord_1036982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036982).length < 2 ^ (prefixWord ++ tailWord_1036982).sum := by decide
  have hdescent : baseEnd_1036982 < baseStart_1036982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037042 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1037042 : Nat := 118140960795 + 1037042 * 2 ^ 59
def prefixEnd_1037042 : Nat := 4983230072969 + 3 ^ 40 * 1037042 * 2
def baseEnd_1037042 : Nat := 355000669933357868070491

theorem tailTrace_1037042 : CollatzResearch.WordTrace tailWord_1037042 prefixEnd_1037042 355000669933357868070491 := by
  unfold tailWord_1037042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9456007277245355379512345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25216019405987614345366253 9456007277245355379512345)
  ·
    refine ⟨7092005457934016534634259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9456007277245355379512345 7092005457934016534634259)
    ·
      refine ⟨10638008186901024801951389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7092005457934016534634259 10638008186901024801951389)
      ·
        refine ⟨3989253070087884300731771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10638008186901024801951389 3989253070087884300731771)
        ·
          refine ⟨5983879605131826451097657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989253070087884300731771 5983879605131826451097657)
          ·
            refine ⟨4487909703848869838323243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5983879605131826451097657 4487909703848869838323243)
            ·
              refine ⟨6731864555773304757484865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487909703848869838323243 6731864555773304757484865)
              ·
                refine ⟨5048898416829978568113649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731864555773304757484865 5048898416829978568113649)
                ·
                  refine ⟨3786673812622483926085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048898416829978568113649 3786673812622483926085237)
                  ·
                    refine ⟨355000669933357868070491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3786673812622483926085237 355000669933357868070491)
                    ·
                      rfl

theorem cell22_1037042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1037042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037042 prefixEnd_1037042 := by exact prefixLift 1037042
  have htrace : WordTrace (prefixWord ++ tailWord_1037042) baseStart_1037042 baseEnd_1037042 := by
    simpa [prefixWord, tailWord_1037042, baseEnd_1037042] using wordTrace_append hprefix tailTrace_1037042
  have hstable : (prefixWord ++ tailWord_1037042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037042).length < 2 ^ (prefixWord ++ tailWord_1037042).sum := by decide
  have hdescent : baseEnd_1037042 < baseStart_1037042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037106 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_1037106 : Nat := 118140960795 + 1037106 * 2 ^ 59
def prefixEnd_1037106 : Nat := 4983230072969 + 3 ^ 40 * 1037106 * 2
def baseEnd_1037106 : Nat := 118340859480427678156765

theorem tailTrace_1037106 : CollatzResearch.WordTrace tailWord_1037106 prefixEnd_1037106 118340859480427678156765 := by
  unfold tailWord_1037106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9456590845187390112094793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25217575587166373632252781 9456590845187390112094793)
  ·
    refine ⟨7092443133890542584071095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9456590845187390112094793 7092443133890542584071095)
    ·
      refine ⟨10638664700835813876106643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7092443133890542584071095 10638664700835813876106643)
      ·
        refine ⟨15957997051253720814159965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638664700835813876106643 15957997051253720814159965)
        ·
          refine ⟨5984248894220145305309987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15957997051253720814159965 5984248894220145305309987)
          ·
            refine ⟨8976373341330217957964981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984248894220145305309987 8976373341330217957964981)
            ·
              refine ⟨841535000749707933559217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8976373341330217957964981 841535000749707933559217)
              ·
                refine ⟨631151250562280950169413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841535000749707933559217 631151250562280950169413)
                ·
                  refine ⟨118340859480427678156765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631151250562280950169413 118340859480427678156765)
                  ·
                    rfl

theorem cell22_1037106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_1037106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037106 prefixEnd_1037106 := by exact prefixLift 1037106
  have htrace : WordTrace (prefixWord ++ tailWord_1037106) baseStart_1037106 baseEnd_1037106 := by
    simpa [prefixWord, tailWord_1037106, baseEnd_1037106] using wordTrace_append hprefix tailTrace_1037106
  have hstable : (prefixWord ++ tailWord_1037106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037106).length < 2 ^ (prefixWord ++ tailWord_1037106).sum := by decide
  have hdescent : baseEnd_1037106 < baseStart_1037106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037177 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_1037177 : Nat := 118140960795 + 1037177 * 2 ^ 59
def prefixEnd_1037177 : Nat := 4983230072969 + 3 ^ 40 * 1037177 * 2
def baseEnd_1037177 : Nat := 355046883192262515945077

theorem tailTrace_1037177 : CollatzResearch.WordTrace tailWord_1037177 prefixEnd_1037177 355046883192262515945077 := by
  unfold tailWord_1037177
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828952963492339574213785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25219301975661559716142523 37828952963492339574213785)
  ·
    refine ⟨28371714722619254680660339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37828952963492339574213785 28371714722619254680660339)
    ·
      refine ⟨42557572083928882020990509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28371714722619254680660339 42557572083928882020990509)
      ·
        refine ⟨15959089531473330757871441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42557572083928882020990509 15959089531473330757871441)
        ·
          refine ⟨11969317148604998068403581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15959089531473330757871441 11969317148604998068403581)
          ·
            refine ⟨4488493930726874275651343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11969317148604998068403581 4488493930726874275651343)
            ·
              refine ⟨6732740896090311413477015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488493930726874275651343 6732740896090311413477015)
              ·
                refine ⟨10099111344135467120215523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732740896090311413477015 10099111344135467120215523)
                ·
                  refine ⟨15148667016203200680323285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10099111344135467120215523 15148667016203200680323285)
                  ·
                    refine ⟨355046883192262515945077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15148667016203200680323285 355046883192262515945077)
                    ·
                      rfl

theorem cell22_1037177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_1037177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037177 prefixEnd_1037177 := by exact prefixLift 1037177
  have htrace : WordTrace (prefixWord ++ tailWord_1037177) baseStart_1037177 baseEnd_1037177 := by
    simpa [prefixWord, tailWord_1037177, baseEnd_1037177] using wordTrace_append hprefix tailTrace_1037177
  have hstable : (prefixWord ++ tailWord_1037177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037177).length < 2 ^ (prefixWord ++ tailWord_1037177).sum := by decide
  have hdescent : baseEnd_1037177 < baseStart_1037177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037207 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 8]
def baseStart_1037207 : Nat := 118140960795 + 1037207 * 2 ^ 59
def prefixEnd_1037207 : Nat := 4983230072969 + 3 ^ 40 * 1037207 * 2
def baseEnd_1037207 : Nat := 118352384268450812564995

theorem tailTrace_1037207 : CollatzResearch.WordTrace tailWord_1037207 prefixEnd_1037207 118352384268450812564995 := by
  unfold tailWord_1037207
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830047153383654697805875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25220031435589103131870583 37830047153383654697805875)
  ·
    refine ⟨56745070730075482046708813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37830047153383654697805875 56745070730075482046708813)
    ·
      refine ⟨21279401523778305767515805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56745070730075482046708813 21279401523778305767515805)
      ·
        refine ⟨7979775571416864662818427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21279401523778305767515805 7979775571416864662818427)
        ·
          refine ⟨11969663357125296994227641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979775571416864662818427 11969663357125296994227641)
          ·
            refine ⟨8977247517843972745670731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11969663357125296994227641 8977247517843972745670731)
            ·
              refine ⟨13465871276765959118506097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977247517843972745670731 13465871276765959118506097)
              ·
                refine ⟨10099403457574469338879573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13465871276765959118506097 10099403457574469338879573)
                ·
                  refine ⟨118352384268450812564995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10099403457574469338879573 118352384268450812564995)
                  ·
                    rfl

theorem cell22_1037207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_1037207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037207 prefixEnd_1037207 := by exact prefixLift 1037207
  have htrace : WordTrace (prefixWord ++ tailWord_1037207) baseStart_1037207 baseEnd_1037207 := by
    simpa [prefixWord, tailWord_1037207, baseEnd_1037207] using wordTrace_append hprefix tailTrace_1037207
  have hstable : (prefixWord ++ tailWord_1037207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037207).length < 2 ^ (prefixWord ++ tailWord_1037207).sum := by decide
  have hdescent : baseEnd_1037207 < baseStart_1037207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037239 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1037239 : Nat := 118140960795 + 1037239 * 2 ^ 59
def prefixEnd_1037239 : Nat := 4983230072969 + 3 ^ 40 * 1037239 * 2
def baseEnd_1037239 : Nat := 355068107059315020894887

theorem tailTrace_1037239 : CollatzResearch.WordTrace tailWord_1037239 prefixEnd_1037239 355068107059315020894887 := by
  unfold tailWord_1037239
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831214289267724162970771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25220809526178482775313847 37831214289267724162970771)
  ·
    refine ⟨56746821433901586244456157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37831214289267724162970771 56746821433901586244456157)
    ·
      refine ⟨21280058037713094841671059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56746821433901586244456157 21280058037713094841671059)
      ·
        refine ⟨31920087056569642262506589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21280058037713094841671059 31920087056569642262506589)
        ·
          refine ⟨11970032646213615848439971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31920087056569642262506589 11970032646213615848439971)
          ·
            refine ⟨17955048969320423772659957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970032646213615848439971 17955048969320423772659957)
            ·
              refine ⟨1683285840873789728686871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17955048969320423772659957 1683285840873789728686871)
              ·
                refine ⟨2524928761310684593030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683285840873789728686871 2524928761310684593030307)
                ·
                  refine ⟨3787393141966026889545461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524928761310684593030307 3787393141966026889545461)
                  ·
                    refine ⟨355068107059315020894887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3787393141966026889545461 355068107059315020894887)
                    ·
                      rfl

theorem cell22_1037239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1037239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037239 prefixEnd_1037239 := by exact prefixLift 1037239
  have htrace : WordTrace (prefixWord ++ tailWord_1037239) baseStart_1037239 baseEnd_1037239 := by
    simpa [prefixWord, tailWord_1037239, baseEnd_1037239] using wordTrace_append hprefix tailTrace_1037239
  have hstable : (prefixWord ++ tailWord_1037239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037239).length < 2 ^ (prefixWord ++ tailWord_1037239).sum := by decide
  have hdescent : baseEnd_1037239 < baseStart_1037239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037290 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_1037290 : Nat := 118140960795 + 1037290 * 2 ^ 59
def prefixEnd_1037290 : Nat := 4983230072969 + 3 ^ 40 * 1037290 * 2
def baseEnd_1037290 : Nat := 355085565401567887869731

theorem tailTrace_1037290 : CollatzResearch.WordTrace tailWord_1037290 prefixEnd_1037290 355085565401567887869731 := by
  unfold tailWord_1037290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458268603020739968269331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25222049608055306582051549 9458268603020739968269331)
  ·
    refine ⟨14187402904531109952403997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9458268603020739968269331 14187402904531109952403997)
    ·
      refine ⟨5320276089199166232151499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14187402904531109952403997 5320276089199166232151499)
      ·
        refine ⟨7980414133798749348227249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320276089199166232151499 7980414133798749348227249)
        ·
          refine ⟨5985310600349062011170437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7980414133798749348227249 5985310600349062011170437)
          ·
            refine ⟨1122245737565449127094457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5985310600349062011170437 1122245737565449127094457)
            ·
              refine ⟨841684303174086845320843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122245737565449127094457 841684303174086845320843)
              ·
                refine ⟨1262526454761130267981265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841684303174086845320843 1262526454761130267981265)
                ·
                  refine ⟨946894841070847700985949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262526454761130267981265 946894841070847700985949)
                  ·
                    refine ⟨355085565401567887869731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946894841070847700985949 355085565401567887869731)
                    ·
                      rfl

theorem cell22_1037290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_1037290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037290 prefixEnd_1037290 := by exact prefixLift 1037290
  have htrace : WordTrace (prefixWord ++ tailWord_1037290) baseStart_1037290 baseEnd_1037290 := by
    simpa [prefixWord, tailWord_1037290, baseEnd_1037290] using wordTrace_append hprefix tailTrace_1037290
  have hstable : (prefixWord ++ tailWord_1037290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037290).length < 2 ^ (prefixWord ++ tailWord_1037290).sum := by decide
  have hdescent : baseEnd_1037290 < baseStart_1037290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037335 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 1, 3]
def baseStart_1037335 : Nat := 118140960795 + 1037335 * 2 ^ 59
def prefixEnd_1037335 : Nat := 4983230072969 + 3 ^ 40 * 1037335 * 2
def baseEnd_1037335 : Nat := 355100969821202770494593

theorem tailTrace_1037335 : CollatzResearch.WordTrace tailWord_1037335 prefixEnd_1037335 355100969821202770494593 := by
  unfold tailWord_1037335
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834715696919932558465459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25223143797946621705643639 37834715696919932558465459)
  ·
    refine ⟨56752073545379898837698189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37834715696919932558465459 56752073545379898837698189)
    ·
      refine ⟨21282027579517462064136821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56752073545379898837698189 21282027579517462064136821)
      ·
        refine ⟨1995190085579762068512827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21282027579517462064136821 1995190085579762068512827)
        ·
          refine ⟨2992785128369643102769241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995190085579762068512827 2992785128369643102769241)
          ·
            refine ⟨2244588846277232327076931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992785128369643102769241 2244588846277232327076931)
            ·
              refine ⟨3366883269415848490615397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244588846277232327076931 3366883269415848490615397)
              ·
                refine ⟨631290613015471591990387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3366883269415848490615397 631290613015471591990387)
                ·
                  refine ⟨946935919523207387985581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631290613015471591990387 946935919523207387985581)
                  ·
                    refine ⟨355100969821202770494593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 946935919523207387985581 355100969821202770494593)
                    ·
                      rfl

theorem cell22_1037335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_1037335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037335 prefixEnd_1037335 := by exact prefixLift 1037335
  have htrace : WordTrace (prefixWord ++ tailWord_1037335) baseStart_1037335 baseEnd_1037335 := by
    simpa [prefixWord, tailWord_1037335, baseEnd_1037335] using wordTrace_append hprefix tailTrace_1037335
  have hstable : (prefixWord ++ tailWord_1037335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037335).length < 2 ^ (prefixWord ++ tailWord_1037335).sum := by decide
  have hdescent : baseEnd_1037335 < baseStart_1037335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037346 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1037346 : Nat := 118140960795 + 1037346 * 2 ^ 59
def prefixEnd_1037346 : Nat := 4983230072969 + 3 ^ 40 * 1037346 * 2
def baseEnd_1037346 : Nat := 355104735346002408469559

theorem tailTrace_1037346 : CollatzResearch.WordTrace tailWord_1037346 prefixEnd_1037346 355104735346002408469559 := by
  unfold tailWord_1037346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458779224970020359278973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25223411266586720958077261 9458779224970020359278973)
  ·
    refine ⟨3547042209363757634729615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9458779224970020359278973 3547042209363757634729615)
    ·
      refine ⟨5320563314045636452094423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547042209363757634729615 5320563314045636452094423)
      ·
        refine ⟨7980844971068454678141635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320563314045636452094423 7980844971068454678141635)
        ·
          refine ⟨11971267456602682017212453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7980844971068454678141635 11971267456602682017212453)
          ·
            refine ⟨2244612648113002878227335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11971267456602682017212453 2244612648113002878227335)
            ·
              refine ⟨3366918972169504317341003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244612648113002878227335 3366918972169504317341003)
              ·
                refine ⟨5050378458254256476011505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366918972169504317341003 5050378458254256476011505)
                ·
                  refine ⟨3787783843690692357008629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5050378458254256476011505 3787783843690692357008629)
                  ·
                    refine ⟨355104735346002408469559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3787783843690692357008629 355104735346002408469559)
                    ·
                      rfl

theorem cell22_1037346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1037346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037346 prefixEnd_1037346 := by exact prefixLift 1037346
  have htrace : WordTrace (prefixWord ++ tailWord_1037346) baseStart_1037346 baseEnd_1037346 := by
    simpa [prefixWord, tailWord_1037346, baseEnd_1037346] using wordTrace_append hprefix tailTrace_1037346
  have hstable : (prefixWord ++ tailWord_1037346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037346).length < 2 ^ (prefixWord ++ tailWord_1037346).sum := by decide
  have hdescent : baseEnd_1037346 < baseStart_1037346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037361 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1037361 : Nat := 118140960795 + 1037361 * 2 ^ 59
def prefixEnd_1037361 : Nat := 4983230072969 + 3 ^ 40 * 1037361 * 2
def baseEnd_1037361 : Nat := 355109870152547369344513

theorem tailTrace_1037361 : CollatzResearch.WordTrace tailWord_1037361 prefixEnd_1037361 355109870152547369344513 := by
  unfold tailWord_1037361
  simp only [CollatzResearch.WordTrace]
  refine ⟨37835663994825738998911937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25223775996550492665941291 37835663994825738998911937)
  ·
    refine ⟨28376747996119304249183953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37835663994825738998911937 28376747996119304249183953)
    ·
      refine ⟨21282560997089478186887965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28376747996119304249183953 21282560997089478186887965)
      ·
        refine ⟨7980960373908554320082987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21282560997089478186887965 7980960373908554320082987)
        ·
          refine ⟨11971440560862831480124481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7980960373908554320082987 11971440560862831480124481)
          ·
            refine ⟨8978580420647123610093361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11971440560862831480124481 8978580420647123610093361)
            ·
              refine ⟨6733935315485342707570021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8978580420647123610093361 6733935315485342707570021)
              ·
                refine ⟨1262612871653501757669379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6733935315485342707570021 1262612871653501757669379)
                ·
                  refine ⟨1893919307480252636504069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262612871653501757669379 1893919307480252636504069)
                  ·
                    refine ⟨355109870152547369344513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1893919307480252636504069 355109870152547369344513)
                    ·
                      rfl

theorem cell22_1037361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1037361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037361 prefixEnd_1037361 := by exact prefixLift 1037361
  have htrace : WordTrace (prefixWord ++ tailWord_1037361) baseStart_1037361 baseEnd_1037361 := by
    simpa [prefixWord, tailWord_1037361, baseEnd_1037361] using wordTrace_append hprefix tailTrace_1037361
  have hstable : (prefixWord ++ tailWord_1037361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037361).length < 2 ^ (prefixWord ++ tailWord_1037361).sum := by decide
  have hdescent : baseEnd_1037361 < baseStart_1037361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037421 : List Nat := [1, 5, 1, 1, 2, 3, 1, 8]
def baseStart_1037421 : Nat := 118140960795 + 1037421 * 2 ^ 59
def prefixEnd_1037421 : Nat := 4983230072969 + 3 ^ 40 * 1037421 * 2
def baseEnd_1037421 : Nat := 39458934375414134760481

theorem tailTrace_1037421 : CollatzResearch.WordTrace tailWord_1037421 prefixEnd_1037421 39458934375414134760481 := by
  unfold tailWord_1037421
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837852374608369246096117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25225234916405579497397411 37837852374608369246096117)
  ·
    refine ⟨3547298660119534616821511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37837852374608369246096117 3547298660119534616821511)
    ·
      refine ⟨5320947990179301925232267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547298660119534616821511 5320947990179301925232267)
      ·
        refine ⟨7981421985268952887848401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320947990179301925232267 7981421985268952887848401)
        ·
          refine ⟨5986066488951714665886301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7981421985268952887848401 5986066488951714665886301)
          ·
            refine ⟨2244774933356892999707363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5986066488951714665886301 2244774933356892999707363)
            ·
              refine ⟨3367162400035339499561045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244774933356892999707363 3367162400035339499561045)
              ·
                refine ⟨39458934375414134760481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3367162400035339499561045 39458934375414134760481)
                ·
                  rfl

theorem cell22_1037421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 8].length) (baseStart_1037421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037421 prefixEnd_1037421 := by exact prefixLift 1037421
  have htrace : WordTrace (prefixWord ++ tailWord_1037421) baseStart_1037421 baseEnd_1037421 := by
    simpa [prefixWord, tailWord_1037421, baseEnd_1037421] using wordTrace_append hprefix tailTrace_1037421
  have hstable : (prefixWord ++ tailWord_1037421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037421).length < 2 ^ (prefixWord ++ tailWord_1037421).sum := by decide
  have hdescent : baseEnd_1037421 < baseStart_1037421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037504 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 1, 3]
def baseStart_1037504 : Nat := 118140960795 + 1037504 * 2 ^ 59
def prefixEnd_1037504 : Nat := 4983230072969 + 3 ^ 40 * 1037504 * 2
def baseEnd_1037504 : Nat := 355158821974942663019075

theorem tailTrace_1037504 : CollatzResearch.WordTrace tailWord_1037504 prefixEnd_1037504 355158821974942663019075 := by
  unfold tailWord_1037504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18920439816653837210683783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25227253088871782947578377 18920439816653837210683783)
  ·
    refine ⟨28380659724980755816025675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18920439816653837210683783 28380659724980755816025675)
    ·
      refine ⟨42570989587471133724038513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28380659724980755816025675 42570989587471133724038513)
      ·
        refine ⟨31928242190603350293028885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42570989587471133724038513 31928242190603350293028885)
        ·
          refine ⟨1496636352684532044985729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31928242190603350293028885 1496636352684532044985729)
          ·
            refine ⟨1122477264513399033739297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496636352684532044985729 1122477264513399033739297)
            ·
              refine ⟨841857948385049275304473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122477264513399033739297 841857948385049275304473)
              ·
                refine ⟨631393461288786956478355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841857948385049275304473 631393461288786956478355)
                ·
                  refine ⟨947090191933180434717533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631393461288786956478355 947090191933180434717533)
                  ·
                    refine ⟨355158821974942663019075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947090191933180434717533 355158821974942663019075)
                    ·
                      rfl

theorem cell22_1037504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_1037504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037504 prefixEnd_1037504 := by exact prefixLift 1037504
  have htrace : WordTrace (prefixWord ++ tailWord_1037504) baseStart_1037504 baseEnd_1037504 := by
    simpa [prefixWord, tailWord_1037504, baseEnd_1037504] using wordTrace_append hprefix tailTrace_1037504
  have hstable : (prefixWord ++ tailWord_1037504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037504).length < 2 ^ (prefixWord ++ tailWord_1037504).sum := by decide
  have hdescent : baseEnd_1037504 < baseStart_1037504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037528 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_1037528 : Nat := 118140960795 + 1037528 * 2 ^ 59
def prefixEnd_1037528 : Nat := 4983230072969 + 3 ^ 40 * 1037528 * 2
def baseEnd_1037528 : Nat := 118389012555138200139667

theorem tailTrace_1037528 : CollatzResearch.WordTrace tailWord_1037528 prefixEnd_1037528 118389012555138200139667 := by
  unfold tailWord_1037528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18920877492610363260120619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25227836656813817680160825 18920877492610363260120619)
  ·
    refine ⟨28381316238915544890180929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18920877492610363260120619 28381316238915544890180929)
    ·
      refine ⟨21285987179186658667635697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28381316238915544890180929 21285987179186658667635697)
      ·
        refine ⟨15964490384389994000726773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21285987179186658667635697 15964490384389994000726773)
        ·
          refine ⟨1496670973536561937568135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15964490384389994000726773 1496670973536561937568135)
          ·
            refine ⟨2245006460304842906352203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496670973536561937568135 2245006460304842906352203)
            ·
              refine ⟨3367509690457264359528305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245006460304842906352203 3367509690457264359528305)
              ·
                refine ⟨2525632267842948269646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367509690457264359528305 2525632267842948269646229)
                ·
                  refine ⟨118389012555138200139667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2525632267842948269646229 118389012555138200139667)
                  ·
                    rfl

theorem cell22_1037528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_1037528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037528 prefixEnd_1037528 := by exact prefixLift 1037528
  have htrace : WordTrace (prefixWord ++ tailWord_1037528) baseStart_1037528 baseEnd_1037528 := by
    simpa [prefixWord, tailWord_1037528, baseEnd_1037528] using wordTrace_append hprefix tailTrace_1037528
  have hstable : (prefixWord ++ tailWord_1037528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037528).length < 2 ^ (prefixWord ++ tailWord_1037528).sum := by decide
  have hdescent : baseEnd_1037528 < baseStart_1037528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037558 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1037558 : Nat := 118140960795 + 1037558 * 2 ^ 59
def prefixEnd_1037558 : Nat := 4983230072969 + 3 ^ 40 * 1037558 * 2
def baseEnd_1037558 : Nat := 355177307278504522168909

theorem tailTrace_1037558 : CollatzResearch.WordTrace tailWord_1037558 prefixEnd_1037558 355177307278504522168909 := by
  unfold tailWord_1037558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365178073444502602739583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25228566116741361095888885 2365178073444502602739583)
  ·
    refine ⟨3547767110166753904109375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365178073444502602739583 3547767110166753904109375)
    ·
      refine ⟨5321650665250130856164063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547767110166753904109375 5321650665250130856164063)
      ·
        refine ⟨7982475997875196284246095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321650665250130856164063 7982475997875196284246095)
        ·
          refine ⟨11973713996812794426369143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982475997875196284246095 11973713996812794426369143)
          ·
            refine ⟨17960570995219191639553715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973713996812794426369143 17960570995219191639553715)
            ·
              refine ⟨26940856492828787459330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17960570995219191639553715 26940856492828787459330573)
              ·
                refine ⟨10102821184810795297248965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26940856492828787459330573 10102821184810795297248965)
                ·
                  refine ⟨1894278972152024118234181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10102821184810795297248965 1894278972152024118234181)
                  ·
                    refine ⟨355177307278504522168909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894278972152024118234181 355177307278504522168909)
                    ·
                      rfl

theorem cell22_1037558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1037558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037558 prefixEnd_1037558 := by exact prefixLift 1037558
  have htrace : WordTrace (prefixWord ++ tailWord_1037558) baseStart_1037558 baseEnd_1037558 := by
    simpa [prefixWord, tailWord_1037558, baseEnd_1037558] using wordTrace_append hprefix tailTrace_1037558
  have hstable : (prefixWord ++ tailWord_1037558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037558).length < 2 ^ (prefixWord ++ tailWord_1037558).sum := by decide
  have hdescent : baseEnd_1037558 < baseStart_1037558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037618 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1037618 : Nat := 118140960795 + 1037618 * 2 ^ 59
def prefixEnd_1037618 : Nat := 4983230072969 + 3 ^ 40 * 1037618 * 2
def baseEnd_1037618 : Nat := 118399282168228121889575

theorem tailTrace_1037618 : CollatzResearch.WordTrace tailWord_1037618 prefixEnd_1037618 118399282168228121889575 := by
  unfold tailWord_1037618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461259388723667972754377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25230025036596447927345005 9461259388723667972754377)
  ·
    refine ⟨7095944541542750979565783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9461259388723667972754377 7095944541542750979565783)
    ·
      refine ⟨10643916812314126469348675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095944541542750979565783 10643916812314126469348675)
      ·
        refine ⟨15965875218471189704023013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643916812314126469348675 15965875218471189704023013)
        ·
          refine ⟨2993601603463348069504315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15965875218471189704023013 2993601603463348069504315)
          ·
            refine ⟨4490402405195022104256473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993601603463348069504315 4490402405195022104256473)
            ·
              refine ⟨3367801803896266578192355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490402405195022104256473 3367801803896266578192355)
              ·
                refine ⟨5051702705844399867288533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367801803896266578192355 5051702705844399867288533)
                ·
                  refine ⟨118399282168228121889575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5051702705844399867288533 118399282168228121889575)
                  ·
                    rfl

theorem cell22_1037618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1037618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037618 prefixEnd_1037618 := by exact prefixLift 1037618
  have htrace : WordTrace (prefixWord ++ tailWord_1037618) baseStart_1037618 baseEnd_1037618 := by
    simpa [prefixWord, tailWord_1037618, baseEnd_1037618] using wordTrace_append hprefix tailTrace_1037618
  have hstable : (prefixWord ++ tailWord_1037618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037618).length < 2 ^ (prefixWord ++ tailWord_1037618).sum := by decide
  have hdescent : baseEnd_1037618 < baseStart_1037618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037648 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_1037648 : Nat := 118140960795 + 1037648 * 2 ^ 59
def prefixEnd_1037648 : Nat := 4983230072969 + 3 ^ 40 * 1037648 * 2
def baseEnd_1037648 : Nat := 355208116117774287418633

theorem tailTrace_1037648 : CollatzResearch.WordTrace tailWord_1037648 prefixEnd_1037648 355208116117774287418633 := by
  unfold tailWord_1037648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923065872392993507304799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25230754496523991343073065 18923065872392993507304799)
  ·
    refine ⟨28384598808589490260957199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18923065872392993507304799 28384598808589490260957199)
    ·
      refine ⟨42576898212884235391435799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28384598808589490260957199 42576898212884235391435799)
      ·
        refine ⟨63865347319326353087153699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42576898212884235391435799 63865347319326353087153699)
        ·
          refine ⟨95798020978989529630730549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63865347319326353087153699 95798020978989529630730549)
          ·
            refine ⟨8981064466780268402880989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95798020978989529630730549 8981064466780268402880989)
            ·
              refine ⟨3367899175042600651080371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8981064466780268402880989 3367899175042600651080371)
              ·
                refine ⟨5051848762563900976620557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367899175042600651080371 5051848762563900976620557)
                ·
                  refine ⟨1894443285961462866232709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5051848762563900976620557 1894443285961462866232709)
                  ·
                    refine ⟨355208116117774287418633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894443285961462866232709 355208116117774287418633)
                    ·
                      rfl

theorem cell22_1037648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_1037648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037648 prefixEnd_1037648 := by exact prefixLift 1037648
  have htrace : WordTrace (prefixWord ++ tailWord_1037648) baseStart_1037648 baseEnd_1037648 := by
    simpa [prefixWord, tailWord_1037648, baseEnd_1037648] using wordTrace_append hprefix tailTrace_1037648
  have hstable : (prefixWord ++ tailWord_1037648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037648).length < 2 ^ (prefixWord ++ tailWord_1037648).sum := by decide
  have hdescent : baseEnd_1037648 < baseStart_1037648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037680 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_1037680 : Nat := 118140960795 + 1037680 * 2 ^ 59
def prefixEnd_1037680 : Nat := 4983230072969 + 3 ^ 40 * 1037680 * 2
def baseEnd_1037680 : Nat := 118406356790578956872845

theorem tailTrace_1037680 : CollatzResearch.WordTrace tailWord_1037680 prefixEnd_1037680 118406356790578956872845 := by
  unfold tailWord_1037680
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923649440335028239887247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25231532587113370986516329 18923649440335028239887247)
  ·
    refine ⟨28385474160502542359830871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18923649440335028239887247 28385474160502542359830871)
    ·
      refine ⟨42578211240753813539746307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28385474160502542359830871 42578211240753813539746307)
      ·
        refine ⟨63867316861130720309619461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42578211240753813539746307 63867316861130720309619461)
        ·
          refine ⟨11975121911462010058053649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63867316861130720309619461 11975121911462010058053649)
          ·
            refine ⟨8981341433596507543540237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11975121911462010058053649 8981341433596507543540237)
            ·
              refine ⟨3368003037598690328827589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8981341433596507543540237 3368003037598690328827589)
              ·
                refine ⟨631500569549754436655173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3368003037598690328827589 631500569549754436655173)
                ·
                  refine ⟨118406356790578956872845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631500569549754436655173 118406356790578956872845)
                  ·
                    rfl

theorem cell22_1037680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_1037680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037680 prefixEnd_1037680 := by exact prefixLift 1037680
  have htrace : WordTrace (prefixWord ++ tailWord_1037680) baseStart_1037680 baseEnd_1037680 := by
    simpa [prefixWord, tailWord_1037680, baseEnd_1037680] using wordTrace_append hprefix tailTrace_1037680
  have hstable : (prefixWord ++ tailWord_1037680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037680).length < 2 ^ (prefixWord ++ tailWord_1037680).sum := by decide
  have hdescent : baseEnd_1037680 < baseStart_1037680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037693 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1037693 : Nat := 118140960795 + 1037693 * 2 ^ 59
def prefixEnd_1037693 : Nat := 4983230072969 + 3 ^ 40 * 1037693 * 2
def baseEnd_1037693 : Nat := 355223520537409170043495

theorem tailTrace_1037693 : CollatzResearch.WordTrace tailWord_1037693 prefixEnd_1037693 355223520537409170043495 := by
  unfold tailWord_1037693
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847773029622959699997733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25231848686415306466665155 37847773029622959699997733)
  ·
    refine ⟨7096457443054304943749575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37847773029622959699997733 7096457443054304943749575)
    ·
      refine ⟨10644686164581457415624363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096457443054304943749575 10644686164581457415624363)
      ·
        refine ⟨15967029246872186123436545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644686164581457415624363 15967029246872186123436545)
        ·
          refine ⟨11975271935154139592577409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15967029246872186123436545 11975271935154139592577409)
          ·
            refine ⟨8981453951365604694433057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11975271935154139592577409 8981453951365604694433057)
            ·
              refine ⟨6736090463524203520824793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981453951365604694433057 6736090463524203520824793)
              ·
                refine ⟨5052067847643152640618595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736090463524203520824793 5052067847643152640618595)
                ·
                  refine ⟨7578101771464728960927893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052067847643152640618595 7578101771464728960927893)
                  ·
                    refine ⟨355223520537409170043495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7578101771464728960927893 355223520537409170043495)
                    ·
                      rfl

theorem cell22_1037693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1037693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037693 prefixEnd_1037693 := by exact prefixLift 1037693
  have htrace : WordTrace (prefixWord ++ tailWord_1037693) baseStart_1037693 baseEnd_1037693 := by
    simpa [prefixWord, tailWord_1037693, baseEnd_1037693] using wordTrace_append hprefix tailTrace_1037693
  have hstable : (prefixWord ++ tailWord_1037693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037693).length < 2 ^ (prefixWord ++ tailWord_1037693).sum := by decide
  have hdescent : baseEnd_1037693 < baseStart_1037693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037740 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_1037740 : Nat := 118140960795 + 1037740 * 2 ^ 59
def prefixEnd_1037740 : Nat := 4983230072969 + 3 ^ 40 * 1037740 * 2
def baseEnd_1037740 : Nat := 355239609597916714118351

theorem tailTrace_1037740 : CollatzResearch.WordTrace tailWord_1037740 prefixEnd_1037740 355239609597916714118351 := by
  unfold tailWord_1037740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924743630226343363479337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25232991506968457817972449 18924743630226343363479337)
  ·
    refine ⟨14193557722669757522609503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18924743630226343363479337 14193557722669757522609503)
    ·
      refine ⟨21290336584004636283914255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14193557722669757522609503 21290336584004636283914255)
      ·
        refine ⟨31935504876006954425871383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21290336584004636283914255 31935504876006954425871383)
        ·
          refine ⟨47903257314010431638807075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31935504876006954425871383 47903257314010431638807075)
          ·
            refine ⟨71854885971015647458210613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47903257314010431638807075 71854885971015647458210613)
            ·
              refine ⟨6736395559782716949207245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71854885971015647458210613 6736395559782716949207245)
              ·
                refine ⟨2526148334918518855952717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6736395559782716949207245 2526148334918518855952717)
                ·
                  refine ⟨947305625594444570982269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2526148334918518855952717 947305625594444570982269)
                  ·
                    refine ⟨355239609597916714118351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947305625594444570982269 355239609597916714118351)
                    ·
                      rfl

theorem cell22_1037740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_1037740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037740 prefixEnd_1037740 := by exact prefixLift 1037740
  have htrace : WordTrace (prefixWord ++ tailWord_1037740) baseStart_1037740 baseEnd_1037740 := by
    simpa [prefixWord, tailWord_1037740, baseEnd_1037740] using wordTrace_append hprefix tailTrace_1037740
  have hstable : (prefixWord ++ tailWord_1037740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037740).length < 2 ^ (prefixWord ++ tailWord_1037740).sum := by decide
  have hdescent : baseEnd_1037740 < baseStart_1037740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037774 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1037774 : Nat := 118140960795 + 1037774 * 2 ^ 59
def prefixEnd_1037774 : Nat := 4983230072969 + 3 ^ 40 * 1037774 * 2
def baseEnd_1037774 : Nat := 355251248492751958768247

theorem tailTrace_1037774 : CollatzResearch.WordTrace tailWord_1037774 prefixEnd_1037774 355251248492751958768247 := by
  unfold tailWord_1037774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731340917791188816712047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25233818228219673689130917 4731340917791188816712047)
  ·
    refine ⟨7097011376686783225068071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4731340917791188816712047 7097011376686783225068071)
    ·
      refine ⟨10645517065030174837602107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7097011376686783225068071 10645517065030174837602107)
      ·
        refine ⟨15968275597545262256403161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10645517065030174837602107 15968275597545262256403161)
        ·
          refine ⟨11976206698158946692302371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968275597545262256403161 11976206698158946692302371)
          ·
            refine ⟨17964310047238420038453557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976206698158946692302371 17964310047238420038453557)
            ·
              refine ⟨1684154066928601878605021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17964310047238420038453557 1684154066928601878605021)
              ·
                refine ⟨631557775098225704476883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1684154066928601878605021 631557775098225704476883)
                ·
                  refine ⟨947336662647338556715325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631557775098225704476883 947336662647338556715325)
                  ·
                    refine ⟨355251248492751958768247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947336662647338556715325 355251248492751958768247)
                    ·
                      rfl

theorem cell22_1037774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1037774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037774 prefixEnd_1037774 := by exact prefixLift 1037774
  have htrace : WordTrace (prefixWord ++ tailWord_1037774) baseStart_1037774 baseEnd_1037774 := by
    simpa [prefixWord, tailWord_1037774, baseEnd_1037774] using wordTrace_append hprefix tailTrace_1037774
  have hstable : (prefixWord ++ tailWord_1037774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037774).length < 2 ^ (prefixWord ++ tailWord_1037774).sum := by decide
  have hdescent : baseEnd_1037774 < baseStart_1037774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037800 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1037800 : Nat := 118140960795 + 1037800 * 2 ^ 59
def prefixEnd_1037800 : Nat := 4983230072969 + 3 ^ 40 * 1037800 * 2
def baseEnd_1037800 : Nat := 355260148824096557618167

theorem tailTrace_1037800 : CollatzResearch.WordTrace tailWord_1037800 prefixEnd_1037800 355260148824096557618167 := by
  unfold tailWord_1037800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925837820117658487071427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25234450426823544649428569 18925837820117658487071427)
  ·
    refine ⟨28388756730176487730607141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18925837820117658487071427 28388756730176487730607141)
    ·
      refine ⟨5322891886908091449488839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28388756730176487730607141 5322891886908091449488839)
      ·
        refine ⟨7984337830362137174233259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322891886908091449488839 7984337830362137174233259)
        ·
          refine ⟨11976506745543205761349889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984337830362137174233259 11976506745543205761349889)
          ·
            refine ⟨8982380059157404321012417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11976506745543205761349889 8982380059157404321012417)
            ·
              refine ⟨6736785044368053240759313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982380059157404321012417 6736785044368053240759313)
              ·
                refine ⟨5052588783276039930569485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736785044368053240759313 5052588783276039930569485)
                ·
                  refine ⟨1894720793728514973963557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5052588783276039930569485 1894720793728514973963557)
                  ·
                    refine ⟨355260148824096557618167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894720793728514973963557 355260148824096557618167)
                    ·
                      rfl

theorem cell22_1037800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1037800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037800 prefixEnd_1037800 := by exact prefixLift 1037800
  have htrace : WordTrace (prefixWord ++ tailWord_1037800) baseStart_1037800 baseEnd_1037800 := by
    simpa [prefixWord, tailWord_1037800, baseEnd_1037800] using wordTrace_append hprefix tailTrace_1037800
  have hstable : (prefixWord ++ tailWord_1037800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037800).length < 2 ^ (prefixWord ++ tailWord_1037800).sum := by decide
  have hdescent : baseEnd_1037800 < baseStart_1037800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037834 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_1037834 : Nat := 118140960795 + 1037834 * 2 ^ 59
def prefixEnd_1037834 : Nat := 4983230072969 + 3 ^ 40 * 1037834 * 2
def baseEnd_1037834 : Nat := 355271787718931802268063

theorem tailTrace_1037834 : CollatzResearch.WordTrace tailWord_1037834 prefixEnd_1037834 355271787718931802268063 := by
  unfold tailWord_1037834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9463228930528035195220139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25235277148074760520587037 9463228930528035195220139)
  ·
    refine ⟨14194843395792052792830209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9463228930528035195220139 14194843395792052792830209)
    ·
      refine ⟨10646132546844039594622657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14194843395792052792830209 10646132546844039594622657)
      ·
        refine ⟨7984599410133029695966993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10646132546844039594622657 7984599410133029695966993)
        ·
          refine ⟨5988449557599772271975245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7984599410133029695966993 5988449557599772271975245)
          ·
            refine ⟨2245668584099914601990717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5988449557599772271975245 2245668584099914601990717)
            ·
              refine ⟨842125719037467975746519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245668584099914601990717 842125719037467975746519)
              ·
                refine ⟨1263188578556201963619779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842125719037467975746519 1263188578556201963619779)
                ·
                  refine ⟨1894782867834302945429669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263188578556201963619779 1894782867834302945429669)
                  ·
                    refine ⟨355271787718931802268063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894782867834302945429669 355271787718931802268063)
                    ·
                      rfl

theorem cell22_1037834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_1037834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037834 prefixEnd_1037834 := by exact prefixLift 1037834
  have htrace : WordTrace (prefixWord ++ tailWord_1037834) baseStart_1037834 baseEnd_1037834 := by
    simpa [prefixWord, tailWord_1037834, baseEnd_1037834] using wordTrace_append hprefix tailTrace_1037834
  have hstable : (prefixWord ++ tailWord_1037834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037834).length < 2 ^ (prefixWord ++ tailWord_1037834).sum := by decide
  have hdescent : baseEnd_1037834 < baseStart_1037834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037843 : List Nat := [1, 1, 1, 2, 1, 16]
def baseStart_1037843 : Nat := 118140960795 + 1037843 * 2 ^ 59
def prefixEnd_1037843 : Nat := 4983230072969 + 3 ^ 40 * 1037843 * 2
def baseEnd_1037843 : Nat := 4386109488924182454235

theorem tailTrace_1037843 : CollatzResearch.WordTrace tailWord_1037843 prefixEnd_1037843 4386109488924182454235 := by
  unfold tailWord_1037843
  simp only [CollatzResearch.WordTrace]
  refine ⟨37853243979079535317958183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25235495986053023545305455 37853243979079535317958183)
  ·
    refine ⟨56779865968619302976937275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37853243979079535317958183 56779865968619302976937275)
    ·
      refine ⟨85169798952928954465405913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56779865968619302976937275 85169798952928954465405913)
      ·
        refine ⟨63877349214696715849054435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85169798952928954465405913 63877349214696715849054435)
        ·
          refine ⟨95816023822045073773581653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63877349214696715849054435 95816023822045073773581653)
          ·
            refine ⟨4386109488924182454235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 95816023822045073773581653 4386109488924182454235)
            ·
              rfl

theorem cell22_1037843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 16].length) (baseStart_1037843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037843 prefixEnd_1037843 := by exact prefixLift 1037843
  have htrace : WordTrace (prefixWord ++ tailWord_1037843) baseStart_1037843 baseEnd_1037843 := by
    simpa [prefixWord, tailWord_1037843, baseEnd_1037843] using wordTrace_append hprefix tailTrace_1037843
  have hstable : (prefixWord ++ tailWord_1037843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037843).length < 2 ^ (prefixWord ++ tailWord_1037843).sum := by decide
  have hdescent : baseEnd_1037843 < baseStart_1037843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037864 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1037864 : Nat := 118140960795 + 1037864 * 2 ^ 59
def prefixEnd_1037864 : Nat := 4983230072969 + 3 ^ 40 * 1037864 * 2
def baseEnd_1037864 : Nat := 355282057332021724017971

theorem tailTrace_1037864 : CollatzResearch.WordTrace tailWord_1037864 prefixEnd_1037864 355282057332021724017971 := by
  unfold tailWord_1037864
  simp only [CollatzResearch.WordTrace]
  refine ⟨18927004956001727952236323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25236006608002303936315097 18927004956001727952236323)
  ·
    refine ⟨28390507434002591928354485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18927004956001727952236323 28390507434002591928354485)
    ·
      refine ⟨2661610071937742993283233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28390507434002591928354485 2661610071937742993283233)
      ·
        refine ⟨1996207553953307244962425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661610071937742993283233 1996207553953307244962425)
        ·
          refine ⟨1497155665464980433721819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996207553953307244962425 1497155665464980433721819)
          ·
            refine ⟨2245733498197470650582729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497155665464980433721819 2245733498197470650582729)
            ·
              refine ⟨1684300123648102987937047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245733498197470650582729 1684300123648102987937047)
              ·
                refine ⟨2526450185472154481905571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684300123648102987937047 2526450185472154481905571)
                ·
                  refine ⟨3789675278208231722858357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526450185472154481905571 3789675278208231722858357)
                  ·
                    refine ⟨355282057332021724017971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3789675278208231722858357 355282057332021724017971)
                    ·
                      rfl

theorem cell22_1037864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1037864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037864 prefixEnd_1037864 := by exact prefixLift 1037864
  have htrace : WordTrace (prefixWord ++ tailWord_1037864) baseStart_1037864 baseEnd_1037864 := by
    simpa [prefixWord, tailWord_1037864, baseEnd_1037864] using wordTrace_append hprefix tailTrace_1037864
  have hstable : (prefixWord ++ tailWord_1037864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037864).length < 2 ^ (prefixWord ++ tailWord_1037864).sum := by decide
  have hdescent : baseEnd_1037864 < baseStart_1037864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037877 : List Nat := [1, 3, 3, 1, 1, 4, 3, 6]
def baseStart_1037877 : Nat := 118140960795 + 1037877 * 2 ^ 59
def prefixEnd_1037877 : Nat := 4983230072969 + 3 ^ 40 * 1037877 * 2
def baseEnd_1037877 : Nat := 39476278610854891493659

theorem tailTrace_1037877 : CollatzResearch.WordTrace tailWord_1037877 prefixEnd_1037877 39476278610854891493659 := by
  unfold tailWord_1037877
  simp only [CollatzResearch.WordTrace]
  refine ⟨37854484060956359124695885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25236322707304239416463923 37854484060956359124695885)
  ·
    refine ⟨14195431522858634671760957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37854484060956359124695885 14195431522858634671760957)
    ·
      refine ⟨5323286821071988001910359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14195431522858634671760957 5323286821071988001910359)
      ·
        refine ⟨7984930231607982002865539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323286821071988001910359 7984930231607982002865539)
        ·
          refine ⟨11977395347411973004298309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984930231607982002865539 11977395347411973004298309)
          ·
            refine ⟨2245761627639744938305933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11977395347411973004298309 2245761627639744938305933)
            ·
              refine ⟨842160610364904351864725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245761627639744938305933 842160610364904351864725)
              ·
                refine ⟨39476278610854891493659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 842160610364904351864725 39476278610854891493659)
                ·
                  rfl

theorem cell22_1037877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 6].length) (baseStart_1037877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037877 prefixEnd_1037877 := by exact prefixLift 1037877
  have htrace : WordTrace (prefixWord ++ tailWord_1037877) baseStart_1037877 baseEnd_1037877 := by
    simpa [prefixWord, tailWord_1037877, baseEnd_1037877] using wordTrace_append hprefix tailTrace_1037877
  have hstable : (prefixWord ++ tailWord_1037877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037877).length < 2 ^ (prefixWord ++ tailWord_1037877).sum := by decide
  have hdescent : baseEnd_1037877 < baseStart_1037877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037894 : List Nat := [6, 1, 1, 1, 3, 1, 9]
def baseStart_1037894 : Nat := 118140960795 + 1037894 * 2 ^ 59
def prefixEnd_1037894 : Nat := 4983230072969 + 3 ^ 40 * 1037894 * 2
def baseEnd_1037894 : Nat := 13158975072041172065477

theorem tailTrace_1037894 : CollatzResearch.WordTrace tailWord_1037894 prefixEnd_1037894 13158975072041172065477 := by
  unfold tailWord_1037894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182972003184211594627023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25236736067929847352043157 1182972003184211594627023)
  ·
    refine ⟨1774458004776317391940535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1182972003184211594627023 1774458004776317391940535)
    ·
      refine ⟨2661687007164476087910803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774458004776317391940535 2661687007164476087910803)
      ·
        refine ⟨3992530510746714131866205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661687007164476087910803 3992530510746714131866205)
        ·
          refine ⟨1497198941530017799449827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3992530510746714131866205 1497198941530017799449827)
          ·
            refine ⟨2245798412295026699174741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497198941530017799449827 2245798412295026699174741)
            ·
              refine ⟨13158975072041172065477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2245798412295026699174741 13158975072041172065477)
              ·
                rfl

theorem cell22_1037894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 9].length) (baseStart_1037894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037894 prefixEnd_1037894 := by exact prefixLift 1037894
  have htrace : WordTrace (prefixWord ++ tailWord_1037894) baseStart_1037894 baseEnd_1037894 := by
    simpa [prefixWord, tailWord_1037894, baseEnd_1037894] using wordTrace_append hprefix tailTrace_1037894
  have hstable : (prefixWord ++ tailWord_1037894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037894).length < 2 ^ (prefixWord ++ tailWord_1037894).sum := by decide
  have hdescent : baseEnd_1037894 < baseStart_1037894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037905 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 7]
def baseStart_1037905 : Nat := 118140960795 + 1037905 * 2 ^ 59
def prefixEnd_1037905 : Nat := 4983230072969 + 3 ^ 40 * 1037905 * 2
def baseEnd_1037905 : Nat := 118432030823303761247615

theorem tailTrace_1037905 : CollatzResearch.WordTrace tailWord_1037905 prefixEnd_1037905 118432030823303761247615 := by
  unfold tailWord_1037905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37855505304854919906715169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25237003536569946604476779 37855505304854919906715169)
  ·
    refine ⟨28391628978641189930036377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37855505304854919906715169 28391628978641189930036377)
    ·
      refine ⟨21293721733980892447527283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28391628978641189930036377 21293721733980892447527283)
      ·
        refine ⟨31940582600971338671290925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21293721733980892447527283 31940582600971338671290925)
        ·
          refine ⟨11977718475364252001734097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31940582600971338671290925 11977718475364252001734097)
          ·
            refine ⟨8983288856523189001300573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11977718475364252001734097 8983288856523189001300573)
            ·
              refine ⟨3368733321196195875487715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8983288856523189001300573 3368733321196195875487715)
              ·
                refine ⟨5053099981794293813231573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368733321196195875487715 5053099981794293813231573)
                ·
                  refine ⟨118432030823303761247615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5053099981794293813231573 118432030823303761247615)
                  ·
                    rfl

theorem cell22_1037905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_1037905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037905 prefixEnd_1037905 := by exact prefixLift 1037905
  have htrace : WordTrace (prefixWord ++ tailWord_1037905) baseStart_1037905 baseEnd_1037905 := by
    simpa [prefixWord, tailWord_1037905, baseEnd_1037905] using wordTrace_append hprefix tailTrace_1037905
  have hstable : (prefixWord ++ tailWord_1037905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037905).length < 2 ^ (prefixWord ++ tailWord_1037905).sum := by decide
  have hdescent : baseEnd_1037905 < baseStart_1037905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037952 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_1037952 : Nat := 118140960795 + 1037952 * 2 ^ 59
def prefixEnd_1037952 : Nat := 4983230072969 + 3 ^ 40 * 1037952 * 2
def baseEnd_1037952 : Nat := 355312181530418827817701

theorem tailTrace_1037952 : CollatzResearch.WordTrace tailWord_1037952 prefixEnd_1037952 355312181530418827817701 := by
  unfold tailWord_1037952
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928609767842323466838055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25238146357123097955784073 18928609767842323466838055)
  ·
    refine ⟨28392914651763485200257083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928609767842323466838055 28392914651763485200257083)
    ·
      refine ⟨42589371977645227800385625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392914651763485200257083 42589371977645227800385625)
      ·
        refine ⟨31942028983233920850289219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42589371977645227800385625 31942028983233920850289219)
        ·
          refine ⟨47913043474850881275433829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31942028983233920850289219 47913043474850881275433829)
          ·
            refine ⟨8983695651534540239143843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47913043474850881275433829 8983695651534540239143843)
            ·
              refine ⟨13475543477301810358715765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983695651534540239143843 13475543477301810358715765)
              ·
                refine ⟨1263332200997044721129603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13475543477301810358715765 1263332200997044721129603)
                ·
                  refine ⟨1894998301495567081694405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263332200997044721129603 1894998301495567081694405)
                  ·
                    refine ⟨355312181530418827817701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894998301495567081694405 355312181530418827817701)
                    ·
                      rfl

theorem cell22_1037952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_1037952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037952 prefixEnd_1037952 := by exact prefixLift 1037952
  have htrace : WordTrace (prefixWord ++ tailWord_1037952) baseStart_1037952 baseEnd_1037952 := by
    simpa [prefixWord, tailWord_1037952, baseEnd_1037952] using wordTrace_append hprefix tailTrace_1037952
  have hstable : (prefixWord ++ tailWord_1037952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037952).length < 2 ^ (prefixWord ++ tailWord_1037952).sum := by decide
  have hdescent : baseEnd_1037952 < baseStart_1037952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037960 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1037960 : Nat := 118140960795 + 1037960 * 2 ^ 59
def prefixEnd_1037960 : Nat := 4983230072969 + 3 ^ 40 * 1037960 * 2
def baseEnd_1037960 : Nat := 355314920093909473617677

theorem tailTrace_1037960 : CollatzResearch.WordTrace tailWord_1037960 prefixEnd_1037960 355314920093909473617677 := by
  unfold tailWord_1037960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928755659827832149983667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25238340879770442866644889 18928755659827832149983667)
  ·
    refine ⟨28393133489741748224975501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928755659827832149983667 28393133489741748224975501)
    ·
      refine ⟨10647425058653155584365813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28393133489741748224975501 10647425058653155584365813)
      ·
        refine ⟨998196099248733336034295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10647425058653155584365813 998196099248733336034295)
        ·
          refine ⟨1497294148873100004051443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998196099248733336034295 1497294148873100004051443)
          ·
            refine ⟨2245941223309650006077165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497294148873100004051443 2245941223309650006077165)
            ·
              refine ⟨842227958741118752278937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245941223309650006077165 842227958741118752278937)
              ·
                refine ⟨631670969055839064209203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842227958741118752278937 631670969055839064209203)
                ·
                  refine ⟨947506453583758596313805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631670969055839064209203 947506453583758596313805)
                  ·
                    refine ⟨355314920093909473617677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947506453583758596313805 355314920093909473617677)
                    ·
                      rfl

theorem cell22_1037960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1037960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037960 prefixEnd_1037960 := by exact prefixLift 1037960
  have htrace : WordTrace (prefixWord ++ tailWord_1037960) baseStart_1037960 baseEnd_1037960 := by
    simpa [prefixWord, tailWord_1037960, baseEnd_1037960] using wordTrace_append hprefix tailTrace_1037960
  have hstable : (prefixWord ++ tailWord_1037960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037960).length < 2 ^ (prefixWord ++ tailWord_1037960).sum := by decide
  have hdescent : baseEnd_1037960 < baseStart_1037960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037986 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1037986 : Nat := 118140960795 + 1037986 * 2 ^ 59
def prefixEnd_1037986 : Nat := 4983230072969 + 3 ^ 40 * 1037986 * 2
def baseEnd_1037986 : Nat := 355323820425254072467597

theorem tailTrace_1037986 : CollatzResearch.WordTrace tailWord_1037986 prefixEnd_1037986 355323820425254072467597 := by
  unfold tailWord_1037986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464614904390367685103453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25238973078374313826942541 9464614904390367685103453)
  ·
    refine ⟨3549230589146387881913795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9464614904390367685103453 3549230589146387881913795)
    ·
      refine ⟨5323845883719581822870693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549230589146387881913795 5323845883719581822870693)
      ·
        refine ⟨998221103197421591788255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5323845883719581822870693 998221103197421591788255)
        ·
          refine ⟨1497331654796132387682383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998221103197421591788255 1497331654796132387682383)
          ·
            refine ⟨2245997482194198581523575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497331654796132387682383 2245997482194198581523575)
            ·
              refine ⟨3368996223291297872285363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245997482194198581523575 3368996223291297872285363)
              ·
                refine ⟨5053494334936946808428045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368996223291297872285363 5053494334936946808428045)
                ·
                  refine ⟨1895060375601355053160517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053494334936946808428045 1895060375601355053160517)
                  ·
                    refine ⟨355323820425254072467597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895060375601355053160517 355323820425254072467597)
                    ·
                      rfl

theorem cell22_1037986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1037986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1037986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1037986 prefixEnd_1037986 := by exact prefixLift 1037986
  have htrace : WordTrace (prefixWord ++ tailWord_1037986) baseStart_1037986 baseEnd_1037986 := by
    simpa [prefixWord, tailWord_1037986, baseEnd_1037986] using wordTrace_append hprefix tailTrace_1037986
  have hstable : (prefixWord ++ tailWord_1037986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037986).length < 2 ^ (prefixWord ++ tailWord_1037986).sum := by decide
  have hdescent : baseEnd_1037986 < baseStart_1037986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038014 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1038014 : Nat := 118140960795 + 1038014 * 2 ^ 59
def prefixEnd_1038014 : Nat := 4983230072969 + 3 ^ 40 * 1038014 * 2
def baseEnd_1038014 : Nat := 355333405397471332767511

theorem tailTrace_1038014 : CollatzResearch.WordTrace tailWord_1038014 prefixEnd_1038014 355333405397471332767511 := by
  unfold tailWord_1038014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732435107682503940304137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25239653907640021014955397 4732435107682503940304137)
  ·
    refine ⟨3549326330761877955228103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732435107682503940304137 3549326330761877955228103)
    ·
      refine ⟨5323989496142816932842155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549326330761877955228103 5323989496142816932842155)
      ·
        refine ⟨7985984244214225399263233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323989496142816932842155 7985984244214225399263233)
        ·
          refine ⟨5989488183160669049447425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7985984244214225399263233 5989488183160669049447425)
          ·
            refine ⟨4492116137370501787085569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5989488183160669049447425 4492116137370501787085569)
            ·
              refine ⟨3369087103027876340314177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492116137370501787085569 3369087103027876340314177)
              ·
                refine ⟨2526815327270907255235633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369087103027876340314177 2526815327270907255235633)
                ·
                  refine ⟨1895111495453180441426725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526815327270907255235633 1895111495453180441426725)
                  ·
                    refine ⟨355333405397471332767511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895111495453180441426725 355333405397471332767511)
                    ·
                      rfl

theorem cell22_1038014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1038014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038014 prefixEnd_1038014 := by exact prefixLift 1038014
  have htrace : WordTrace (prefixWord ++ tailWord_1038014) baseStart_1038014 baseEnd_1038014 := by
    simpa [prefixWord, tailWord_1038014, baseEnd_1038014] using wordTrace_append hprefix tailTrace_1038014
  have hstable : (prefixWord ++ tailWord_1038014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038014).length < 2 ^ (prefixWord ++ tailWord_1038014).sum := by decide
  have hdescent : baseEnd_1038014 < baseStart_1038014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038027 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 7, 3]
def baseStart_1038027 : Nat := 118140960795 + 1038027 * 2 ^ 59
def prefixEnd_1038027 : Nat := 4983230072969 + 3 ^ 40 * 1038027 * 2
def baseEnd_1038027 : Nat := 355337855563143632192471

theorem tailTrace_1038027 : CollatzResearch.WordTrace tailWord_1038027 prefixEnd_1038027 355337855563143632192471 := by
  unfold tailWord_1038027
  simp only [CollatzResearch.WordTrace]
  refine ⟨37859955010412934742656335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25239970006941956495104223 37859955010412934742656335)
  ·
    refine ⟨56789932515619402113984503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37859955010412934742656335 56789932515619402113984503)
    ·
      refine ⟨85184898773429103170976755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56789932515619402113984503 85184898773429103170976755)
      ·
        refine ⟨127777348160143654756465133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85184898773429103170976755 127777348160143654756465133)
        ·
          refine ⟨47916505560053870533674425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127777348160143654756465133 47916505560053870533674425)
          ·
            refine ⟨35937379170040402900255819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47916505560053870533674425 35937379170040402900255819)
            ·
              refine ⟨53906068755060604350383729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35937379170040402900255819 53906068755060604350383729)
              ·
                refine ⟨40429551566295453262787797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53906068755060604350383729 40429551566295453262787797)
                ·
                  refine ⟨947567614835049685846589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 40429551566295453262787797 947567614835049685846589)
                  ·
                    refine ⟨355337855563143632192471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947567614835049685846589 355337855563143632192471)
                    ·
                      rfl

theorem cell22_1038027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3].length) (baseStart_1038027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038027 prefixEnd_1038027 := by exact prefixLift 1038027
  have htrace : WordTrace (prefixWord ++ tailWord_1038027) baseStart_1038027 baseEnd_1038027 := by
    simpa [prefixWord, tailWord_1038027, baseEnd_1038027] using wordTrace_append hprefix tailTrace_1038027
  have hstable : (prefixWord ++ tailWord_1038027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038027).length < 2 ^ (prefixWord ++ tailWord_1038027).sum := by decide
  have hdescent : baseEnd_1038027 < baseStart_1038027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038078 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1038078 : Nat := 118140960795 + 1038078 * 2 ^ 59
def prefixEnd_1038078 : Nat := 4983230072969 + 3 ^ 40 * 1038078 * 2
def baseEnd_1038078 : Nat := 355355313905396499167315

theorem tailTrace_1038078 : CollatzResearch.WordTrace tailWord_1038078 prefixEnd_1038078 355355313905396499167315 := by
  unfold tailWord_1038078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732726891653521306595361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25241210088818780301841925 4732726891653521306595361)
  ·
    refine ⟨3549545168740140979946521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4732726891653521306595361 3549545168740140979946521)
    ·
      refine ⟨2662158876555105734959891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549545168740140979946521 2662158876555105734959891)
      ·
        refine ⟨3993238314832658602439837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662158876555105734959891 3993238314832658602439837)
        ·
          refine ⟨1497464368062246975914939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993238314832658602439837 1497464368062246975914939)
          ·
            refine ⟨2246196552093370463872409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497464368062246975914939 2246196552093370463872409)
            ·
              refine ⟨1684647414070027847904307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246196552093370463872409 1684647414070027847904307)
              ·
                refine ⟨2526971121105041771856461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684647414070027847904307 2526971121105041771856461)
                ·
                  refine ⟨947614170414390664446173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2526971121105041771856461 947614170414390664446173)
                  ·
                    refine ⟨355355313905396499167315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947614170414390664446173 355355313905396499167315)
                    ·
                      rfl

theorem cell22_1038078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1038078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038078 prefixEnd_1038078 := by exact prefixLift 1038078
  have htrace : WordTrace (prefixWord ++ tailWord_1038078) baseStart_1038078 baseEnd_1038078 := by
    simpa [prefixWord, tailWord_1038078, baseEnd_1038078] using wordTrace_append hprefix tailTrace_1038078
  have hstable : (prefixWord ++ tailWord_1038078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038078).length < 2 ^ (prefixWord ++ tailWord_1038078).sum := by decide
  have hdescent : baseEnd_1038078 < baseStart_1038078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038104 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1038104 : Nat := 118140960795 + 1038104 * 2 ^ 59
def prefixEnd_1038104 : Nat := 4983230072969 + 3 ^ 40 * 1038104 * 2
def baseEnd_1038104 : Nat := 355364214236741098017235

theorem tailTrace_1038104 : CollatzResearch.WordTrace tailWord_1038104 prefixEnd_1038104 355364214236741098017235 := by
  unfold tailWord_1038104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931381715566988446604683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25241842287422651262139577 18931381715566988446604683)
  ·
    refine ⟨28397072573350482669907025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18931381715566988446604683 28397072573350482669907025)
    ·
      refine ⟨21297804430012862002430269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28397072573350482669907025 21297804430012862002430269)
      ·
        refine ⟨7986676661254823250911351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21297804430012862002430269 7986676661254823250911351)
        ·
          refine ⟨11980014991882234876367027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986676661254823250911351 11980014991882234876367027)
          ·
            refine ⟨17970022487823352314550541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980014991882234876367027 17970022487823352314550541)
            ·
              refine ⟨6738758432933757117956453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17970022487823352314550541 6738758432933757117956453)
              ·
                refine ⟨1263517206175079459616835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6738758432933757117956453 1263517206175079459616835)
                ·
                  refine ⟨1895275809262619189425253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263517206175079459616835 1895275809262619189425253)
                  ·
                    refine ⟨355364214236741098017235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895275809262619189425253 355364214236741098017235)
                    ·
                      rfl

theorem cell22_1038104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1038104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038104 prefixEnd_1038104 := by exact prefixLift 1038104
  have htrace : WordTrace (prefixWord ++ tailWord_1038104) baseStart_1038104 baseEnd_1038104 := by
    simpa [prefixWord, tailWord_1038104, baseEnd_1038104] using wordTrace_append hprefix tailTrace_1038104
  have hstable : (prefixWord ++ tailWord_1038104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038104).length < 2 ^ (prefixWord ++ tailWord_1038104).sum := by decide
  have hdescent : baseEnd_1038104 < baseStart_1038104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038147 : List Nat := [1, 1, 1, 3, 1, 5, 1, 9]
def baseStart_1038147 : Nat := 118140960795 + 1038147 * 2 ^ 59
def prefixEnd_1038147 : Nat := 4983230072969 + 3 ^ 40 * 1038147 * 2
def baseEnd_1038147 : Nat := 39486548223944813243567

theorem tailTrace_1038147 : CollatzResearch.WordTrace tailWord_1038147 prefixEnd_1038147 39486548223944813243567 := by
  unfold tailWord_1038147
  simp only [CollatzResearch.WordTrace]
  refine ⟨37864331769978195237024695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25242887846652130158016463 37864331769978195237024695)
  ·
    refine ⟨56796497654967292855537043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37864331769978195237024695 56796497654967292855537043)
    ·
      refine ⟨85194746482450939283305565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56796497654967292855537043 85194746482450939283305565)
      ·
        refine ⟨31948029930919102231239587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85194746482450939283305565 31948029930919102231239587)
        ·
          refine ⟨47922044896378653346859381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31948029930919102231239587 47922044896378653346859381)
          ·
            refine ⟨4492691709035498751268067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47922044896378653346859381 4492691709035498751268067)
            ·
              refine ⟨6739037563553248126902101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492691709035498751268067 6739037563553248126902101)
              ·
                refine ⟨39486548223944813243567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6739037563553248126902101 39486548223944813243567)
                ·
                  rfl

theorem cell22_1038147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 9].length) (baseStart_1038147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038147 prefixEnd_1038147 := by exact prefixLift 1038147
  have htrace : WordTrace (prefixWord ++ tailWord_1038147) baseStart_1038147 baseEnd_1038147 := by
    simpa [prefixWord, tailWord_1038147, baseEnd_1038147] using wordTrace_append hprefix tailTrace_1038147
  have hstable : (prefixWord ++ tailWord_1038147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038147).length < 2 ^ (prefixWord ++ tailWord_1038147).sum := by decide
  have hdescent : baseEnd_1038147 < baseStart_1038147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038164 : List Nat := [2, 4, 1, 1, 3, 1, 2, 8]
def baseStart_1038164 : Nat := 118140960795 + 1038164 * 2 ^ 59
def prefixEnd_1038164 : Nat := 4983230072969 + 3 ^ 40 * 1038164 * 2
def baseEnd_1038164 : Nat := 39487194829213437946339

theorem tailTrace_1038164 : CollatzResearch.WordTrace tailWord_1038164 prefixEnd_1038164 39487194829213437946339 := by
  unfold tailWord_1038164
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932475905458303570196773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25243301207277738093595697 18932475905458303570196773)
  ·
    refine ⟨3549839232273431919411895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18932475905458303570196773 3549839232273431919411895)
    ·
      refine ⟨5324758848410147879117843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549839232273431919411895 5324758848410147879117843)
      ·
        refine ⟨7987138272615221818676765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324758848410147879117843 7987138272615221818676765)
        ·
          refine ⟨2995176852230708182003787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7987138272615221818676765 2995176852230708182003787)
          ·
            refine ⟨4492765278346062273005681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995176852230708182003787 4492765278346062273005681)
            ·
              refine ⟨3369573958759546704754261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4492765278346062273005681 3369573958759546704754261)
              ·
                refine ⟨39487194829213437946339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3369573958759546704754261 39487194829213437946339)
                ·
                  rfl

theorem cell22_1038164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_1038164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038164 prefixEnd_1038164 := by exact prefixLift 1038164
  have htrace : WordTrace (prefixWord ++ tailWord_1038164) baseStart_1038164 baseEnd_1038164 := by
    simpa [prefixWord, tailWord_1038164, baseEnd_1038164] using wordTrace_append hprefix tailTrace_1038164
  have hstable : (prefixWord ++ tailWord_1038164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038164).length < 2 ^ (prefixWord ++ tailWord_1038164).sum := by decide
  have hdescent : baseEnd_1038164 < baseStart_1038164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038198 : List Nat := [5, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1038198 : Nat := 118140960795 + 1038198 * 2 ^ 59
def prefixEnd_1038198 : Nat := 4983230072969 + 3 ^ 40 * 1038198 * 2
def baseEnd_1038198 : Nat := 39488488039750687351883

theorem tailTrace_1038198 : CollatzResearch.WordTrace tailWord_1038198 prefixEnd_1038198 39488488039750687351883 := by
  unfold tailWord_1038198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366636993299589434195703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25244127928528953964754165 2366636993299589434195703)
  ·
    refine ⟨3549955489949384151293555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366636993299589434195703 3549955489949384151293555)
    ·
      refine ⟨5324933234924076226940333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549955489949384151293555 5324933234924076226940333)
      ·
        refine ⟨1996849963096528585102625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5324933234924076226940333 1996849963096528585102625)
        ·
          refine ⟨1497637472322396438826969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996849963096528585102625 1497637472322396438826969)
          ·
            refine ⟨1123228104241797329120227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497637472322396438826969 1123228104241797329120227)
            ·
              refine ⟨1684842156362695993680341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123228104241797329120227 1684842156362695993680341)
              ·
                refine ⟨39488488039750687351883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1684842156362695993680341 39488488039750687351883)
                ·
                  rfl

theorem cell22_1038198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1038198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038198 prefixEnd_1038198 := by exact prefixLift 1038198
  have htrace : WordTrace (prefixWord ++ tailWord_1038198) baseStart_1038198 baseEnd_1038198 := by
    simpa [prefixWord, tailWord_1038198, baseEnd_1038198] using wordTrace_append hprefix tailTrace_1038198
  have hstable : (prefixWord ++ tailWord_1038198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038198).length < 2 ^ (prefixWord ++ tailWord_1038198).sum := by decide
  have hdescent : baseEnd_1038198 < baseStart_1038198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038286 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1038286 : Nat := 118140960795 + 1038286 * 2 ^ 59
def prefixEnd_1038286 : Nat := 4983230072969 + 3 ^ 40 * 1038286 * 2
def baseEnd_1038286 : Nat := 355426516556153289966677

theorem tailTrace_1038286 : CollatzResearch.WordTrace tailWord_1038286 prefixEnd_1038286 355426516556153289966677 := by
  unfold tailWord_1038286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733675189559327747041839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25246267677649747984223141 4733675189559327747041839)
  ·
    refine ⟨7100512784338991620562759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4733675189559327747041839 7100512784338991620562759)
    ·
      refine ⟨10650769176508487430844139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7100512784338991620562759 10650769176508487430844139)
      ·
        refine ⟨15976153764762731146266209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650769176508487430844139 15976153764762731146266209)
        ·
          refine ⟨11982115323572048359699657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15976153764762731146266209 11982115323572048359699657)
          ·
            refine ⟨8986586492679036269774743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11982115323572048359699657 8986586492679036269774743)
            ·
              refine ⟨13479879739018554404662115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986586492679036269774743 13479879739018554404662115)
              ·
                refine ⟨20219819608527831606993173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479879739018554404662115 20219819608527831606993173)
                ·
                  refine ⟨947804044149742106577805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20219819608527831606993173 947804044149742106577805)
                  ·
                    refine ⟨355426516556153289966677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947804044149742106577805 355426516556153289966677)
                    ·
                      rfl

theorem cell22_1038286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1038286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038286 prefixEnd_1038286 := by exact prefixLift 1038286
  have htrace : WordTrace (prefixWord ++ tailWord_1038286) baseStart_1038286 baseEnd_1038286 := by
    simpa [prefixWord, tailWord_1038286, baseEnd_1038286] using wordTrace_append hprefix tailTrace_1038286
  have hstable : (prefixWord ++ tailWord_1038286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038286).length < 2 ^ (prefixWord ++ tailWord_1038286).sum := by decide
  have hdescent : baseEnd_1038286 < baseStart_1038286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038331 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 3, 3]
def baseStart_1038331 : Nat := 118140960795 + 1038331 * 2 ^ 59
def prefixEnd_1038331 : Nat := 4983230072969 + 3 ^ 40 * 1038331 * 2
def baseEnd_1038331 : Nat := 355441920975788172591539

theorem tailTrace_1038331 : CollatzResearch.WordTrace tailWord_1038331 prefixEnd_1038331 355441920975788172591539 := by
  unfold tailWord_1038331
  simp only [CollatzResearch.WordTrace]
  refine ⟨37871042801311594661722847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25247361867541063107815231 37871042801311594661722847)
  ·
    refine ⟨56806564201967391992584271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37871042801311594661722847 56806564201967391992584271)
    ·
      refine ⟨85209846302951087988876407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56806564201967391992584271 85209846302951087988876407)
      ·
        refine ⟨127814769454426631983314611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85209846302951087988876407 127814769454426631983314611)
        ·
          refine ⟨191722154181639947974971917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127814769454426631983314611 191722154181639947974971917)
          ·
            refine ⟨71895807818114980490614469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191722154181639947974971917 71895807818114980490614469)
            ·
              refine ⟨13480463965896558841990213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71895807818114980490614469 13480463965896558841990213)
              ·
                refine ⟨2527586993605604782873165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13480463965896558841990213 2527586993605604782873165)
                ·
                  refine ⟨947845122602101793577437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2527586993605604782873165 947845122602101793577437)
                  ·
                    refine ⟨355441920975788172591539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 947845122602101793577437 355441920975788172591539)
                    ·
                      rfl

theorem cell22_1038331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3].length) (baseStart_1038331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038331 prefixEnd_1038331 := by exact prefixLift 1038331
  have htrace : WordTrace (prefixWord ++ tailWord_1038331) baseStart_1038331 baseEnd_1038331 := by
    simpa [prefixWord, tailWord_1038331, baseEnd_1038331] using wordTrace_append hprefix tailTrace_1038331
  have hstable : (prefixWord ++ tailWord_1038331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038331).length < 2 ^ (prefixWord ++ tailWord_1038331).sum := by decide
  have hdescent : baseEnd_1038331 < baseStart_1038331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038356 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1038356 : Nat := 118140960795 + 1038356 * 2 ^ 59
def prefixEnd_1038356 : Nat := 4983230072969 + 3 ^ 40 * 1038356 * 2
def baseEnd_1038356 : Nat := 118483492995565480238821

theorem tailTrace_1038356 : CollatzResearch.WordTrace tailWord_1038356 prefixEnd_1038356 118483492995565480238821 := by
  unfold tailWord_1038356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935977313110511965691461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25247969750814015954255281 18935977313110511965691461)
  ·
    refine ⟨3550495746208220993567149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18935977313110511965691461 3550495746208220993567149)
    ·
      refine ⟨1331435904828082872587681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3550495746208220993567149 1331435904828082872587681)
      ·
        refine ⟨998576928621062154440761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331435904828082872587681 998576928621062154440761)
        ·
          refine ⟨748932696465796615830571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998576928621062154440761 748932696465796615830571)
          ·
            refine ⟨1123399044698694923745857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748932696465796615830571 1123399044698694923745857)
            ·
              refine ⟨842549283524021192809393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123399044698694923745857 842549283524021192809393)
              ·
                refine ⟨631911962643015894607045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842549283524021192809393 631911962643015894607045)
                ·
                  refine ⟨118483492995565480238821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631911962643015894607045 118483492995565480238821)
                  ·
                    rfl

theorem cell22_1038356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1038356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038356 prefixEnd_1038356 := by exact prefixLift 1038356
  have htrace : WordTrace (prefixWord ++ tailWord_1038356) baseStart_1038356 baseEnd_1038356 := by
    simpa [prefixWord, tailWord_1038356, baseEnd_1038356] using wordTrace_append hprefix tailTrace_1038356
  have hstable : (prefixWord ++ tailWord_1038356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038356).length < 2 ^ (prefixWord ++ tailWord_1038356).sum := by decide
  have hdescent : baseEnd_1038356 < baseStart_1038356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038378 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_1038378 : Nat := 118140960795 + 1038378 * 2 ^ 59
def prefixEnd_1038378 : Nat := 4983230072969 + 3 ^ 40 * 1038378 * 2
def baseEnd_1038378 : Nat := 118486003345431905555465

theorem tailTrace_1038378 : CollatzResearch.WordTrace tailWord_1038378 prefixEnd_1038378 118486003345431905555465 := by
  unfold tailWord_1038378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468189258035330422170947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25248504688094214459122525 9468189258035330422170947)
  ·
    refine ⟨14202283887052995633256421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9468189258035330422170947 14202283887052995633256421)
    ·
      refine ⟨2662928228822436681235579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14202283887052995633256421 2662928228822436681235579)
      ·
        refine ⟨3994392343233655021853369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662928228822436681235579 3994392343233655021853369)
        ·
          refine ⟨2995794257425241266390027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3994392343233655021853369 2995794257425241266390027)
          ·
            refine ⟨4493691386137861899585041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995794257425241266390027 4493691386137861899585041)
            ·
              refine ⟨3370268539603396424688781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4493691386137861899585041 3370268539603396424688781)
              ·
                refine ⟨1263850702351273659258293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3370268539603396424688781 1263850702351273659258293)
                ·
                  refine ⟨118486003345431905555465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1263850702351273659258293 118486003345431905555465)
                  ·
                    rfl

theorem cell22_1038378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_1038378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038378 prefixEnd_1038378 := by exact prefixLift 1038378
  have htrace : WordTrace (prefixWord ++ tailWord_1038378) baseStart_1038378 baseEnd_1038378 := by
    simpa [prefixWord, tailWord_1038378, baseEnd_1038378] using wordTrace_append hprefix tailTrace_1038378
  have hstable : (prefixWord ++ tailWord_1038378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038378).length < 2 ^ (prefixWord ++ tailWord_1038378).sum := by decide
  have hdescent : baseEnd_1038378 < baseStart_1038378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038391 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1038391 : Nat := 118140960795 + 1038391 * 2 ^ 59
def prefixEnd_1038391 : Nat := 4983230072969 + 3 ^ 40 * 1038391 * 2
def baseEnd_1038391 : Nat := 355462460201968016091355

theorem tailTrace_1038391 : CollatzResearch.WordTrace tailWord_1038391 prefixEnd_1038391 355462460201968016091355 := by
  unfold tailWord_1038391
  simp only [CollatzResearch.WordTrace]
  refine ⟨37873231181094224908907027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25248820787396149939271351 37873231181094224908907027)
  ·
    refine ⟨56809846771641337363360541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37873231181094224908907027 56809846771641337363360541)
    ·
      refine ⟨21303692539365501511260203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56809846771641337363360541 21303692539365501511260203)
      ·
        refine ⟨31955538809048252266890305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21303692539365501511260203 31955538809048252266890305)
        ·
          refine ⟨23966654106786189200167729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31955538809048252266890305 23966654106786189200167729)
          ·
            refine ⟨17974990580089641900125797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23966654106786189200167729 17974990580089641900125797)
            ·
              refine ⟨3370310733766807856273587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17974990580089641900125797 3370310733766807856273587)
              ·
                refine ⟨5055466100650211784410381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370310733766807856273587 5055466100650211784410381)
                ·
                  refine ⟨1895799787743829419153893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5055466100650211784410381 1895799787743829419153893)
                  ·
                    refine ⟨355462460201968016091355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895799787743829419153893 355462460201968016091355)
                    ·
                      rfl

theorem cell22_1038391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1038391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038391 prefixEnd_1038391 := by exact prefixLift 1038391
  have htrace : WordTrace (prefixWord ++ tailWord_1038391) baseStart_1038391 baseEnd_1038391 := by
    simpa [prefixWord, tailWord_1038391, baseEnd_1038391] using wordTrace_append hprefix tailTrace_1038391
  have hstable : (prefixWord ++ tailWord_1038391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038391).length < 2 ^ (prefixWord ++ tailWord_1038391).sum := by decide
  have hdescent : baseEnd_1038391 < baseStart_1038391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038423 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 4]
def baseStart_1038423 : Nat := 118140960795 + 1038423 * 2 ^ 59
def prefixEnd_1038423 : Nat := 4983230072969 + 3 ^ 40 * 1038423 * 2
def baseEnd_1038423 : Nat := 118491138151976866430419

theorem tailTrace_1038423 : CollatzResearch.WordTrace tailWord_1038423 prefixEnd_1038423 118491138151976866430419 := by
  unfold tailWord_1038423
  simp only [CollatzResearch.WordTrace]
  refine ⟨37874398316978294374071923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25249598877985529582714615 37874398316978294374071923)
  ·
    refine ⟨56811597475467441561107885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37874398316978294374071923 56811597475467441561107885)
    ·
      refine ⟨21304349053300290585415457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56811597475467441561107885 21304349053300290585415457)
      ·
        refine ⟨15978261789975217939061593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21304349053300290585415457 15978261789975217939061593)
        ·
          refine ⟨11983696342481413454296195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15978261789975217939061593 11983696342481413454296195)
          ·
            refine ⟨17975544513722120181444293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983696342481413454296195 17975544513722120181444293)
            ·
              refine ⟨3370414596322897534020805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17975544513722120181444293 3370414596322897534020805)
              ·
                refine ⟨631952736810543287628901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3370414596322897534020805 631952736810543287628901)
                ·
                  refine ⟨118491138151976866430419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631952736810543287628901 118491138151976866430419)
                  ·
                    rfl

theorem cell22_1038423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 4].length) (baseStart_1038423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038423 prefixEnd_1038423 := by exact prefixLift 1038423
  have htrace : WordTrace (prefixWord ++ tailWord_1038423) baseStart_1038423 baseEnd_1038423 := by
    simpa [prefixWord, tailWord_1038423, baseEnd_1038423] using wordTrace_append hprefix tailTrace_1038423
  have hstable : (prefixWord ++ tailWord_1038423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038423).length < 2 ^ (prefixWord ++ tailWord_1038423).sum := by decide
  have hdescent : baseEnd_1038423 < baseStart_1038423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038436 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1038436 : Nat := 118140960795 + 1038436 * 2 ^ 59
def prefixEnd_1038436 : Nat := 4983230072969 + 3 ^ 40 * 1038436 * 2
def baseEnd_1038436 : Nat := 355477864621602898716217

theorem tailTrace_1038436 : CollatzResearch.WordTrace tailWord_1038436 prefixEnd_1038436 355477864621602898716217 := by
  unfold tailWord_1038436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937436232965598797147581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25249914977287465062863441 18937436232965598797147581)
  ·
    refine ⟨7101538587362099548930343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18937436232965598797147581 7101538587362099548930343)
    ·
      refine ⟨10652307881043149323395515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7101538587362099548930343 10652307881043149323395515)
      ·
        refine ⟨15978461821564723985093273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10652307881043149323395515 15978461821564723985093273)
        ·
          refine ⟨11983846366173542988819955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15978461821564723985093273 11983846366173542988819955)
          ·
            refine ⟨17975769549260314483229933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11983846366173542988819955 17975769549260314483229933)
            ·
              refine ⟨6740913580972617931211225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17975769549260314483229933 6740913580972617931211225)
              ·
                refine ⟨5055685185729463448408419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6740913580972617931211225 5055685185729463448408419)
                ·
                  refine ⟨7583527778594195172612629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5055685185729463448408419 7583527778594195172612629)
                  ·
                    refine ⟨355477864621602898716217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7583527778594195172612629 355477864621602898716217)
                    ·
                      rfl

theorem cell22_1038436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1038436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038436 prefixEnd_1038436 := by exact prefixLift 1038436
  have htrace : WordTrace (prefixWord ++ tailWord_1038436) baseStart_1038436 baseEnd_1038436 := by
    simpa [prefixWord, tailWord_1038436, baseEnd_1038436] using wordTrace_append hprefix tailTrace_1038436
  have hstable : (prefixWord ++ tailWord_1038436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038436).length < 2 ^ (prefixWord ++ tailWord_1038436).sum := by decide
  have hdescent : baseEnd_1038436 < baseStart_1038436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038511 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1038511 : Nat := 118140960795 + 1038511 * 2 ^ 59
def prefixEnd_1038511 : Nat := 4983230072969 + 3 ^ 40 * 1038511 * 2
def baseEnd_1038511 : Nat := 355503538654327703090987

theorem tailTrace_1038511 : CollatzResearch.WordTrace tailWord_1038511 prefixEnd_1038511 355503538654327703090987 := by
  unfold tailWord_1038511
  simp only [CollatzResearch.WordTrace]
  refine ⟨37877607940659485403275387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25251738627106323602183591 37877607940659485403275387)
  ·
    refine ⟨56816411910989228104913081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37877607940659485403275387 56816411910989228104913081)
    ·
      refine ⟨42612308933241921078684811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56816411910989228104913081 42612308933241921078684811)
      ·
        refine ⟨63918463399862881618027217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42612308933241921078684811 63918463399862881618027217)
        ·
          refine ⟨47938847549897161213520413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63918463399862881618027217 47938847549897161213520413)
          ·
            refine ⟨17977067831211435455070155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47938847549897161213520413 17977067831211435455070155)
            ·
              refine ⟨26965601746817153182605233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17977067831211435455070155 26965601746817153182605233)
              ·
                refine ⟨20224201310112864886953925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26965601746817153182605233 20224201310112864886953925)
                ·
                  refine ⟨3792037745646162166303861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20224201310112864886953925 3792037745646162166303861)
                  ·
                    refine ⟨355503538654327703090987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3792037745646162166303861 355503538654327703090987)
                    ·
                      rfl

theorem cell22_1038511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1038511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038511 prefixEnd_1038511 := by exact prefixLift 1038511
  have htrace : WordTrace (prefixWord ++ tailWord_1038511) baseStart_1038511 baseEnd_1038511 := by
    simpa [prefixWord, tailWord_1038511, baseEnd_1038511] using wordTrace_append hprefix tailTrace_1038511
  have hstable : (prefixWord ++ tailWord_1038511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038511).length < 2 ^ (prefixWord ++ tailWord_1038511).sum := by decide
  have hdescent : baseEnd_1038511 < baseStart_1038511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038575 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 4]
def baseStart_1038575 : Nat := 118140960795 + 1038575 * 2 ^ 59
def prefixEnd_1038575 : Nat := 4983230072969 + 3 ^ 40 * 1038575 * 2
def baseEnd_1038575 : Nat := 118508482387417623163597

theorem tailTrace_1038575 : CollatzResearch.WordTrace tailWord_1038575 prefixEnd_1038575 118508482387417623163597 := by
  unfold tailWord_1038575
  simp only [CollatzResearch.WordTrace]
  refine ⟨37879942212427624333605179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25253294808285082889070119 37879942212427624333605179)
  ·
    refine ⟨56819913318641436500407769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37879942212427624333605179 56819913318641436500407769)
    ·
      refine ⟨42614934988981077375305827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56819913318641436500407769 42614934988981077375305827)
      ·
        refine ⟨63922402483471616062958741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42614934988981077375305827 63922402483471616062958741)
        ·
          refine ⟨2996362616412732002951191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63922402483471616062958741 2996362616412732002951191)
          ·
            refine ⟨4494543924619098004426787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996362616412732002951191 4494543924619098004426787)
            ·
              refine ⟨6741815886928647006640181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494543924619098004426787 6741815886928647006640181)
              ·
                refine ⟨632045239399560656872517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6741815886928647006640181 632045239399560656872517)
                ·
                  refine ⟨118508482387417623163597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632045239399560656872517 118508482387417623163597)
                  ·
                    rfl

theorem cell22_1038575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 4].length) (baseStart_1038575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038575 prefixEnd_1038575 := by exact prefixLift 1038575
  have htrace : WordTrace (prefixWord ++ tailWord_1038575) baseStart_1038575 baseEnd_1038575 := by
    simpa [prefixWord, tailWord_1038575, baseEnd_1038575] using wordTrace_append hprefix tailTrace_1038575
  have hstable : (prefixWord ++ tailWord_1038575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038575).length < 2 ^ (prefixWord ++ tailWord_1038575).sum := by decide
  have hdescent : baseEnd_1038575 < baseStart_1038575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038622 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1038622 : Nat := 118140960795 + 1038622 * 2 ^ 59
def prefixEnd_1038622 : Nat := 4983230072969 + 3 ^ 40 * 1038622 * 2
def baseEnd_1038622 : Nat := 355541536222760413565647

theorem tailTrace_1038622 : CollatzResearch.WordTrace tailWord_1038622 prefixEnd_1038622 355541536222760413565647 := by
  unfold tailWord_1038622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735207055407168920070765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25254437628838234240377413 4735207055407168920070765)
  ·
    refine ⟨1775702645777688345026537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4735207055407168920070765 1775702645777688345026537)
    ·
      refine ⟨1331776984333266258769903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775702645777688345026537 1331776984333266258769903)
      ·
        refine ⟨1997665476499899388154855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331776984333266258769903 1997665476499899388154855)
        ·
          refine ⟨2996498214749849082232283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997665476499899388154855 2996498214749849082232283)
          ·
            refine ⟨4494747322124773623348425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996498214749849082232283 4494747322124773623348425)
            ·
              refine ⟨3371060491593580217511319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494747322124773623348425 3371060491593580217511319)
              ·
                refine ⟨5056590737390370326266979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371060491593580217511319 5056590737390370326266979)
                ·
                  refine ⟨7584886106085555489400469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5056590737390370326266979 7584886106085555489400469)
                  ·
                    refine ⟨355541536222760413565647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7584886106085555489400469 355541536222760413565647)
                    ·
                      rfl

theorem cell22_1038622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1038622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038622 prefixEnd_1038622 := by exact prefixLift 1038622
  have htrace : WordTrace (prefixWord ++ tailWord_1038622) baseStart_1038622 baseEnd_1038622 := by
    simpa [prefixWord, tailWord_1038622, baseEnd_1038622] using wordTrace_append hprefix tailTrace_1038622
  have hstable : (prefixWord ++ tailWord_1038622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038622).length < 2 ^ (prefixWord ++ tailWord_1038622).sum := by decide
  have hdescent : baseEnd_1038622 < baseStart_1038622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038637 : List Nat := [1, 5, 3, 1, 2, 2, 8]
def baseStart_1038637 : Nat := 118140960795 + 1038637 * 2 ^ 59
def prefixEnd_1038637 : Nat := 4983230072969 + 3 ^ 40 * 1038637 * 2
def baseEnd_1038637 : Nat := 13168395223307606460763

theorem tailTrace_1038637 : CollatzResearch.WordTrace tailWord_1038637 prefixEnd_1038637 13168395223307606460763 := by
  unfold tailWord_1038637
  simp only [CollatzResearch.WordTrace]
  refine ⟨37882203538203008922362165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25254802358802005948241443 37882203538203008922362165)
  ·
    refine ⟨3551456581706532086471453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37882203538203008922362165 3551456581706532086471453)
    ·
      refine ⟨1331796218139949532426795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3551456581706532086471453 1331796218139949532426795)
      ·
        refine ⟨1997694327209924298640193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331796218139949532426795 1997694327209924298640193)
        ·
          refine ⟨1498270745407443223980145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1997694327209924298640193 1498270745407443223980145)
          ·
            refine ⟨1123703059055582417985109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498270745407443223980145 1123703059055582417985109)
            ·
              refine ⟨13168395223307606460763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1123703059055582417985109 13168395223307606460763)
              ·
                rfl

theorem cell22_1038637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 8].length) (baseStart_1038637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038637 prefixEnd_1038637 := by exact prefixLift 1038637
  have htrace : WordTrace (prefixWord ++ tailWord_1038637) baseStart_1038637 baseEnd_1038637 := by
    simpa [prefixWord, tailWord_1038637, baseEnd_1038637] using wordTrace_append hprefix tailTrace_1038637
  have hstable : (prefixWord ++ tailWord_1038637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038637).length < 2 ^ (prefixWord ++ tailWord_1038637).sum := by decide
  have hdescent : baseEnd_1038637 < baseStart_1038637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038648 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_1038648 : Nat := 118140960795 + 1038648 * 2 ^ 59
def prefixEnd_1038648 : Nat := 4983230072969 + 3 ^ 40 * 1038648 * 2
def baseEnd_1038648 : Nat := 118516812184701670805189

theorem tailTrace_1038648 : CollatzResearch.WordTrace tailWord_1038648 prefixEnd_1038648 118516812184701670805189 := by
  unfold tailWord_1038648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18941302370581578900506299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25255069827442105200675065 18941302370581578900506299)
  ·
    refine ⟨28411953555872368350759449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18941302370581578900506299 28411953555872368350759449)
    ·
      refine ⟨21308965166904276263069587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28411953555872368350759449 21308965166904276263069587)
      ·
        refine ⟨31963447750356414394604381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308965166904276263069587 31963447750356414394604381)
        ·
          refine ⟨11986292906383655397976643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31963447750356414394604381 11986292906383655397976643)
          ·
            refine ⟨17979439359575483096964965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11986292906383655397976643 17979439359575483096964965)
            ·
              refine ⟨3371144879920403080680931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17979439359575483096964965 3371144879920403080680931)
              ·
                refine ⟨5056717319880604621021397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3371144879920403080680931 5056717319880604621021397)
                ·
                  refine ⟨118516812184701670805189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5056717319880604621021397 118516812184701670805189)
                  ·
                    rfl

theorem cell22_1038648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_1038648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038648 prefixEnd_1038648 := by exact prefixLift 1038648
  have htrace : WordTrace (prefixWord ++ tailWord_1038648) baseStart_1038648 baseEnd_1038648 := by
    simpa [prefixWord, tailWord_1038648, baseEnd_1038648] using wordTrace_append hprefix tailTrace_1038648
  have hstable : (prefixWord ++ tailWord_1038648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038648).length < 2 ^ (prefixWord ++ tailWord_1038648).sum := by decide
  have hdescent : baseEnd_1038648 < baseStart_1038648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038663 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1038663 : Nat := 118140960795 + 1038663 * 2 ^ 59
def prefixEnd_1038663 : Nat := 4983230072969 + 3 ^ 40 * 1038663 * 2
def baseEnd_1038663 : Nat := 355555571360649973290521

theorem tailTrace_1038663 : CollatzResearch.WordTrace tailWord_1038663 prefixEnd_1038663 355555571360649973290521 := by
  unfold tailWord_1038663
  simp only [CollatzResearch.WordTrace]
  refine ⟨37883151836108815362808643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25255434557405876908539095 37883151836108815362808643)
  ·
    refine ⟨56824727754163223044212965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37883151836108815362808643 56824727754163223044212965)
    ·
      refine ⟨10654636453905604320789931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56824727754163223044212965 10654636453905604320789931)
      ·
        refine ⟨15981954680858406481184897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654636453905604320789931 15981954680858406481184897)
        ·
          refine ⟨11986466010643804860888673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15981954680858406481184897 11986466010643804860888673)
          ·
            refine ⟨8989849507982853645666505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11986466010643804860888673 8989849507982853645666505)
            ·
              refine ⟨6742387130987140234249879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8989849507982853645666505 6742387130987140234249879)
              ·
                refine ⟨10113580696480710351374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6742387130987140234249879 10113580696480710351374819)
                ·
                  refine ⟨15170371044721065527062229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10113580696480710351374819 15170371044721065527062229)
                  ·
                    refine ⟨355555571360649973290521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15170371044721065527062229 355555571360649973290521)
                    ·
                      rfl

theorem cell22_1038663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1038663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038663 prefixEnd_1038663 := by exact prefixLift 1038663
  have htrace : WordTrace (prefixWord ++ tailWord_1038663) baseStart_1038663 baseEnd_1038663 := by
    simpa [prefixWord, tailWord_1038663, baseEnd_1038663] using wordTrace_append hprefix tailTrace_1038663
  have hstable : (prefixWord ++ tailWord_1038663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038663).length < 2 ^ (prefixWord ++ tailWord_1038663).sum := by decide
  have hdescent : baseEnd_1038663 < baseStart_1038663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038725 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_1038725 : Nat := 118140960795 + 1038725 * 2 ^ 59
def prefixEnd_1038725 : Nat := 4983230072969 + 3 ^ 40 * 1038725 * 2
def baseEnd_1038725 : Nat := 355576795227702478240331

theorem tailTrace_1038725 : CollatzResearch.WordTrace tailWord_1038725 prefixEnd_1038725 355576795227702478240331 := by
  unfold tailWord_1038725
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885413161884199951565629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25256942107922799967710419 37885413161884199951565629)
  ·
    refine ⟨14207029935706574981837111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37885413161884199951565629 14207029935706574981837111)
    ·
      refine ⟨21310544903559862472755667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14207029935706574981837111 21310544903559862472755667)
      ·
        refine ⟨31965817355339793709133501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21310544903559862472755667 31965817355339793709133501)
        ·
          refine ⟨11987181508252422640925063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31965817355339793709133501 11987181508252422640925063)
          ·
            refine ⟨17980772262378633961387595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11987181508252422640925063 17980772262378633961387595)
            ·
              refine ⟨26971158393567950942081393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17980772262378633961387595 26971158393567950942081393)
              ·
                refine ⟨20228368795175963206561045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26971158393567950942081393 20228368795175963206561045)
                ·
                  refine ⟨948204787273873275307549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20228368795175963206561045 948204787273873275307549)
                  ·
                    refine ⟨355576795227702478240331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948204787273873275307549 355576795227702478240331)
                    ·
                      rfl

theorem cell22_1038725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_1038725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038725 prefixEnd_1038725 := by exact prefixLift 1038725
  have htrace : WordTrace (prefixWord ++ tailWord_1038725) baseStart_1038725 baseEnd_1038725 := by
    simpa [prefixWord, tailWord_1038725, baseEnd_1038725] using wordTrace_append hprefix tailTrace_1038725
  have hstable : (prefixWord ++ tailWord_1038725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038725).length < 2 ^ (prefixWord ++ tailWord_1038725).sum := by decide
  have hdescent : baseEnd_1038725 < baseStart_1038725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038744 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_1038744 : Nat := 118140960795 + 1038744 * 2 ^ 59
def prefixEnd_1038744 : Nat := 4983230072969 + 3 ^ 40 * 1038744 * 2
def baseEnd_1038744 : Nat := 118527766438664254005091

theorem tailTrace_1038744 : CollatzResearch.WordTrace tailWord_1038744 prefixEnd_1038744 118527766438664254005091 := by
  unfold tailWord_1038744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943053074407683098253643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25257404099210244131004857 18943053074407683098253643)
  ·
    refine ⟨28414579611611524647380465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18943053074407683098253643 28414579611611524647380465)
    ·
      refine ⟨21310934708708643485535349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28414579611611524647380465 21310934708708643485535349)
      ·
        refine ⟨1997900128941435326768939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21310934708708643485535349 1997900128941435326768939)
        ·
          refine ⟨2996850193412152990153409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997900128941435326768939 2996850193412152990153409)
          ·
            refine ⟨2247637645059114742615057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996850193412152990153409 2247637645059114742615057)
            ·
              refine ⟨1685728233794336056961293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247637645059114742615057 1685728233794336056961293)
              ·
                refine ⟨632148087672876021360485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1685728233794336056961293 632148087672876021360485)
                ·
                  refine ⟨118527766438664254005091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632148087672876021360485 118527766438664254005091)
                  ·
                    rfl

theorem cell22_1038744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_1038744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038744 prefixEnd_1038744 := by exact prefixLift 1038744
  have htrace : WordTrace (prefixWord ++ tailWord_1038744) baseStart_1038744 baseEnd_1038744 := by
    simpa [prefixWord, tailWord_1038744, baseEnd_1038744] using wordTrace_append hprefix tailTrace_1038744
  have hstable : (prefixWord ++ tailWord_1038744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038744).length < 2 ^ (prefixWord ++ tailWord_1038744).sum := by decide
  have hdescent : baseEnd_1038744 < baseStart_1038744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038759 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1038759 : Nat := 118140960795 + 1038759 * 2 ^ 59
def prefixEnd_1038759 : Nat := 4983230072969 + 3 ^ 40 * 1038759 * 2
def baseEnd_1038759 : Nat := 355588434122537722890227

theorem tailTrace_1038759 : CollatzResearch.WordTrace tailWord_1038759 prefixEnd_1038759 355588434122537722890227 := by
  unfold tailWord_1038759
  simp only [CollatzResearch.WordTrace]
  refine ⟨37886653243761023758303331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25257768829174015838868887 37886653243761023758303331)
  ·
    refine ⟨56829979865641535637454997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37886653243761023758303331 56829979865641535637454997)
    ·
      refine ⟨2663905306201946983005703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56829979865641535637454997 2663905306201946983005703)
      ·
        refine ⟨3995857959302920474508555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663905306201946983005703 3995857959302920474508555)
        ·
          refine ⟨5993786938954380711762833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995857959302920474508555 5993786938954380711762833)
          ·
            refine ⟨4495340204215785533822125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5993786938954380711762833 4495340204215785533822125)
            ·
              refine ⟨1685752576580919575183297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4495340204215785533822125 1685752576580919575183297)
              ·
                refine ⟨1264314432435689681387473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685752576580919575183297 1264314432435689681387473)
                ·
                  refine ⟨948235824326767261040605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1264314432435689681387473 948235824326767261040605)
                  ·
                    refine ⟨355588434122537722890227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948235824326767261040605 355588434122537722890227)
                    ·
                      rfl

theorem cell22_1038759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1038759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038759 prefixEnd_1038759 := by exact prefixLift 1038759
  have htrace : WordTrace (prefixWord ++ tailWord_1038759) baseStart_1038759 baseEnd_1038759 := by
    simpa [prefixWord, tailWord_1038759, baseEnd_1038759] using wordTrace_append hprefix tailTrace_1038759
  have hstable : (prefixWord ++ tailWord_1038759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038759).length < 2 ^ (prefixWord ++ tailWord_1038759).sum := by decide
  have hdescent : baseEnd_1038759 < baseStart_1038759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038821 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_1038821 : Nat := 118140960795 + 1038821 * 2 ^ 59
def prefixEnd_1038821 : Nat := 4983230072969 + 3 ^ 40 * 1038821 * 2
def baseEnd_1038821 : Nat := 355609657989590227840037

theorem tailTrace_1038821 : CollatzResearch.WordTrace tailWord_1038821 prefixEnd_1038821 355609657989590227840037 := by
  unfold tailWord_1038821
  simp only [CollatzResearch.WordTrace]
  refine ⟨37888914569536408347060317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25259276379690938898040211 37888914569536408347060317)
  ·
    refine ⟨14208342963576153130147619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37888914569536408347060317 14208342963576153130147619)
    ·
      refine ⟨21312514445364229695221429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14208342963576153130147619 21312514445364229695221429)
      ·
        refine ⟨1998048229252896533927009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21312514445364229695221429 1998048229252896533927009)
        ·
          refine ⟨1498536171939672400445257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998048229252896533927009 1498536171939672400445257)
          ·
            refine ⟨1123902128954754300333943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498536171939672400445257 1123902128954754300333943)
            ·
              refine ⟨1685853193432131450500915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123902128954754300333943 1685853193432131450500915)
              ·
                refine ⟨2528779790148197175751373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685853193432131450500915 2528779790148197175751373)
                ·
                  refine ⟨948292421305573940906765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2528779790148197175751373 948292421305573940906765)
                  ·
                    refine ⟨355609657989590227840037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948292421305573940906765 355609657989590227840037)
                    ·
                      rfl

theorem cell22_1038821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_1038821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038821 prefixEnd_1038821 := by exact prefixLift 1038821
  have htrace : WordTrace (prefixWord ++ tailWord_1038821) baseStart_1038821 baseEnd_1038821 := by
    simpa [prefixWord, tailWord_1038821, baseEnd_1038821] using wordTrace_append hprefix tailTrace_1038821
  have hstable : (prefixWord ++ tailWord_1038821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038821).length < 2 ^ (prefixWord ++ tailWord_1038821).sum := by decide
  have hdescent : baseEnd_1038821 < baseStart_1038821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038834 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_1038834 : Nat := 118140960795 + 1038834 * 2 ^ 59
def prefixEnd_1038834 : Nat := 4983230072969 + 3 ^ 40 * 1038834 * 2
def baseEnd_1038834 : Nat := 118538036051754175754999

theorem tailTrace_1038834 : CollatzResearch.WordTrace tailWord_1038834 prefixEnd_1038834 118538036051754175754999 := by
  unfold tailWord_1038834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472347179622327891820889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25259592478992874378189037 9472347179622327891820889)
  ·
    refine ⟨7104260384716745918865667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9472347179622327891820889 7104260384716745918865667)
    ·
      refine ⟨10656390577075118878298501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104260384716745918865667 10656390577075118878298501)
      ·
        refine ⟨1998073233201584789680969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10656390577075118878298501 1998073233201584789680969)
        ·
          refine ⟨1498554924901188592260727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998073233201584789680969 1498554924901188592260727)
          ·
            refine ⟨2247832387351782888391091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498554924901188592260727 2247832387351782888391091)
            ·
              refine ⟨3371748581027674332586637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247832387351782888391091 3371748581027674332586637)
              ·
                refine ⟨1264405717885377874719989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3371748581027674332586637 1264405717885377874719989)
                ·
                  refine ⟨118538036051754175754999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1264405717885377874719989 118538036051754175754999)
                  ·
                    rfl

theorem cell22_1038834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_1038834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038834 prefixEnd_1038834 := by exact prefixLift 1038834
  have htrace : WordTrace (prefixWord ++ tailWord_1038834) baseStart_1038834 baseEnd_1038834 := by
    simpa [prefixWord, tailWord_1038834, baseEnd_1038834] using wordTrace_append hprefix tailTrace_1038834
  have hstable : (prefixWord ++ tailWord_1038834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038834).length < 2 ^ (prefixWord ++ tailWord_1038834).sum := by decide
  have hdescent : baseEnd_1038834 < baseStart_1038834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038845 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 8]
def baseStart_1038845 : Nat := 118140960795 + 1038845 * 2 ^ 59
def prefixEnd_1038845 : Nat := 4983230072969 + 3 ^ 40 * 1038845 * 2
def baseEnd_1038845 : Nat := 118539291226687388413321

theorem tailTrace_1038845 : CollatzResearch.WordTrace tailWord_1038845 prefixEnd_1038845 118539291226687388413321 := by
  unfold tailWord_1038845
  simp only [CollatzResearch.WordTrace]
  refine ⟨37889789921449460445933989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25259859947632973630622659 37889789921449460445933989)
  ·
    refine ⟨7104335610271773833612623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37889789921449460445933989 7104335610271773833612623)
    ·
      refine ⟨10656503415407660750418935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104335610271773833612623 10656503415407660750418935)
      ·
        refine ⟨15984755123111491125628403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10656503415407660750418935 15984755123111491125628403)
        ·
          refine ⟨23977132684667236688442605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15984755123111491125628403 23977132684667236688442605)
          ·
            refine ⟨8991424756750213758165977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23977132684667236688442605 8991424756750213758165977)
            ·
              refine ⟨6743568567562660318624483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8991424756750213758165977 6743568567562660318624483)
              ·
                refine ⟨10115352851343990477936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6743568567562660318624483 10115352851343990477936725)
                ·
                  refine ⟨118539291226687388413321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10115352851343990477936725 118539291226687388413321)
                  ·
                    rfl

theorem cell22_1038845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_1038845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038845 prefixEnd_1038845 := by exact prefixLift 1038845
  have htrace : WordTrace (prefixWord ++ tailWord_1038845) baseStart_1038845 baseEnd_1038845 := by
    simpa [prefixWord, tailWord_1038845, baseEnd_1038845] using wordTrace_append hprefix tailTrace_1038845
  have hstable : (prefixWord ++ tailWord_1038845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038845).length < 2 ^ (prefixWord ++ tailWord_1038845).sum := by decide
  have hdescent : baseEnd_1038845 < baseStart_1038845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038909 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1038909 : Nat := 118140960795 + 1038909 * 2 ^ 59
def prefixEnd_1038909 : Nat := 4983230072969 + 3 ^ 40 * 1038909 * 2
def baseEnd_1038909 : Nat := 355639782187987331639767

theorem tailTrace_1038909 : CollatzResearch.WordTrace tailWord_1038909 prefixEnd_1038909 355639782187987331639767 := by
  unfold tailWord_1038909
  simp only [CollatzResearch.WordTrace]
  refine ⟨37892124193217599376263781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25261416128811732917509187 37892124193217599376263781)
  ·
    refine ⟨7104773286228299883049459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37892124193217599376263781 7104773286228299883049459)
    ·
      refine ⟨10657159929342449824574189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104773286228299883049459 10657159929342449824574189)
      ·
        refine ⟨3996434973503418684215321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10657159929342449824574189 3996434973503418684215321)
        ·
          refine ⟨2997326230127564013161491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3996434973503418684215321 2997326230127564013161491)
          ·
            refine ⟨4495989345191346019742237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997326230127564013161491 4495989345191346019742237)
            ·
              refine ⟨1685996004446754757403339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4495989345191346019742237 1685996004446754757403339)
              ·
                refine ⟨2528994006670132136105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685996004446754757403339 2528994006670132136105009)
                ·
                  refine ⟨1896745505002599102078757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528994006670132136105009 1896745505002599102078757)
                  ·
                    refine ⟨355639782187987331639767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1896745505002599102078757 355639782187987331639767)
                    ·
                      rfl

theorem cell22_1038909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1038909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1038909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1038909 prefixEnd_1038909 := by exact prefixLift 1038909
  have htrace : WordTrace (prefixWord ++ tailWord_1038909) baseStart_1038909 baseEnd_1038909 := by
    simpa [prefixWord, tailWord_1038909, baseEnd_1038909] using wordTrace_append hprefix tailTrace_1038909
  have hstable : (prefixWord ++ tailWord_1038909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038909).length < 2 ^ (prefixWord ++ tailWord_1038909).sum := by decide
  have hdescent : baseEnd_1038909 < baseStart_1038909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039029 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1039029 : Nat := 118140960795 + 1039029 * 2 ^ 59
def prefixEnd_1039029 : Nat := 4983230072969 + 3 ^ 40 * 1039029 * 2
def baseEnd_1039029 : Nat := 355680860640347018639399

theorem tailTrace_1039029 : CollatzResearch.WordTrace tailWord_1039029 prefixEnd_1039029 355680860640347018639399 := by
  unfold tailWord_1039029
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896500952782859870632141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25264333968521906580421427 37896500952782859870632141)
  ·
    refine ⟨14211187857293572451487053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37896500952782859870632141 14211187857293572451487053)
    ·
      refine ⟨5329195446485089669307645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14211187857293572451487053 5329195446485089669307645)
      ·
        refine ⟨1998448292431908625990367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5329195446485089669307645 1998448292431908625990367)
        ·
          refine ⟨2997672438647862938985551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998448292431908625990367 2997672438647862938985551)
          ·
            refine ⟨4496508657971794408478327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997672438647862938985551 4496508657971794408478327)
            ·
              refine ⟨6744762986957691612717491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4496508657971794408478327 6744762986957691612717491)
              ·
                refine ⟨10117144480436537419076237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6744762986957691612717491 10117144480436537419076237)
                ·
                  refine ⟨3793929180163701532153589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10117144480436537419076237 3793929180163701532153589)
                  ·
                    refine ⟨355680860640347018639399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3793929180163701532153589 355680860640347018639399)
                    ·
                      rfl

theorem cell22_1039029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1039029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039029 prefixEnd_1039029 := by exact prefixLift 1039029
  have htrace : WordTrace (prefixWord ++ tailWord_1039029) baseStart_1039029 baseEnd_1039029 := by
    simpa [prefixWord, tailWord_1039029, baseEnd_1039029] using wordTrace_append hprefix tailTrace_1039029
  have hstable : (prefixWord ++ tailWord_1039029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039029).length < 2 ^ (prefixWord ++ tailWord_1039029).sum := by decide
  have hdescent : baseEnd_1039029 < baseStart_1039029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039048 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_1039048 : Nat := 118140960795 + 1039048 * 2 ^ 59
def prefixEnd_1039048 : Nat := 4983230072969 + 3 ^ 40 * 1039048 * 2
def baseEnd_1039048 : Nat := 118562454909545767471447

theorem tailTrace_1039048 : CollatzResearch.WordTrace tailWord_1039048 prefixEnd_1039048 118562454909545767471447 := by
  unfold tailWord_1039048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18948596969857013057786899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25264795959809350743715865 18948596969857013057786899)
  ·
    refine ⟨28422895454785519586680349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18948596969857013057786899 28422895454785519586680349)
    ·
      refine ⟨10658585795544569845005131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28422895454785519586680349 10658585795544569845005131)
      ·
        refine ⟨15987878693316854767507697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658585795544569845005131 15987878693316854767507697)
        ·
          refine ⟨11990909019987641075630773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15987878693316854767507697 11990909019987641075630773)
          ·
            refine ⟨1124147720623841350840385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11990909019987641075630773 1124147720623841350840385)
            ·
              refine ⟨843110790467881013130289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124147720623841350840385 843110790467881013130289)
              ·
                refine ⟨632333092850910759847717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843110790467881013130289 632333092850910759847717)
                ·
                  refine ⟨118562454909545767471447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632333092850910759847717 118562454909545767471447)
                  ·
                    rfl

theorem cell22_1039048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_1039048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039048 prefixEnd_1039048 := by exact prefixLift 1039048
  have htrace : WordTrace (prefixWord ++ tailWord_1039048) baseStart_1039048 baseEnd_1039048 := by
    simpa [prefixWord, tailWord_1039048, baseEnd_1039048] using wordTrace_append hprefix tailTrace_1039048
  have hstable : (prefixWord ++ tailWord_1039048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039048).length < 2 ^ (prefixWord ++ tailWord_1039048).sum := by decide
  have hdescent : baseEnd_1039048 < baseStart_1039048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039072 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_1039072 : Nat := 118140960795 + 1039072 * 2 ^ 59
def prefixEnd_1039072 : Nat := 4983230072969 + 3 ^ 40 * 1039072 * 2
def baseEnd_1039072 : Nat := 355695580419109239814267

theorem tailTrace_1039072 : CollatzResearch.WordTrace tailWord_1039072 prefixEnd_1039072 355695580419109239814267 := by
  unfold tailWord_1039072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949034645813539107223735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25265379527751385476298313 18949034645813539107223735)
  ·
    refine ⟨28423551968720308660835603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18949034645813539107223735 28423551968720308660835603)
    ·
      refine ⟨42635327953080462991253405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28423551968720308660835603 42635327953080462991253405)
      ·
        refine ⟨15988247982405173621720027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42635327953080462991253405 15988247982405173621720027)
        ·
          refine ⟨23982371973607760432580041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15988247982405173621720027 23982371973607760432580041)
          ·
            refine ⟨17986778980205820324435031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23982371973607760432580041 17986778980205820324435031)
            ·
              refine ⟨26980168470308730486652547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17986778980205820324435031 26980168470308730486652547)
              ·
                refine ⟨40470252705463095729978821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26980168470308730486652547 40470252705463095729978821)
                ·
                  refine ⟨7588172382274330449371029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40470252705463095729978821 7588172382274330449371029)
                  ·
                    refine ⟨355695580419109239814267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7588172382274330449371029 355695580419109239814267)
                    ·
                      rfl

theorem cell22_1039072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_1039072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039072 prefixEnd_1039072 := by exact prefixLift 1039072
  have htrace : WordTrace (prefixWord ++ tailWord_1039072) baseStart_1039072 baseEnd_1039072 := by
    simpa [prefixWord, tailWord_1039072, baseEnd_1039072] using wordTrace_append hprefix tailTrace_1039072
  have hstable : (prefixWord ++ tailWord_1039072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039072).length < 2 ^ (prefixWord ++ tailWord_1039072).sum := by decide
  have hdescent : baseEnd_1039072 < baseStart_1039072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039093 : List Nat := [1, 3, 6, 1, 1, 1, 9]
def baseStart_1039093 : Nat := 118140960795 + 1039093 * 2 ^ 59
def prefixEnd_1039093 : Nat := 4983230072969 + 3 ^ 40 * 1039093 * 2
def baseEnd_1039093 : Nat := 13174176635121192038489

theorem tailTrace_1039093 : CollatzResearch.WordTrace tailWord_1039093 prefixEnd_1039093 13174176635121192038489 := by
  unfold tailWord_1039093
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898835224550998800961933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25265890149700665867307955 37898835224550998800961933)
  ·
    refine ⟨14212063209206624550360725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37898835224550998800961933 14212063209206624550360725)
    ·
      refine ⟨666190462931560525798159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14212063209206624550360725 666190462931560525798159)
      ·
        refine ⟨999285694397340788697239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666190462931560525798159 999285694397340788697239)
        ·
          refine ⟨1498928541596011183045859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999285694397340788697239 1498928541596011183045859)
          ·
            refine ⟨2248392812394016774568789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498928541596011183045859 2248392812394016774568789)
            ·
              refine ⟨13174176635121192038489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2248392812394016774568789 13174176635121192038489)
              ·
                rfl

theorem cell22_1039093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 9].length) (baseStart_1039093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039093 prefixEnd_1039093 := by exact prefixLift 1039093
  have htrace : WordTrace (prefixWord ++ tailWord_1039093) baseStart_1039093 baseEnd_1039093 := by
    simpa [prefixWord, tailWord_1039093, baseEnd_1039093] using wordTrace_append hprefix tailTrace_1039093
  have hstable : (prefixWord ++ tailWord_1039093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039093).length < 2 ^ (prefixWord ++ tailWord_1039093).sum := by decide
  have hdescent : baseEnd_1039093 < baseStart_1039093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039108 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1039108 : Nat := 118140960795 + 1039108 * 2 ^ 59
def prefixEnd_1039108 : Nat := 4983230072969 + 3 ^ 40 * 1039108 * 2
def baseEnd_1039108 : Nat := 355707903954817145914157

theorem tailTrace_1039108 : CollatzResearch.WordTrace tailWord_1039108 prefixEnd_1039108 355707903954817145914157 := by
  unfold tailWord_1039108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18949691159748328181378989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25266254879664437575171985 18949691159748328181378989)
  ·
    refine ⟨7106134184905623068017121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18949691159748328181378989 7106134184905623068017121)
    ·
      refine ⟨5329600638679217301012841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7106134184905623068017121 5329600638679217301012841)
      ·
        refine ⟨3997200479009412975759631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329600638679217301012841 3997200479009412975759631)
        ·
          refine ⟨5995800718514119463639447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997200479009412975759631 5995800718514119463639447)
          ·
            refine ⟨8993701077771179195459171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995800718514119463639447 8993701077771179195459171)
            ·
              refine ⟨13490551616656768793188757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993701077771179195459171 13490551616656768793188757)
              ·
                refine ⟨632369607030786037180723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13490551616656768793188757 632369607030786037180723)
                ·
                  refine ⟨948554410546179055771085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632369607030786037180723 948554410546179055771085)
                  ·
                    refine ⟨355707903954817145914157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 948554410546179055771085 355707903954817145914157)
                    ·
                      rfl

theorem cell22_1039108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1039108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039108 prefixEnd_1039108 := by exact prefixLift 1039108
  have htrace : WordTrace (prefixWord ++ tailWord_1039108) baseStart_1039108 baseEnd_1039108 := by
    simpa [prefixWord, tailWord_1039108, baseEnd_1039108] using wordTrace_append hprefix tailTrace_1039108
  have hstable : (prefixWord ++ tailWord_1039108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039108).length < 2 ^ (prefixWord ++ tailWord_1039108).sum := by decide
  have hdescent : baseEnd_1039108 < baseStart_1039108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039172 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1039172 : Nat := 118140960795 + 1039172 * 2 ^ 59
def prefixEnd_1039172 : Nat := 4983230072969 + 3 ^ 40 * 1039172 * 2
def baseEnd_1039172 : Nat := 118576604154247437437987

theorem tailTrace_1039172 : CollatzResearch.WordTrace tailWord_1039172 prefixEnd_1039172 118576604154247437437987 := by
  unfold tailWord_1039172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950858295632397646543885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25267811060843196862058513 18950858295632397646543885)
  ·
    refine ⟨7106571860862149117453957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18950858295632397646543885 7106571860862149117453957)
    ·
      refine ⟨1332482223911652959522617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7106571860862149117453957 1332482223911652959522617)
      ·
        refine ⟨999361667933739719641963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1332482223911652959522617 999361667933739719641963)
        ·
          refine ⟨1499042501900609579462945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999361667933739719641963 1499042501900609579462945)
          ·
            refine ⟨1124281876425457184597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499042501900609579462945 1124281876425457184597209)
            ·
              refine ⟨843211407319092888447907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124281876425457184597209 843211407319092888447907)
              ·
                refine ⟨1264817110978639332671861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843211407319092888447907 1264817110978639332671861)
                ·
                  refine ⟨118576604154247437437987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1264817110978639332671861 118576604154247437437987)
                  ·
                    rfl

theorem cell22_1039172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1039172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039172 prefixEnd_1039172 := by exact prefixLift 1039172
  have htrace : WordTrace (prefixWord ++ tailWord_1039172) baseStart_1039172 baseEnd_1039172 := by
    simpa [prefixWord, tailWord_1039172, baseEnd_1039172] using wordTrace_append hprefix tailTrace_1039172
  have hstable : (prefixWord ++ tailWord_1039172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039172).length < 2 ^ (prefixWord ++ tailWord_1039172).sum := by decide
  have hdescent : baseEnd_1039172 < baseStart_1039172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039185 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_1039185 : Nat := 118140960795 + 1039185 * 2 ^ 59
def prefixEnd_1039185 : Nat := 4983230072969 + 3 ^ 40 * 1039185 * 2
def baseEnd_1039185 : Nat := 355734262628414611738921

theorem tailTrace_1039185 : CollatzResearch.WordTrace tailWord_1039185 prefixEnd_1039185 355734262628414611738921 := by
  unfold tailWord_1039185
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902190740217698513311009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25268127160145132342207339 37902190740217698513311009)
  ·
    refine ⟨28426643055163273884983257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37902190740217698513311009 28426643055163273884983257)
    ·
      refine ⟨21319982291372455413737443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28426643055163273884983257 21319982291372455413737443)
      ·
        refine ⟨31979973437058683120606165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21319982291372455413737443 31979973437058683120606165)
        ·
          refine ⟨749530627431062885639207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31979973437058683120606165 749530627431062885639207)
          ·
            refine ⟨1124295941146594328458811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749530627431062885639207 1124295941146594328458811)
            ·
              refine ⟨1686443911719891492688217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124295941146594328458811 1686443911719891492688217)
              ·
                refine ⟨1264832933789918619516163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686443911719891492688217 1264832933789918619516163)
                ·
                  refine ⟨1897249400684877929274245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264832933789918619516163 1897249400684877929274245)
                  ·
                    refine ⟨355734262628414611738921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1897249400684877929274245 355734262628414611738921)
                    ·
                      rfl

theorem cell22_1039185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_1039185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039185 prefixEnd_1039185 := by exact prefixLift 1039185
  have htrace : WordTrace (prefixWord ++ tailWord_1039185) baseStart_1039185 baseEnd_1039185 := by
    simpa [prefixWord, tailWord_1039185, baseEnd_1039185] using wordTrace_append hprefix tailTrace_1039185
  have hstable : (prefixWord ++ tailWord_1039185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039185).length < 2 ^ (prefixWord ++ tailWord_1039185).sum := by decide
  have hdescent : baseEnd_1039185 < baseStart_1039185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039194 : List Nat := [3, 1, 1, 2, 1, 4, 2, 8]
def baseStart_1039194 : Nat := 118140960795 + 1039194 * 2 ^ 59
def prefixEnd_1039194 : Nat := 4983230072969 + 3 ^ 40 * 1039194 * 2
def baseEnd_1039194 : Nat := 39526371501371287584877

theorem tailTrace_1039194 : CollatzResearch.WordTrace tailWord_1039194 prefixEnd_1039194 39526371501371287584877 := by
  unfold tailWord_1039194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475629749296273262597159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25268345998123395366925757 9475629749296273262597159)
  ·
    refine ⟨14213444623944409893895739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475629749296273262597159 14213444623944409893895739)
    ·
      refine ⟨21320166935916614840843609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213444623944409893895739 21320166935916614840843609)
      ·
        refine ⟨15990125201937461130632707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21320166935916614840843609 15990125201937461130632707)
        ·
          refine ⟨23985187802906191695949061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990125201937461130632707 23985187802906191695949061)
          ·
            refine ⟨4497222713044910942990449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23985187802906191695949061 4497222713044910942990449)
            ·
              refine ⟨3372917034783683207242837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497222713044910942990449 3372917034783683207242837)
              ·
                refine ⟨39526371501371287584877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3372917034783683207242837 39526371501371287584877)
                ·
                  rfl

theorem cell22_1039194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_1039194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1039194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1039194 prefixEnd_1039194 := by exact prefixLift 1039194
  have htrace : WordTrace (prefixWord ++ tailWord_1039194) baseStart_1039194 baseEnd_1039194 := by
    simpa [prefixWord, tailWord_1039194, baseEnd_1039194] using wordTrace_append hprefix tailTrace_1039194
  have hstable : (prefixWord ++ tailWord_1039194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039194).length < 2 ^ (prefixWord ++ tailWord_1039194).sum := by decide
  have hdescent : baseEnd_1039194 < baseStart_1039194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
