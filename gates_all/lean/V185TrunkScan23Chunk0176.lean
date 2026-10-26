import V185TrunkScan23Chunk0175

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1041840 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2]
def baseStart_1041840 : Nat := 118140960795 + 1041840 * 2 ^ 59
def prefixEnd_1041840 : Nat := 4983230072969 + 3 ^ 40 * 1041840 * 2
def baseEnd_1041840 : Nat := 534964685080309029908671

theorem tailTrace_1041840 : CollatzResearch.WordTrace tailWord_1041840 prefixEnd_1041840 534964685080309029908671 := by
  unfold tailWord_1041840
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999513272799543475605487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25332684363732724634140649 18999513272799543475605487)
  ·
    refine ⟨28499269909199315213408231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18999513272799543475605487 28499269909199315213408231)
    ·
      refine ⟨42748904863798972820112347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28499269909199315213408231 42748904863798972820112347)
      ·
        refine ⟨64123357295698459230168521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42748904863798972820112347 64123357295698459230168521)
        ·
          refine ⟨48092517971773844422626391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64123357295698459230168521 48092517971773844422626391)
          ·
            refine ⟨72138776957660766633939587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48092517971773844422626391 72138776957660766633939587)
            ·
              refine ⟨108208165436491149950909381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72138776957660766633939587 108208165436491149950909381)
              ·
                refine ⟨20289031019342090615795509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108208165436491149950909381 20289031019342090615795509)
                ·
                  refine ⟨1902096658063320995230829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20289031019342090615795509 1902096658063320995230829)
                  ·
                    refine ⟨713286246773745373211561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902096658063320995230829 713286246773745373211561)
                    ·
                      refine ⟨534964685080309029908671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713286246773745373211561 534964685080309029908671)
                      ·
                        rfl

theorem cell23_1041840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2].length) (baseStart_1041840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041840 prefixEnd_1041840 := by exact prefixLift 1041840
  have htrace : WordTrace (prefixWord ++ tailWord_1041840) baseStart_1041840 baseEnd_1041840 := by
    simpa [prefixWord, tailWord_1041840, baseEnd_1041840] using wordTrace_append hprefix tailTrace_1041840
  have hstable : (prefixWord ++ tailWord_1041840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041840).length < 2 ^ (prefixWord ++ tailWord_1041840).sum := by decide
  have hdescent : baseEnd_1041840 < baseStart_1041840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041858 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1041858 : Nat := 118140960795 + 1041858 * 2 ^ 59
def prefixEnd_1041858 : Nat := 4983230072969 + 3 ^ 40 * 1041858 * 2
def baseEnd_1041858 : Nat := 178324642577363319827863

theorem tailTrace_1041858 : CollatzResearch.WordTrace tailWord_1041858 prefixEnd_1041858 178324642577363319827863 := by
  unfold tailWord_1041858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499920764883469006341557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25333122039689250683577485 9499920764883469006341557)
  ·
    refine ⟨890617571707825219344521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9499920764883469006341557 890617571707825219344521)
    ·
      refine ⟨667963178780868914508391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 890617571707825219344521 667963178780868914508391)
      ·
        refine ⟨1001944768171303371762587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667963178780868914508391 1001944768171303371762587)
        ·
          refine ⟨1502917152256955057643881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001944768171303371762587 1502917152256955057643881)
          ·
            refine ⟨1127187864192716293232911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502917152256955057643881 1127187864192716293232911)
            ·
              refine ⟨1690781796289074439849367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127187864192716293232911 1690781796289074439849367)
              ·
                refine ⟨2536172694433611659774051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690781796289074439849367 2536172694433611659774051)
                ·
                  refine ⟨3804259041650417489661077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536172694433611659774051 3804259041650417489661077)
                  ·
                    refine ⟨178324642577363319827863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3804259041650417489661077 178324642577363319827863)
                    ·
                      rfl

theorem cell23_1041858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1041858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041858 prefixEnd_1041858 := by exact prefixLift 1041858
  have htrace : WordTrace (prefixWord ++ tailWord_1041858) baseStart_1041858 baseEnd_1041858 := by
    simpa [prefixWord, tailWord_1041858, baseEnd_1041858] using wordTrace_append hprefix tailTrace_1041858
  have hstable : (prefixWord ++ tailWord_1041858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041858).length < 2 ^ (prefixWord ++ tailWord_1041858).sum := by decide
  have hdescent : baseEnd_1041858 < baseStart_1041858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041863 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 2, 6]
def baseStart_1041863 : Nat := 118140960795 + 1041863 * 2 ^ 59
def prefixEnd_1041863 : Nat := 4983230072969 + 3 ^ 40 * 1041863 * 2
def baseEnd_1041863 : Nat := 178325498378454146640355

theorem tailTrace_1041863 : CollatzResearch.WordTrace tailWord_1041863 prefixEnd_1041863 178325498378454146640355 := by
  unfold tailWord_1041863
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999865424515761879298243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25333243616343841252865495 37999865424515761879298243)
  ·
    refine ⟨56999798136773642818947365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37999865424515761879298243 56999798136773642818947365)
    ·
      refine ⟨10687462150645058028552631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56999798136773642818947365 10687462150645058028552631)
      ·
        refine ⟨16031193225967587042828947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687462150645058028552631 16031193225967587042828947)
        ·
          refine ⟨24046789838951380564243421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16031193225967587042828947 24046789838951380564243421)
          ·
            refine ⟨9017546189606767711591283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24046789838951380564243421 9017546189606767711591283)
            ·
              refine ⟨13526319284410151567386925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017546189606767711591283 13526319284410151567386925)
              ·
                refine ⟨5072369731653806837770097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13526319284410151567386925 5072369731653806837770097)
                ·
                  refine ⟨3804277298740355128327573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5072369731653806837770097 3804277298740355128327573)
                  ·
                    refine ⟨178325498378454146640355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3804277298740355128327573 178325498378454146640355)
                    ·
                      rfl

theorem cell23_1041863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_1041863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041863 prefixEnd_1041863 := by exact prefixLift 1041863
  have htrace : WordTrace (prefixWord ++ tailWord_1041863) baseStart_1041863 baseEnd_1041863 := by
    simpa [prefixWord, tailWord_1041863, baseEnd_1041863] using wordTrace_append hprefix tailTrace_1041863
  have hstable : (prefixWord ++ tailWord_1041863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041863).length < 2 ^ (prefixWord ++ tailWord_1041863).sum := by decide
  have hdescent : baseEnd_1041863 < baseStart_1041863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041864 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_1041864 : Nat := 118140960795 + 1041864 * 2 ^ 59
def prefixEnd_1041864 : Nat := 4983230072969 + 3 ^ 40 * 1041864 * 2
def baseEnd_1041864 : Nat := 534977008616016936008561

theorem tailTrace_1041864 : CollatzResearch.WordTrace tailWord_1041864 prefixEnd_1041864 534977008616016936008561 := by
  unfold tailWord_1041864
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999950948756069525042323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25333267931674759366723097 18999950948756069525042323)
  ·
    refine ⟨28499926423134104287563485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18999950948756069525042323 28499926423134104287563485)
    ·
      refine ⟨10687472408675289107836307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28499926423134104287563485 10687472408675289107836307)
      ·
        refine ⟨16031208613012933661754461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687472408675289107836307 16031208613012933661754461)
        ·
          refine ⟨6011703229879850123157923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16031208613012933661754461 6011703229879850123157923)
          ·
            refine ⟨9017554844819775184736885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011703229879850123157923 9017554844819775184736885)
            ·
              refine ⟨845395766701853923569083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9017554844819775184736885 845395766701853923569083)
              ·
                refine ⟨1268093650052780885353625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845395766701853923569083 1268093650052780885353625)
                ·
                  refine ⟨951070237539585664015219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1268093650052780885353625 951070237539585664015219)
                  ·
                    refine ⟨1426605356309378496022829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 951070237539585664015219 1426605356309378496022829)
                    ·
                      refine ⟨534977008616016936008561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426605356309378496022829 534977008616016936008561)
                      ·
                        rfl

theorem cell23_1041864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_1041864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041864 prefixEnd_1041864 := by exact prefixLift 1041864
  have htrace : WordTrace (prefixWord ++ tailWord_1041864) baseStart_1041864 baseEnd_1041864 := by
    simpa [prefixWord, tailWord_1041864, baseEnd_1041864] using wordTrace_append hprefix tailTrace_1041864
  have hstable : (prefixWord ++ tailWord_1041864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041864).length < 2 ^ (prefixWord ++ tailWord_1041864).sum := by decide
  have hdescent : baseEnd_1041864 < baseStart_1041864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041887 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 6, 2, 2]
def baseStart_1041887 : Nat := 118140960795 + 1041887 * 2 ^ 59
def prefixEnd_1041887 : Nat := 4983230072969 + 3 ^ 40 * 1041887 * 2
def baseEnd_1041887 : Nat := 534988818671070346020955

theorem tailTrace_1041887 : CollatzResearch.WordTrace tailWord_1041887 prefixEnd_1041887 534988818671070346020955 := by
  unfold tailWord_1041887
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000740776428813978171915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25333827184285875985447943 38000740776428813978171915)
  ·
    refine ⟨57001111164643220967257873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38000740776428813978171915 57001111164643220967257873)
    ·
      refine ⟨42750833373482415725443405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57001111164643220967257873 42750833373482415725443405)
      ·
        refine ⟨16031562515055905897041277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42750833373482415725443405 16031562515055905897041277)
        ·
          refine ⟨6011835943145964711390479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16031562515055905897041277 6011835943145964711390479)
          ·
            refine ⟨9017753914718947067085719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011835943145964711390479 9017753914718947067085719)
            ·
              refine ⟨13526630872078420600628579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9017753914718947067085719 13526630872078420600628579)
              ·
                refine ⟨20289946308117630900942869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13526630872078420600628579 20289946308117630900942869)
                ·
                  refine ⟨951091233193013948481697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20289946308117630900942869 951091233193013948481697)
                  ·
                    refine ⟨713318424894760461361273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951091233193013948481697 713318424894760461361273)
                    ·
                      refine ⟨534988818671070346020955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713318424894760461361273 534988818671070346020955)
                      ·
                        rfl

theorem cell23_1041887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_1041887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041887 prefixEnd_1041887 := by exact prefixLift 1041887
  have htrace : WordTrace (prefixWord ++ tailWord_1041887) baseStart_1041887 baseEnd_1041887 := by
    simpa [prefixWord, tailWord_1041887, baseEnd_1041887] using wordTrace_append hprefix tailTrace_1041887
  have hstable : (prefixWord ++ tailWord_1041887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041887).length < 2 ^ (prefixWord ++ tailWord_1041887).sum := by decide
  have hdescent : baseEnd_1041887 < baseStart_1041887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041921 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_1041921 : Nat := 118140960795 + 1041921 * 2 ^ 59
def prefixEnd_1041921 : Nat := 4983230072969 + 3 ^ 40 * 1041921 * 2
def baseEnd_1041921 : Nat := 535006277013323212995799

theorem tailTrace_1041921 : CollatzResearch.WordTrace tailWord_1041921 prefixEnd_1041921 535006277013323212995799 := by
  unfold tailWord_1041921
  simp only [CollatzResearch.WordTrace]
  refine ⟨38001980858305637784909617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25334653905537091856606411 38001980858305637784909617)
  ·
    refine ⟨28501485643729228338682213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38001980858305637784909617 28501485643729228338682213)
    ·
      refine ⟨5344028558199230313502915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28501485643729228338682213 5344028558199230313502915)
      ·
        refine ⟨8016042837298845470254373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5344028558199230313502915 8016042837298845470254373)
        ·
          refine ⟨1503008031993533525672695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8016042837298845470254373 1503008031993533525672695)
          ·
            refine ⟨2254512047990300288509043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503008031993533525672695 2254512047990300288509043)
            ·
              refine ⟨3381768071985450432763565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254512047990300288509043 3381768071985450432763565)
              ·
                refine ⟨1268163026994543912286337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381768071985450432763565 1268163026994543912286337)
                ·
                  refine ⟨951122270245907934214753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1268163026994543912286337 951122270245907934214753)
                  ·
                    refine ⟨713341702684430950661065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951122270245907934214753 713341702684430950661065)
                    ·
                      refine ⟨535006277013323212995799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713341702684430950661065 535006277013323212995799)
                      ·
                        rfl

theorem cell23_1041921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_1041921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041921 prefixEnd_1041921 := by exact prefixLift 1041921
  have htrace : WordTrace (prefixWord ++ tailWord_1041921) baseStart_1041921 baseEnd_1041921 := by
    simpa [prefixWord, tailWord_1041921, baseEnd_1041921] using wordTrace_append hprefix tailTrace_1041921
  have hstable : (prefixWord ++ tailWord_1041921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041921).length < 2 ^ (prefixWord ++ tailWord_1041921).sum := by decide
  have hdescent : baseEnd_1041921 < baseStart_1041921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041923 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 7]
def baseStart_1041923 : Nat := 118140960795 + 1041923 * 2 ^ 59
def prefixEnd_1041923 : Nat := 4983230072969 + 3 ^ 40 * 1041923 * 2
def baseEnd_1041923 : Nat := 178335767991544068390263

theorem tailTrace_1041923 : CollatzResearch.WordTrace tailWord_1041923 prefixEnd_1041923 178335767991544068390263 := by
  unfold tailWord_1041923
  simp only [CollatzResearch.WordTrace]
  refine ⟨38002053804298392126482423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25334702536198928084321615 38002053804298392126482423)
  ·
    refine ⟨57003080706447588189723635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38002053804298392126482423 57003080706447588189723635)
    ·
      refine ⟨85504621059671382284585453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57003080706447588189723635 85504621059671382284585453)
      ·
        refine ⟨32064232897376768356719545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85504621059671382284585453 32064232897376768356719545)
        ·
          refine ⟨24048174673032576267539659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32064232897376768356719545 24048174673032576267539659)
          ·
            refine ⟨36072262009548864401309489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24048174673032576267539659 36072262009548864401309489)
            ·
              refine ⟨27054196507161648300982117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36072262009548864401309489 27054196507161648300982117)
              ·
                refine ⟨5072661845092809056434147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27054196507161648300982117 5072661845092809056434147)
                ·
                  refine ⟨7608992767639213584651221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072661845092809056434147 7608992767639213584651221)
                  ·
                    refine ⟨178335767991544068390263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7608992767639213584651221 178335767991544068390263)
                    ·
                      rfl

theorem cell23_1041923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_1041923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041923 prefixEnd_1041923 := by exact prefixLift 1041923
  have htrace : WordTrace (prefixWord ++ tailWord_1041923) baseStart_1041923 baseEnd_1041923 := by
    simpa [prefixWord, tailWord_1041923, baseEnd_1041923] using wordTrace_append hprefix tailTrace_1041923
  have hstable : (prefixWord ++ tailWord_1041923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041923).length < 2 ^ (prefixWord ++ tailWord_1041923).sum := by decide
  have hdescent : baseEnd_1041923 < baseStart_1041923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041977 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1041977 : Nat := 118140960795 + 1041977 * 2 ^ 59
def prefixEnd_1041977 : Nat := 4983230072969 + 3 ^ 40 * 1041977 * 2
def baseEnd_1041977 : Nat := 535035031929974993895541

theorem tailTrace_1041977 : CollatzResearch.WordTrace tailWord_1041977 prefixEnd_1041977 535035031929974993895541 := by
  unfold tailWord_1041977
  simp only [CollatzResearch.WordTrace]
  refine ⟨38004023346102759348948185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25336015564068506232632123 38004023346102759348948185)
  ·
    refine ⟨28503017509577069511711139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38004023346102759348948185 28503017509577069511711139)
    ·
      refine ⟨42754526264365604267566709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28503017509577069511711139 42754526264365604267566709)
      ·
        refine ⟨4008236837284275400084379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42754526264365604267566709 4008236837284275400084379)
        ·
          refine ⟨6012355255926413100126569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008236837284275400084379 6012355255926413100126569)
          ·
            refine ⟨4509266441944809825094927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012355255926413100126569 4509266441944809825094927)
            ·
              refine ⟨6763899662917214737642391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509266441944809825094927 6763899662917214737642391)
              ·
                refine ⟨10145849494375822106463587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763899662917214737642391 10145849494375822106463587)
                ·
                  refine ⟨15218774241563733159695381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10145849494375822106463587 15218774241563733159695381)
                  ·
                    refine ⟨713380042573299991860721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15218774241563733159695381 713380042573299991860721)
                    ·
                      refine ⟨535035031929974993895541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713380042573299991860721 535035031929974993895541)
                      ·
                        rfl

theorem cell23_1041977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1041977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1041977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1041977 prefixEnd_1041977 := by exact prefixLift 1041977
  have htrace : WordTrace (prefixWord ++ tailWord_1041977) baseStart_1041977 baseEnd_1041977 := by
    simpa [prefixWord, tailWord_1041977, baseEnd_1041977] using wordTrace_append hprefix tailTrace_1041977
  have hstable : (prefixWord ++ tailWord_1041977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041977).length < 2 ^ (prefixWord ++ tailWord_1041977).sum := by decide
  have hdescent : baseEnd_1041977 < baseStart_1041977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042010 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1042010 : Nat := 118140960795 + 1042010 * 2 ^ 59
def prefixEnd_1042010 : Nat := 4983230072969 + 3 ^ 40 * 1042010 * 2
def baseEnd_1042010 : Nat := 535051976791573364782889

theorem tailTrace_1042010 : CollatzResearch.WordTrace tailWord_1042010 prefixEnd_1042010 535051976791573364782889 := by
  unfold tailWord_1042010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501306738745801496224871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25336817969988803989932989 9501306738745801496224871)
  ·
    refine ⟨14251960108118702244337307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501306738745801496224871 14251960108118702244337307)
    ·
      refine ⟨21377940162178053366505961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14251960108118702244337307 21377940162178053366505961)
      ·
        refine ⟨16033455121633540024879471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21377940162178053366505961 16033455121633540024879471)
        ·
          refine ⟨24050182682450310037319207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16033455121633540024879471 24050182682450310037319207)
          ·
            refine ⟨36075274023675465055978811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24050182682450310037319207 36075274023675465055978811)
            ·
              refine ⟨54112911035513197583968217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36075274023675465055978811 54112911035513197583968217)
              ·
                refine ⟨40584683276634898187976163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54112911035513197583968217 40584683276634898187976163)
                ·
                  refine ⟨60877024914952347281964245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40584683276634898187976163 60877024914952347281964245)
                  ·
                    refine ⟨1426805271444195639421037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60877024914952347281964245 1426805271444195639421037)
                    ·
                      refine ⟨535051976791573364782889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426805271444195639421037 535051976791573364782889)
                      ·
                        rfl

theorem cell23_1042010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1042010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042010 prefixEnd_1042010 := by exact prefixLift 1042010
  have htrace : WordTrace (prefixWord ++ tailWord_1042010) baseStart_1042010 baseEnd_1042010 := by
    simpa [prefixWord, tailWord_1042010, baseEnd_1042010] using wordTrace_append hprefix tailTrace_1042010
  have hstable : (prefixWord ++ tailWord_1042010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042010).length < 2 ^ (prefixWord ++ tailWord_1042010).sum := by decide
  have hdescent : baseEnd_1042010 < baseStart_1042010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042020 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1042020 : Nat := 118140960795 + 1042020 * 2 ^ 59
def prefixEnd_1042020 : Nat := 4983230072969 + 3 ^ 40 * 1042020 * 2
def baseEnd_1042020 : Nat := 535057111598118325657843

theorem tailTrace_1042020 : CollatzResearch.WordTrace tailWord_1042020 prefixEnd_1042020 535057111598118325657843 := by
  unfold tailWord_1042020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002795842473488846381757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25337061123297985128509009 19002795842473488846381757)
  ·
    refine ⟨7126048440927558317393159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19002795842473488846381757 7126048440927558317393159)
    ·
      refine ⟨10689072661391337476089739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126048440927558317393159 10689072661391337476089739)
      ·
        refine ⟨16033608992087006214134609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10689072661391337476089739 16033608992087006214134609)
        ·
          refine ⟨12025206744065254660600957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16033608992087006214134609 12025206744065254660600957)
          ·
            refine ⟨4509452529024470497725359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12025206744065254660600957 4509452529024470497725359)
            ·
              refine ⟨6764178793536705746588039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509452529024470497725359 6764178793536705746588039)
              ·
                refine ⟨10146268190305058619882059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764178793536705746588039 10146268190305058619882059)
                ·
                  refine ⟨15219402285457587929823089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146268190305058619882059 15219402285457587929823089)
                  ·
                    refine ⟨11414551714093190947367317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15219402285457587929823089 11414551714093190947367317)
                    ·
                      refine ⟨535057111598118325657843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11414551714093190947367317 535057111598118325657843)
                      ·
                        rfl

theorem cell23_1042020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1042020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042020 prefixEnd_1042020 := by exact prefixLift 1042020
  have htrace : WordTrace (prefixWord ++ tailWord_1042020) baseStart_1042020 baseEnd_1042020 := by
    simpa [prefixWord, tailWord_1042020, baseEnd_1042020] using wordTrace_append hprefix tailTrace_1042020
  have hstable : (prefixWord ++ tailWord_1042020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042020).length < 2 ^ (prefixWord ++ tailWord_1042020).sum := by decide
  have hdescent : baseEnd_1042020 < baseStart_1042020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042034 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_1042034 : Nat := 118140960795 + 1042034 * 2 ^ 59
def prefixEnd_1042034 : Nat := 4983230072969 + 3 ^ 40 * 1042034 * 2
def baseEnd_1042034 : Nat := 59451588925253474542531

theorem tailTrace_1042034 : CollatzResearch.WordTrace tailWord_1042034 prefixEnd_1042034 59451588925253474542531 := by
  unfold tailWord_1042034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501525576724064520943289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25337401537930838722515437 9501525576724064520943289)
  ·
    refine ⟨7126144182543048390707467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9501525576724064520943289 7126144182543048390707467)
    ·
      refine ⟨10689216273814572586061201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126144182543048390707467 10689216273814572586061201)
      ·
        refine ⟨8016912205360929439545901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10689216273814572586061201 8016912205360929439545901)
        ·
          refine ⟨3006342077010348539829713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8016912205360929439545901 3006342077010348539829713)
          ·
            refine ⟨2254756557757761404872285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006342077010348539829713 2254756557757761404872285)
            ·
              refine ⟨845533709159160526827107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2254756557757761404872285 845533709159160526827107)
              ·
                refine ⟨1268300563738740790240661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845533709159160526827107 1268300563738740790240661)
                ·
                  refine ⟨59451588925253474542531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1268300563738740790240661 59451588925253474542531)
                  ·
                    rfl

theorem cell23_1042034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_1042034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042034 prefixEnd_1042034 := by exact prefixLift 1042034
  have htrace : WordTrace (prefixWord ++ tailWord_1042034) baseStart_1042034 baseEnd_1042034 := by
    simpa [prefixWord, tailWord_1042034, baseEnd_1042034] using wordTrace_append hprefix tailTrace_1042034
  have hstable : (prefixWord ++ tailWord_1042034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042034).length < 2 ^ (prefixWord ++ tailWord_1042034).sum := by decide
  have hdescent : baseEnd_1042034 < baseStart_1042034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042060 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_1042060 : Nat := 118140960795 + 1042060 * 2 ^ 59
def prefixEnd_1042060 : Nat := 4983230072969 + 3 ^ 40 * 1042060 * 2
def baseEnd_1042060 : Nat := 178359216941432723052553

theorem tailTrace_1042060 : CollatzResearch.WordTrace tailWord_1042060 prefixEnd_1042060 178359216941432723052553 := by
  unfold tailWord_1042060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003525302401032262109817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25338033736534709682813089 19003525302401032262109817)
  ·
    refine ⟨14252643976800774196582363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19003525302401032262109817 14252643976800774196582363)
    ·
      refine ⟨21378965965201161294873545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14252643976800774196582363 21378965965201161294873545)
      ·
        refine ⟨16034224473900870971155159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21378965965201161294873545 16034224473900870971155159)
        ·
          refine ⟨24051336710851306456732739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034224473900870971155159 24051336710851306456732739)
          ·
            refine ⟨36077005066276959685099109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24051336710851306456732739 36077005066276959685099109)
            ·
              refine ⟨6764438449926929940956083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36077005066276959685099109 6764438449926929940956083)
              ·
                refine ⟨10146657674890394911434125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764438449926929940956083 10146657674890394911434125)
                ·
                  refine ⟨3804996628083898091787797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10146657674890394911434125 3804996628083898091787797)
                  ·
                    refine ⟨178359216941432723052553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3804996628083898091787797 178359216941432723052553)
                    ·
                      rfl

theorem cell23_1042060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_1042060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042060 prefixEnd_1042060 := by exact prefixLift 1042060
  have htrace : WordTrace (prefixWord ++ tailWord_1042060) baseStart_1042060 baseEnd_1042060 := by
    simpa [prefixWord, tailWord_1042060, baseEnd_1042060] using wordTrace_append hprefix tailTrace_1042060
  have hstable : (prefixWord ++ tailWord_1042060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042060).length < 2 ^ (prefixWord ++ tailWord_1042060).sum := by decide
  have hdescent : baseEnd_1042060 < baseStart_1042060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042078 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1042078 : Nat := 118140960795 + 1042078 * 2 ^ 59
def prefixEnd_1042078 : Nat := 4983230072969 + 3 ^ 40 * 1042078 * 2
def baseEnd_1042078 : Nat := 535086893476079098732577

theorem tailTrace_1042078 : CollatzResearch.WordTrace tailWord_1042078 prefixEnd_1042078 535086893476079098732577 := by
  unfold tailWord_1042078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750963389842106699796861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25338471412491235732249925 4750963389842106699796861)
  ·
    refine ⟨1781611271190790012423823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4750963389842106699796861 1781611271190790012423823)
    ·
      refine ⟨2672416906786185018635735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781611271190790012423823 2672416906786185018635735)
      ·
        refine ⟨4008625360179277527953603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672416906786185018635735 4008625360179277527953603)
        ·
          refine ⟨6012938040268916291930405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008625360179277527953603 6012938040268916291930405)
          ·
            refine ⟨1127425882550421804736951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6012938040268916291930405 1127425882550421804736951)
            ·
              refine ⟨1691138823825632707105427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127425882550421804736951 1691138823825632707105427)
              ·
                refine ⟨2536708235738449060658141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691138823825632707105427 2536708235738449060658141)
                ·
                  refine ⟨951265588401918397746803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2536708235738449060658141 951265588401918397746803)
                  ·
                    refine ⟨1426898382602877596620205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 951265588401918397746803 1426898382602877596620205)
                    ·
                      refine ⟨535086893476079098732577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426898382602877596620205 535086893476079098732577)
                      ·
                        rfl

theorem cell23_1042078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1042078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042078 prefixEnd_1042078 := by exact prefixLift 1042078
  have htrace : WordTrace (prefixWord ++ tailWord_1042078) baseStart_1042078 baseEnd_1042078 := by
    simpa [prefixWord, tailWord_1042078, baseEnd_1042078] using wordTrace_append hprefix tailTrace_1042078
  have hstable : (prefixWord ++ tailWord_1042078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042078).length < 2 ^ (prefixWord ++ tailWord_1042078).sum := by decide
  have hdescent : baseEnd_1042078 < baseStart_1042078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042117 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_1042117 : Nat := 118140960795 + 1042117 * 2 ^ 59
def prefixEnd_1042117 : Nat := 4983230072969 + 3 ^ 40 * 1042117 * 2
def baseEnd_1042117 : Nat := 535106919221604446144897

theorem tailTrace_1042117 : CollatzResearch.WordTrace tailWord_1042117 prefixEnd_1042117 535106919221604446144897 := by
  unfold tailWord_1042117
  simp only [CollatzResearch.WordTrace]
  refine ⟨38009129565595563259044605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25339419710397042172696403 38009129565595563259044605)
  ·
    refine ⟨14253423587098336222141727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38009129565595563259044605 14253423587098336222141727)
    ·
      refine ⟨21380135380647504333212591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14253423587098336222141727 21380135380647504333212591)
      ·
        refine ⟨32070203070971256499818887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21380135380647504333212591 32070203070971256499818887)
        ·
          refine ⟨48105304606456884749728331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32070203070971256499818887 48105304606456884749728331)
          ·
            refine ⟨72157956909685327124592497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48105304606456884749728331 72157956909685327124592497)
            ·
              refine ⟨54118467682263995343444373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72157956909685327124592497 54118467682263995343444373)
              ·
                refine ⟨2536803172606124781723955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54118467682263995343444373 2536803172606124781723955)
                ·
                  refine ⟨3805204758909187172585933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536803172606124781723955 3805204758909187172585933)
                  ·
                    refine ⟨1426951784590945189719725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3805204758909187172585933 1426951784590945189719725)
                    ·
                      refine ⟨535106919221604446144897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1426951784590945189719725 535106919221604446144897)
                      ·
                        rfl

theorem cell23_1042117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_1042117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042117 prefixEnd_1042117 := by exact prefixLift 1042117
  have htrace : WordTrace (prefixWord ++ tailWord_1042117) baseStart_1042117 baseEnd_1042117 := by
    simpa [prefixWord, tailWord_1042117, baseEnd_1042117] using wordTrace_append hprefix tailTrace_1042117
  have hstable : (prefixWord ++ tailWord_1042117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042117).length < 2 ^ (prefixWord ++ tailWord_1042117).sum := by decide
  have hdescent : baseEnd_1042117 < baseStart_1042117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042141 : List Nat := [1, 4, 3, 3, 1, 2, 1, 8]
def baseStart_1042141 : Nat := 118140960795 + 1042141 * 2 ^ 59
def prefixEnd_1042141 : Nat := 4983230072969 + 3 ^ 40 * 1042141 * 2
def baseEnd_1042141 : Nat := 19819231213233790823881

theorem tailTrace_1042141 : CollatzResearch.WordTrace tailWord_1042141 prefixEnd_1042141 19819231213233790823881 := by
  unfold tailWord_1042141
  simp only [CollatzResearch.WordTrace]
  refine ⟨38010004917508615357918277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25340003278339076905278851 38010004917508615357918277)
  ·
    refine ⟨7126875922032865379609677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38010004917508615357918277 7126875922032865379609677)
    ·
      refine ⟨2672578470762324517353629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7126875922032865379609677 2672578470762324517353629)
      ·
        refine ⟨1002216926535871694007611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2672578470762324517353629 1002216926535871694007611)
        ·
          refine ⟨1503325389803807541011417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002216926535871694007611 1503325389803807541011417)
          ·
            refine ⟨1127494042352855655758563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503325389803807541011417 1127494042352855655758563)
            ·
              refine ⟨1691241063529283483637845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127494042352855655758563 1691241063529283483637845)
              ·
                refine ⟨19819231213233790823881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1691241063529283483637845 19819231213233790823881)
                ·
                  rfl

theorem cell23_1042141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 8].length) (baseStart_1042141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042141 prefixEnd_1042141 := by exact prefixLift 1042141
  have htrace : WordTrace (prefixWord ++ tailWord_1042141) baseStart_1042141 baseEnd_1042141 := by
    simpa [prefixWord, tailWord_1042141, baseEnd_1042141] using wordTrace_append hprefix tailTrace_1042141
  have hstable : (prefixWord ++ tailWord_1042141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042141).length < 2 ^ (prefixWord ++ tailWord_1042141).sum := by decide
  have hdescent : baseEnd_1042141 < baseStart_1042141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042144 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2]
def baseStart_1042144 : Nat := 118140960795 + 1042144 * 2 ^ 59
def prefixEnd_1042144 : Nat := 4983230072969 + 3 ^ 40 * 1042144 * 2
def baseEnd_1042144 : Nat := 535120783199275840507273

theorem tailTrace_1042144 : CollatzResearch.WordTrace tailWord_1042144 prefixEnd_1042144 535120783199275840507273 := by
  unfold tailWord_1042144
  simp only [CollatzResearch.WordTrace]
  refine ⟨19005057168248873435138743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25340076224331831246851657 19005057168248873435138743)
  ·
    refine ⟨28507585752373310152708115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19005057168248873435138743 28507585752373310152708115)
    ·
      refine ⟨42761378628559965229062173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28507585752373310152708115 42761378628559965229062173)
      ·
        refine ⟨16035516985709986960898315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42761378628559965229062173 16035516985709986960898315)
        ·
          refine ⟨24053275478564980441347473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16035516985709986960898315 24053275478564980441347473)
          ·
            refine ⟨18039956608923735331010605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24053275478564980441347473 18039956608923735331010605)
            ·
              refine ⟨6764983728346400749128977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18039956608923735331010605 6764983728346400749128977)
              ·
                refine ⟨5073737796259800561846733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764983728346400749128977 5073737796259800561846733)
                ·
                  refine ⟨1902651673597425210692525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5073737796259800561846733 1902651673597425210692525)
                  ·
                    refine ⟨713494377599034454009697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902651673597425210692525 713494377599034454009697)
                    ·
                      refine ⟨535120783199275840507273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713494377599034454009697 535120783199275840507273)
                      ·
                        rfl

theorem cell23_1042144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_1042144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042144 prefixEnd_1042144 := by exact prefixLift 1042144
  have htrace : WordTrace (prefixWord ++ tailWord_1042144) baseStart_1042144 baseEnd_1042144 := by
    simpa [prefixWord, tailWord_1042144, baseEnd_1042144] using wordTrace_append hprefix tailTrace_1042144
  have hstable : (prefixWord ++ tailWord_1042144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042144).length < 2 ^ (prefixWord ++ tailWord_1042144).sum := by decide
  have hdescent : baseEnd_1042144 < baseStart_1042144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042177 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1042177 : Nat := 118140960795 + 1042177 * 2 ^ 59
def prefixEnd_1042177 : Nat := 4983230072969 + 3 ^ 40 * 1042177 * 2
def baseEnd_1042177 : Nat := 535137728060874211394621

theorem tailTrace_1042177 : CollatzResearch.WordTrace tailWord_1042177 prefixEnd_1042177 535137728060874211394621 := by
  unfold tailWord_1042177
  simp only [CollatzResearch.WordTrace]
  refine ⟨38011317945378193506228785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25340878630252129004152523 38011317945378193506228785)
  ·
    refine ⟨28508488459033645129671589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38011317945378193506228785 28508488459033645129671589)
    ·
      refine ⟨5345341586068808461813423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28508488459033645129671589 5345341586068808461813423)
      ·
        refine ⟨8018012379103212692720135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345341586068808461813423 8018012379103212692720135)
        ·
          refine ⟨12027018568654819039080203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018012379103212692720135 12027018568654819039080203)
          ·
            refine ⟨18040527852982228558620305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12027018568654819039080203 18040527852982228558620305)
            ·
              refine ⟨13530395889736671418965229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18040527852982228558620305 13530395889736671418965229)
              ·
                refine ⟨5073898458651251782111961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13530395889736671418965229 5073898458651251782111961)
                ·
                  refine ⟨3805423843988438836583971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073898458651251782111961 3805423843988438836583971)
                  ·
                    refine ⟨5708135765982658254875957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805423843988438836583971 5708135765982658254875957)
                    ·
                      refine ⟨535137728060874211394621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5708135765982658254875957 535137728060874211394621)
                      ·
                        rfl

theorem cell23_1042177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1042177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042177 prefixEnd_1042177 := by exact prefixLift 1042177
  have htrace : WordTrace (prefixWord ++ tailWord_1042177) baseStart_1042177 baseEnd_1042177 := by
    simpa [prefixWord, tailWord_1042177, baseEnd_1042177] using wordTrace_append hprefix tailTrace_1042177
  have hstable : (prefixWord ++ tailWord_1042177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042177).length < 2 ^ (prefixWord ++ tailWord_1042177).sum := by decide
  have hdescent : baseEnd_1042177 < baseStart_1042177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042178 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1042178 : Nat := 118140960795 + 1042178 * 2 ^ 59
def prefixEnd_1042178 : Nat := 4983230072969 + 3 ^ 40 * 1042178 * 2
def baseEnd_1042178 : Nat := 535138241541528707482117

theorem tailTrace_1042178 : CollatzResearch.WordTrace tailWord_1042178 prefixEnd_1042178 535138241541528707482117 := by
  unfold tailWord_1042178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9502838604593642669253797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25340902945583047118010125 9502838604593642669253797)
  ·
    refine ⟨1781782238361308000485087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9502838604593642669253797 1781782238361308000485087)
    ·
      refine ⟨2672673357541962000727631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781782238361308000485087 2672673357541962000727631)
      ·
        refine ⟨4009010036312943001091447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672673357541962000727631 4009010036312943001091447)
        ·
          refine ⟨6013515054469414501637171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009010036312943001091447 6013515054469414501637171)
          ·
            refine ⟨9020272581704121752455757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013515054469414501637171 9020272581704121752455757)
            ·
              refine ⟨3382602218139045657170909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9020272581704121752455757 3382602218139045657170909)
              ·
                refine ⟨1268475831802142121439091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382602218139045657170909 1268475831802142121439091)
                ·
                  refine ⟨1902713747703213182158637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268475831802142121439091 1902713747703213182158637)
                  ·
                    refine ⟨713517655388704943309489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1902713747703213182158637 713517655388704943309489)
                    ·
                      refine ⟨535138241541528707482117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713517655388704943309489 535138241541528707482117)
                      ·
                        rfl

theorem cell23_1042178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1042178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042178 prefixEnd_1042178 := by exact prefixLift 1042178
  have htrace : WordTrace (prefixWord ++ tailWord_1042178) baseStart_1042178 baseEnd_1042178 := by
    simpa [prefixWord, tailWord_1042178, baseEnd_1042178] using wordTrace_append hprefix tailTrace_1042178
  have hstable : (prefixWord ++ tailWord_1042178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042178).length < 2 ^ (prefixWord ++ tailWord_1042178).sum := by decide
  have hdescent : baseEnd_1042178 < baseStart_1042178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042187 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_1042187 : Nat := 118140960795 + 1042187 * 2 ^ 59
def prefixEnd_1042187 : Nat := 4983230072969 + 3 ^ 40 * 1042187 * 2
def baseEnd_1042187 : Nat := 535142862867419172269575

theorem tailTrace_1042187 : CollatzResearch.WordTrace tailWord_1042187 prefixEnd_1042187 535142862867419172269575 := by
  unfold tailWord_1042187
  simp only [CollatzResearch.WordTrace]
  refine ⟨38011682675341965214092815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25341121783561310142728543 38011682675341965214092815)
  ·
    refine ⟨57017524013012947821139223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38011682675341965214092815 57017524013012947821139223)
    ·
      refine ⟨85526286019519421731708835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57017524013012947821139223 85526286019519421731708835)
      ·
        refine ⟨128289429029279132597563253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85526286019519421731708835 128289429029279132597563253)
        ·
          refine ⟨12027133971494918681021555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128289429029279132597563253 12027133971494918681021555)
          ·
            refine ⟨18040700957242378021532333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12027133971494918681021555 18040700957242378021532333)
            ·
              refine ⟨6765262858965891758074625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18040700957242378021532333 6765262858965891758074625)
              ·
                refine ⟨5073947144224418818555969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765262858965891758074625 5073947144224418818555969)
                ·
                  refine ⟨3805460358168314113916977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073947144224418818555969 3805460358168314113916977)
                  ·
                    refine ⟨2854095268626235585437733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805460358168314113916977 2854095268626235585437733)
                    ·
                      refine ⟨535142862867419172269575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2854095268626235585437733 535142862867419172269575)
                      ·
                        rfl

theorem cell23_1042187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_1042187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042187 prefixEnd_1042187 := by exact prefixLift 1042187
  have htrace : WordTrace (prefixWord ++ tailWord_1042187) baseStart_1042187 baseEnd_1042187 := by
    simpa [prefixWord, tailWord_1042187, baseEnd_1042187] using wordTrace_append hprefix tailTrace_1042187
  have hstable : (prefixWord ++ tailWord_1042187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042187).length < 2 ^ (prefixWord ++ tailWord_1042187).sum := by decide
  have hdescent : baseEnd_1042187 < baseStart_1042187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042191 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 2, 2, 2]
def baseStart_1042191 : Nat := 118140960795 + 1042191 * 2 ^ 59
def prefixEnd_1042191 : Nat := 4983230072969 + 3 ^ 40 * 1042191 * 2
def baseEnd_1042191 : Nat := 535144916790037156619557

theorem tailTrace_1042191 : CollatzResearch.WordTrace tailWord_1042191 prefixEnd_1042191 535144916790037156619557 := by
  unfold tailWord_1042191
  simp only [CollatzResearch.WordTrace]
  refine ⟨38011828567327473897238427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25341219044884982598158951 38011828567327473897238427)
  ·
    refine ⟨57017742850991210845857641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38011828567327473897238427 57017742850991210845857641)
    ·
      refine ⟨42763307138243408134393231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57017742850991210845857641 42763307138243408134393231)
      ·
        refine ⟨64144960707365112201589847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42763307138243408134393231 64144960707365112201589847)
        ·
          refine ⟨96217441061047668302384771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64144960707365112201589847 96217441061047668302384771)
          ·
            refine ⟨144326161591571502453577157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96217441061047668302384771 144326161591571502453577157)
            ·
              refine ⟨27061155298419656710045717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144326161591571502453577157 27061155298419656710045717)
              ·
                refine ⟨1268491654613421408283393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27061155298419656710045717 1268491654613421408283393)
                ·
                  refine ⟨951368740960066056212545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1268491654613421408283393 951368740960066056212545)
                  ·
                    refine ⟨713526555720049542159409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951368740960066056212545 713526555720049542159409)
                    ·
                      refine ⟨535144916790037156619557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713526555720049542159409 535144916790037156619557)
                      ·
                        rfl

theorem cell23_1042191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2, 2].length) (baseStart_1042191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042191 prefixEnd_1042191 := by exact prefixLift 1042191
  have htrace : WordTrace (prefixWord ++ tailWord_1042191) baseStart_1042191 baseEnd_1042191 := by
    simpa [prefixWord, tailWord_1042191, baseEnd_1042191] using wordTrace_append hprefix tailTrace_1042191
  have hstable : (prefixWord ++ tailWord_1042191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042191).length < 2 ^ (prefixWord ++ tailWord_1042191).sum := by decide
  have hdescent : baseEnd_1042191 < baseStart_1042191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042197 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 7]
def baseStart_1042197 : Nat := 118140960795 + 1042197 * 2 ^ 59
def prefixEnd_1042197 : Nat := 4983230072969 + 3 ^ 40 * 1042197 * 2
def baseEnd_1042197 : Nat := 59460888630440459238281

theorem tailTrace_1042197 : CollatzResearch.WordTrace tailWord_1042197 prefixEnd_1042197 59460888630440459238281 := by
  unfold tailWord_1042197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38012047405305736921956845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25341364936870491281304563 38012047405305736921956845)
  ·
    refine ⟨14254517776989651345733817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38012047405305736921956845 14254517776989651345733817)
    ·
      refine ⟨10690888332742238509300363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14254517776989651345733817 10690888332742238509300363)
      ·
        refine ⟨16036332499113357763950545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10690888332742238509300363 16036332499113357763950545)
        ·
          refine ⟨12027249374335018322962909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16036332499113357763950545 12027249374335018322962909)
          ·
            refine ⟨4510218515375631871111091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12027249374335018322962909 4510218515375631871111091)
            ·
              refine ⟨6765327773063447806666637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510218515375631871111091 6765327773063447806666637)
              ·
                refine ⟨2536997914898792927499989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6765327773063447806666637 2536997914898792927499989)
                ·
                  refine ⟨59460888630440459238281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2536997914898792927499989 59460888630440459238281)
                  ·
                    rfl

theorem cell23_1042197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_1042197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042197 prefixEnd_1042197 := by exact prefixLift 1042197
  have htrace : WordTrace (prefixWord ++ tailWord_1042197) baseStart_1042197 baseEnd_1042197 := by
    simpa [prefixWord, tailWord_1042197, baseEnd_1042197] using wordTrace_append hprefix tailTrace_1042197
  have hstable : (prefixWord ++ tailWord_1042197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042197).length < 2 ^ (prefixWord ++ tailWord_1042197).sum := by decide
  have hdescent : baseEnd_1042197 < baseStart_1042197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042277 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1042277 : Nat := 118140960795 + 1042277 * 2 ^ 59
def prefixEnd_1042277 : Nat := 4983230072969 + 3 ^ 40 * 1042277 * 2
def baseEnd_1042277 : Nat := 535189076126323820144161

theorem tailTrace_1042277 : CollatzResearch.WordTrace tailWord_1042277 prefixEnd_1042277 535189076126323820144161 := by
  unfold tailWord_1042277
  simp only [CollatzResearch.WordTrace]
  refine ⟨38014965245015910584869085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25343310163343940389912723 38014965245015910584869085)
  ·
    refine ⟨14255611966880966469325907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38014965245015910584869085 14255611966880966469325907)
    ·
      refine ⟨21383417950321449703988861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14255611966880966469325907 21383417950321449703988861)
      ·
        refine ⟨8018781731370543638995823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21383417950321449703988861 8018781731370543638995823)
        ·
          refine ⟨12028172597055815458493735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018781731370543638995823 12028172597055815458493735)
          ·
            refine ⟨18042258895583723187740603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028172597055815458493735 18042258895583723187740603)
            ·
              refine ⟨27063388343375584781610905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042258895583723187740603 27063388343375584781610905)
              ·
                refine ⟨20297541257531688586208179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27063388343375584781610905 20297541257531688586208179)
                ·
                  refine ⟨30446311886297532879312269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20297541257531688586208179 30446311886297532879312269)
                  ·
                    refine ⟨11417366957361574829742101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30446311886297532879312269 11417366957361574829742101)
                    ·
                      refine ⟨535189076126323820144161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11417366957361574829742101 535189076126323820144161)
                      ·
                        rfl

theorem cell23_1042277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1042277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042277 prefixEnd_1042277 := by exact prefixLift 1042277
  have htrace : WordTrace (prefixWord ++ tailWord_1042277) baseStart_1042277 baseEnd_1042277 := by
    simpa [prefixWord, tailWord_1042277, baseEnd_1042277] using wordTrace_append hprefix tailTrace_1042277
  have hstable : (prefixWord ++ tailWord_1042277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042277).length < 2 ^ (prefixWord ++ tailWord_1042277).sum := by decide
  have hdescent : baseEnd_1042277 < baseStart_1042277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042291 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 1, 4]
def baseStart_1042291 : Nat := 118140960795 + 1042291 * 2 ^ 59
def prefixEnd_1042291 : Nat := 4983230072969 + 3 ^ 40 * 1042291 * 2
def baseEnd_1042291 : Nat := 178398754951828921789699

theorem tailTrace_1042291 : CollatzResearch.WordTrace tailWord_1042291 prefixEnd_1042291 178398754951828921789699 := by
  unfold tailWord_1042291
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015475866965190975878727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25343650577976793983919151 38015475866965190975878727)
  ·
    refine ⟨57023213800447786463818091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38015475866965190975878727 57023213800447786463818091)
    ·
      refine ⟨85534820700671679695727137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57023213800447786463818091 85534820700671679695727137)
      ·
        refine ⟨64151115525503759771795353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85534820700671679695727137 64151115525503759771795353)
        ·
          refine ⟨48113336644127819828846515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64151115525503759771795353 48113336644127819828846515)
          ·
            refine ⟨72170004966191729743269773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48113336644127819828846515 72170004966191729743269773)
            ·
              refine ⟨27063751862321898653726165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72170004966191729743269773 27063751862321898653726165)
              ·
                refine ⟨634306684273169499696707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27063751862321898653726165 634306684273169499696707)
                ·
                  refine ⟨951460026409754249545061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634306684273169499696707 951460026409754249545061)
                  ·
                    refine ⟨178398754951828921789699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 951460026409754249545061 178398754951828921789699)
                    ·
                      rfl

theorem cell23_1042291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 4].length) (baseStart_1042291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042291 prefixEnd_1042291 := by exact prefixLift 1042291
  have htrace : WordTrace (prefixWord ++ tailWord_1042291) baseStart_1042291 baseEnd_1042291 := by
    simpa [prefixWord, tailWord_1042291, baseEnd_1042291] using wordTrace_append hprefix tailTrace_1042291
  have hstable : (prefixWord ++ tailWord_1042291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042291).length < 2 ^ (prefixWord ++ tailWord_1042291).sum := by decide
  have hdescent : baseEnd_1042291 < baseStart_1042291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042304 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 6]
def baseStart_1042304 : Nat := 118140960795 + 1042304 * 2 ^ 59
def prefixEnd_1042304 : Nat := 4983230072969 + 3 ^ 40 * 1042304 * 2
def baseEnd_1042304 : Nat := 59466993344888357167393

theorem tailTrace_1042304 : CollatzResearch.WordTrace tailWord_1042304 prefixEnd_1042304 59466993344888357167393 := by
  unfold tailWord_1042304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007975007959047098050983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25343966677278729464067977 19007975007959047098050983)
  ·
    refine ⟨28511962511938570647076475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19007975007959047098050983 28511962511938570647076475)
    ·
      refine ⟨42767943767907855970614713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28511962511938570647076475 42767943767907855970614713)
      ·
        refine ⟨32075957825930891977961035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42767943767907855970614713 32075957825930891977961035)
        ·
          refine ⟨48113936738896337966941553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32075957825930891977961035 48113936738896337966941553)
          ·
            refine ⟨36085452554172253475206165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48113936738896337966941553 36085452554172253475206165)
            ·
              refine ⟨1691505588476824381650289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36085452554172253475206165 1691505588476824381650289)
              ·
                refine ⟨1268629191357618286237717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691505588476824381650289 1268629191357618286237717)
                ·
                  refine ⟨59466993344888357167393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1268629191357618286237717 59466993344888357167393)
                  ·
                    rfl

theorem cell23_1042304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_1042304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042304 prefixEnd_1042304 := by exact prefixLift 1042304
  have htrace : WordTrace (prefixWord ++ tailWord_1042304) baseStart_1042304 baseEnd_1042304 := by
    simpa [prefixWord, tailWord_1042304, baseEnd_1042304] using wordTrace_append hprefix tailTrace_1042304
  have hstable : (prefixWord ++ tailWord_1042304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042304).length < 2 ^ (prefixWord ++ tailWord_1042304).sum := by decide
  have hdescent : baseEnd_1042304 < baseStart_1042304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042335 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1042335 : Nat := 118140960795 + 1042335 * 2 ^ 59
def prefixEnd_1042335 : Nat := 4983230072969 + 3 ^ 40 * 1042335 * 2
def baseEnd_1042335 : Nat := 535218858004284593218895

theorem tailTrace_1042335 : CollatzResearch.WordTrace tailWord_1042335 prefixEnd_1042335 535218858004284593218895 := by
  unfold tailWord_1042335
  simp only [CollatzResearch.WordTrace]
  refine ⟨38017080678805786490480459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25344720452537190993653639 38017080678805786490480459)
  ·
    refine ⟨57025621018208679735720689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38017080678805786490480459 57025621018208679735720689)
    ·
      refine ⟨42769215763656509801790517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57025621018208679735720689 42769215763656509801790517)
      ·
        refine ⟨4009613977842797793917861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42769215763656509801790517 4009613977842797793917861)
        ·
          refine ⟨751802620845524586359599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4009613977842797793917861 751802620845524586359599)
          ·
            refine ⟨1127703931268286879539399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751802620845524586359599 1127703931268286879539399)
            ·
              refine ⟨1691555896902430319309099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127703931268286879539399 1691555896902430319309099)
              ·
                refine ⟨2537333845353645478963649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691555896902430319309099 2537333845353645478963649)
                ·
                  refine ⟨1903000384015234109222737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537333845353645478963649 1903000384015234109222737)
                  ·
                    refine ⟨1427250288011425581917053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903000384015234109222737 1427250288011425581917053)
                    ·
                      refine ⟨535218858004284593218895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1427250288011425581917053 535218858004284593218895)
                      ·
                        rfl

theorem cell23_1042335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1042335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042335 prefixEnd_1042335 := by exact prefixLift 1042335
  have htrace : WordTrace (prefixWord ++ tailWord_1042335) baseStart_1042335 baseEnd_1042335 := by
    simpa [prefixWord, tailWord_1042335, baseEnd_1042335] using wordTrace_append hprefix tailTrace_1042335
  have hstable : (prefixWord ++ tailWord_1042335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042335).length < 2 ^ (prefixWord ++ tailWord_1042335).sum := by decide
  have hdescent : baseEnd_1042335 < baseStart_1042335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042365 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_1042365 : Nat := 118140960795 + 1042365 * 2 ^ 59
def prefixEnd_1042365 : Nat := 4983230072969 + 3 ^ 40 * 1042365 * 2
def baseEnd_1042365 : Nat := 535234262423919475843757

theorem tailTrace_1042365 : CollatzResearch.WordTrace tailWord_1042365 prefixEnd_1042365 535234262423919475843757 := by
  unfold tailWord_1042365
  simp only [CollatzResearch.WordTrace]
  refine ⟨38018174868697101614072549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25345449912464734409381699 38018174868697101614072549)
  ·
    refine ⟨7128407787880706552638603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38018174868697101614072549 7128407787880706552638603)
    ·
      refine ⟨10692611681821059828957905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128407787880706552638603 10692611681821059828957905)
      ·
        refine ⟨8019458761365794871718429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10692611681821059828957905 8019458761365794871718429)
        ·
          refine ⟨3007297035512173076894411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8019458761365794871718429 3007297035512173076894411)
          ·
            refine ⟨4510945553268259615341617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007297035512173076894411 4510945553268259615341617)
            ·
              refine ⟨3383209164951194711506213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510945553268259615341617 3383209164951194711506213)
              ·
                refine ⟨634351718428349008407415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383209164951194711506213 634351718428349008407415)
                ·
                  refine ⟨951527577642523512611123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634351718428349008407415 951527577642523512611123)
                  ·
                    refine ⟨1427291366463785268916685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 951527577642523512611123 1427291366463785268916685)
                    ·
                      refine ⟨535234262423919475843757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1427291366463785268916685 535234262423919475843757)
                      ·
                        rfl

theorem cell23_1042365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_1042365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042365 prefixEnd_1042365 := by exact prefixLift 1042365
  have htrace : WordTrace (prefixWord ++ tailWord_1042365) baseStart_1042365 baseEnd_1042365 := by
    simpa [prefixWord, tailWord_1042365, baseEnd_1042365] using wordTrace_append hprefix tailTrace_1042365
  have hstable : (prefixWord ++ tailWord_1042365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042365).length < 2 ^ (prefixWord ++ tailWord_1042365).sum := by decide
  have hdescent : baseEnd_1042365 < baseStart_1042365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042388 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1042388 : Nat := 118140960795 + 1042388 * 2 ^ 59
def prefixEnd_1042388 : Nat := 4983230072969 + 3 ^ 40 * 1042388 * 2
def baseEnd_1042388 : Nat := 535246072478972885856151

theorem tailTrace_1042388 : CollatzResearch.WordTrace tailWord_1042388 prefixEnd_1042388 535246072478972885856151 := by
  unfold tailWord_1042388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009506873806888271079909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25346009165075851028106545 19009506873806888271079909)
  ·
    refine ⟨3564282538838791550827483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19009506873806888271079909 3564282538838791550827483)
    ·
      refine ⟨5346423808258187326241225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564282538838791550827483 5346423808258187326241225)
      ·
        refine ⟨4009817856193640494680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5346423808258187326241225 4009817856193640494680919)
        ·
          refine ⟨6014726784290460742021379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009817856193640494680919 6014726784290460742021379)
          ·
            refine ⟨9022090176435691113032069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014726784290460742021379 9022090176435691113032069)
            ·
              refine ⟨1691641908081692083693513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9022090176435691113032069 1691641908081692083693513)
              ·
                refine ⟨1268731431061269062770135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691641908081692083693513 1268731431061269062770135)
                ·
                  refine ⟨1903097146591903594155203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268731431061269062770135 1903097146591903594155203)
                  ·
                    refine ⟨2854645719887855391232805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903097146591903594155203 2854645719887855391232805)
                    ·
                      refine ⟨535246072478972885856151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2854645719887855391232805 535246072478972885856151)
                      ·
                        rfl

theorem cell23_1042388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1042388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042388 prefixEnd_1042388 := by exact prefixLift 1042388
  have htrace : WordTrace (prefixWord ++ tailWord_1042388) baseStart_1042388 baseEnd_1042388 := by
    simpa [prefixWord, tailWord_1042388, baseEnd_1042388] using wordTrace_append hprefix tailTrace_1042388
  have hstable : (prefixWord ++ tailWord_1042388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042388).length < 2 ^ (prefixWord ++ tailWord_1042388).sum := by decide
  have hdescent : baseEnd_1042388 < baseStart_1042388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042442 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_1042442 : Nat := 118140960795 + 1042442 * 2 ^ 59
def prefixEnd_1042442 : Nat := 4983230072969 + 3 ^ 40 * 1042442 * 2
def baseEnd_1042442 : Nat := 535273800434315674580903

theorem tailTrace_1042442 : CollatzResearch.WordTrace tailWord_1042442 prefixEnd_1042442 535273800434315674580903 := by
  unfold tailWord_1042442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9505245822354535941156395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25347322192945429176417053 9505245822354535941156395)
  ·
    refine ⟨14257868733531803911734593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9505245822354535941156395 14257868733531803911734593)
    ·
      refine ⟨10693401550148852933800945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14257868733531803911734593 10693401550148852933800945)
      ·
        refine ⟨8020051162611639700350709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10693401550148852933800945 8020051162611639700350709)
        ·
          refine ⟨751879796494841221907879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8020051162611639700350709 751879796494841221907879)
          ·
            refine ⟨1127819694742261832861819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751879796494841221907879 1127819694742261832861819)
            ·
              refine ⟨1691729542113392749292729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127819694742261832861819 1691729542113392749292729)
              ·
                refine ⟨1268797156585044561969547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691729542113392749292729 1268797156585044561969547)
                ·
                  refine ⟨1903195734877566842954321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1268797156585044561969547 1903195734877566842954321)
                  ·
                    refine ⟨1427396801158175132215741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903195734877566842954321 1427396801158175132215741)
                    ·
                      refine ⟨535273800434315674580903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1427396801158175132215741 535273800434315674580903)
                      ·
                        rfl

theorem cell23_1042442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_1042442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042442 prefixEnd_1042442 := by exact prefixLift 1042442
  have htrace : WordTrace (prefixWord ++ tailWord_1042442) baseStart_1042442 baseEnd_1042442 := by
    simpa [prefixWord, tailWord_1042442, baseEnd_1042442] using wordTrace_append hprefix tailTrace_1042442
  have hstable : (prefixWord ++ tailWord_1042442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042442).length < 2 ^ (prefixWord ++ tailWord_1042442).sum := by decide
  have hdescent : baseEnd_1042442 < baseStart_1042442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042481 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1042481 : Nat := 118140960795 + 1042481 * 2 ^ 59
def prefixEnd_1042481 : Nat := 4983230072969 + 3 ^ 40 * 1042481 * 2
def baseEnd_1042481 : Nat := 535293826179841021993223

theorem tailTrace_1042481 : CollatzResearch.WordTrace tailWord_1042481 prefixEnd_1042481 535293826179841021993223 := by
  unfold tailWord_1042481
  simp only [CollatzResearch.WordTrace]
  refine ⟨38022405736276853425295297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25348270490851235616863531 38022405736276853425295297)
  ·
    refine ⟨28516804302207640068971473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38022405736276853425295297 28516804302207640068971473)
    ·
      refine ⟨21387603226655730051728605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28516804302207640068971473 21387603226655730051728605)
      ·
        refine ⟨8020351209995898769398227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21387603226655730051728605 8020351209995898769398227)
        ·
          refine ⟨12030526814993848154097341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020351209995898769398227 12030526814993848154097341)
          ·
            refine ⟨4511447555622693057786503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12030526814993848154097341 4511447555622693057786503)
            ·
              refine ⟨6767171333434039586679755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511447555622693057786503 6767171333434039586679755)
              ·
                refine ⟨10150757000151059380019633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767171333434039586679755 10150757000151059380019633)
                ·
                  refine ⟨7613067750113294535014725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10150757000151059380019633 7613067750113294535014725)
                  ·
                    refine ⟨1427450203146242725315261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7613067750113294535014725 1427450203146242725315261)
                    ·
                      refine ⟨535293826179841021993223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1427450203146242725315261 535293826179841021993223)
                      ·
                        rfl

theorem cell23_1042481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1042481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042481 prefixEnd_1042481 := by exact prefixLift 1042481
  have htrace : WordTrace (prefixWord ++ tailWord_1042481) baseStart_1042481 baseEnd_1042481 := by
    simpa [prefixWord, tailWord_1042481, baseEnd_1042481] using wordTrace_append hprefix tailTrace_1042481
  have hstable : (prefixWord ++ tailWord_1042481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042481).length < 2 ^ (prefixWord ++ tailWord_1042481).sum := by decide
  have hdescent : baseEnd_1042481 < baseStart_1042481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042495 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 2, 2, 2]
def baseStart_1042495 : Nat := 118140960795 + 1042495 * 2 ^ 59
def prefixEnd_1042495 : Nat := 4983230072969 + 3 ^ 40 * 1042495 * 2
def baseEnd_1042495 : Nat := 535301014909003967218159

theorem tailTrace_1042495 : CollatzResearch.WordTrace tailWord_1042495 prefixEnd_1042495 535301014909003967218159 := by
  unfold tailWord_1042495
  simp only [CollatzResearch.WordTrace]
  refine ⟨38022916358226133816304939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25348610905484089210869959 38022916358226133816304939)
  ·
    refine ⟨57034374537339200724457409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38022916358226133816304939 57034374537339200724457409)
    ·
      refine ⟨42775780903004400543343057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57034374537339200724457409 42775780903004400543343057)
      ·
        refine ⟨32081835677253300407507293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42775780903004400543343057 32081835677253300407507293)
        ·
          refine ⟨12030688378969987652815235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32081835677253300407507293 12030688378969987652815235)
          ·
            refine ⟨18046032568454981479222853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030688378969987652815235 18046032568454981479222853)
            ·
              refine ⟨3383631106585309027354285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18046032568454981479222853 3383631106585309027354285)
              ·
                refine ⟨1268861664969490885257857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3383631106585309027354285 1268861664969490885257857)
                ·
                  refine ⟨951646248727118163943393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1268861664969490885257857 951646248727118163943393)
                  ·
                    refine ⟨713734686545338622957545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951646248727118163943393 713734686545338622957545)
                    ·
                      refine ⟨535301014909003967218159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713734686545338622957545 535301014909003967218159)
                      ·
                        rfl

theorem cell23_1042495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_1042495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042495 prefixEnd_1042495 := by exact prefixLift 1042495
  have htrace : WordTrace (prefixWord ++ tailWord_1042495) baseStart_1042495 baseEnd_1042495 := by
    simpa [prefixWord, tailWord_1042495, baseEnd_1042495] using wordTrace_append hprefix tailTrace_1042495
  have hstable : (prefixWord ++ tailWord_1042495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042495).length < 2 ^ (prefixWord ++ tailWord_1042495).sum := by decide
  have hdescent : baseEnd_1042495 < baseStart_1042495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042531 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 2, 5]
def baseStart_1042531 : Nat := 118140960795 + 1042531 * 2 ^ 59
def prefixEnd_1042531 : Nat := 4983230072969 + 3 ^ 40 * 1042531 * 2
def baseEnd_1042531 : Nat := 178439833404188608789331

theorem tailTrace_1042531 : CollatzResearch.WordTrace tailWord_1042531 prefixEnd_1042531 178439833404188608789331 := by
  unfold tailWord_1042531
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024229386095711964615447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25349486257397141309743631 38024229386095711964615447)
  ·
    refine ⟨57036344079143567946923171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38024229386095711964615447 57036344079143567946923171)
    ·
      refine ⟨85554516118715351920384757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57036344079143567946923171 85554516118715351920384757)
      ·
        refine ⟨8020735886129564242536071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85554516118715351920384757 8020735886129564242536071)
        ·
          refine ⟨12031103829194346363804107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8020735886129564242536071 12031103829194346363804107)
          ·
            refine ⟨18046655743791519545706161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12031103829194346363804107 18046655743791519545706161)
            ·
              refine ⟨13534991807843639659279621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18046655743791519545706161 13534991807843639659279621)
              ·
                refine ⟨2537810963970682436114929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13534991807843639659279621 2537810963970682436114929)
                ·
                  refine ⟨1903358222978011827086197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2537810963970682436114929 1903358222978011827086197)
                  ·
                    refine ⟨178439833404188608789331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1903358222978011827086197 178439833404188608789331)
                    ·
                      rfl

theorem cell23_1042531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 5].length) (baseStart_1042531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042531 prefixEnd_1042531 := by exact prefixLift 1042531
  have htrace : WordTrace (prefixWord ++ tailWord_1042531) baseStart_1042531 baseEnd_1042531 := by
    simpa [prefixWord, tailWord_1042531, baseEnd_1042531] using wordTrace_append hprefix tailTrace_1042531
  have hstable : (prefixWord ++ tailWord_1042531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042531).length < 2 ^ (prefixWord ++ tailWord_1042531).sum := by decide
  have hdescent : baseEnd_1042531 < baseStart_1042531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042541 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1042541 : Nat := 118140960795 + 1042541 * 2 ^ 59
def prefixEnd_1042541 : Nat := 4983230072969 + 3 ^ 40 * 1042541 * 2
def baseEnd_1042541 : Nat := 535324635019110787242947

theorem tailTrace_1042541 : CollatzResearch.WordTrace tailWord_1042541 prefixEnd_1042541 535324635019110787242947 := by
  unfold tailWord_1042541
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024594116059483672479477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25349729410706322448319651 38024594116059483672479477)
  ·
    refine ⟨3564805698380576594294951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38024594116059483672479477 3564805698380576594294951)
    ·
      refine ⟨5347208547570864891442427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564805698380576594294951 5347208547570864891442427)
      ·
        refine ⟨8020812821356297337163641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347208547570864891442427 8020812821356297337163641)
        ·
          refine ⟨6015609616017223002872731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8020812821356297337163641 6015609616017223002872731)
          ·
            refine ⟨9023414424025834504309097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015609616017223002872731 9023414424025834504309097)
            ·
              refine ⟨6767560818019375878231823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023414424025834504309097 6767560818019375878231823)
              ·
                refine ⟨10151341227029063817347735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767560818019375878231823 10151341227029063817347735)
                ·
                  refine ⟨15227011840543595726021603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151341227029063817347735 15227011840543595726021603)
                  ·
                    refine ⟨22840517760815393589032405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15227011840543595726021603 22840517760815393589032405)
                    ·
                      refine ⟨535324635019110787242947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22840517760815393589032405 535324635019110787242947)
                      ·
                        rfl

theorem cell23_1042541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1042541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042541 prefixEnd_1042541 := by exact prefixLift 1042541
  have htrace : WordTrace (prefixWord ++ tailWord_1042541) baseStart_1042541 baseEnd_1042541 := by
    simpa [prefixWord, tailWord_1042541, baseEnd_1042541] using wordTrace_append hprefix tailTrace_1042541
  have hstable : (prefixWord ++ tailWord_1042541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042541).length < 2 ^ (prefixWord ++ tailWord_1042541).sum := by decide
  have hdescent : baseEnd_1042541 < baseStart_1042541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042551 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1042551 : Nat := 118140960795 + 1042551 * 2 ^ 59
def prefixEnd_1042551 : Nat := 4983230072969 + 3 ^ 40 * 1042551 * 2
def baseEnd_1042551 : Nat := 535329769825655748117901

theorem tailTrace_1042551 : CollatzResearch.WordTrace tailWord_1042551 prefixEnd_1042551 535329769825655748117901 := by
  unfold tailWord_1042551
  simp only [CollatzResearch.WordTrace]
  refine ⟨38024958846023255380343507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25349972564015503586895671 38024958846023255380343507)
  ·
    refine ⟨57037438269034883070515261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38024958846023255380343507 57037438269034883070515261)
    ·
      refine ⟨21389039350888081151443223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57037438269034883070515261 21389039350888081151443223)
      ·
        refine ⟨32083559026332121727164835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389039350888081151443223 32083559026332121727164835)
        ·
          refine ⟨48125338539498182590747253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32083559026332121727164835 48125338539498182590747253)
          ·
            refine ⟨4511750488077954617882555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48125338539498182590747253 4511750488077954617882555)
            ·
              refine ⟨6767625732116931926823833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511750488077954617882555 6767625732116931926823833)
              ·
                refine ⟨5075719299087698945117875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6767625732116931926823833 5075719299087698945117875)
                ·
                  refine ⟨7613578948631548417676813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075719299087698945117875 7613578948631548417676813)
                  ·
                    refine ⟨2855092105736830656628805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7613578948631548417676813 2855092105736830656628805)
                    ·
                      refine ⟨535329769825655748117901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2855092105736830656628805 535329769825655748117901)
                      ·
                        rfl

theorem cell23_1042551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1042551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042551 prefixEnd_1042551 := by exact prefixLift 1042551
  have htrace : WordTrace (prefixWord ++ tailWord_1042551) baseStart_1042551 baseEnd_1042551 := by
    simpa [prefixWord, tailWord_1042551, baseEnd_1042551] using wordTrace_append hprefix tailTrace_1042551
  have hstable : (prefixWord ++ tailWord_1042551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042551).length < 2 ^ (prefixWord ++ tailWord_1042551).sum := by decide
  have hdescent : baseEnd_1042551 < baseStart_1042551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042568 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1042568 : Nat := 118140960795 + 1042568 * 2 ^ 59
def prefixEnd_1042568 : Nat := 4983230072969 + 3 ^ 40 * 1042568 * 2
def baseEnd_1042568 : Nat := 535338498996782181605323

theorem tailTrace_1042568 : CollatzResearch.WordTrace tailWord_1042568 prefixEnd_1042568 535338498996782181605323 := by
  unfold tailWord_1042568
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012789443480833641856179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25350385924641111522474905 19012789443480833641856179)
  ·
    refine ⟨28519184165221250462784269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19012789443480833641856179 28519184165221250462784269)
    ·
      refine ⟨10694694061957968923544101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28519184165221250462784269 10694694061957968923544101)
      ·
        refine ⟨2005255136617119173164519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10694694061957968923544101 2005255136617119173164519)
        ·
          refine ⟨3007882704925678759746779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005255136617119173164519 3007882704925678759746779)
          ·
            refine ⟨4511824057388518139620169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007882704925678759746779 4511824057388518139620169)
            ·
              refine ⟨3383868043041388604715127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511824057388518139620169 3383868043041388604715127)
              ·
                refine ⟨5075802064562082907072691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383868043041388604715127 5075802064562082907072691)
                ·
                  refine ⟨7613703096843124360609037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075802064562082907072691 7613703096843124360609037)
                  ·
                    refine ⟨2855138661316171635228389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7613703096843124360609037 2855138661316171635228389)
                    ·
                      refine ⟨535338498996782181605323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2855138661316171635228389 535338498996782181605323)
                      ·
                        rfl

theorem cell23_1042568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1042568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042568 prefixEnd_1042568 := by exact prefixLift 1042568
  have htrace : WordTrace (prefixWord ++ tailWord_1042568) baseStart_1042568 baseEnd_1042568 := by
    simpa [prefixWord, tailWord_1042568, baseEnd_1042568] using wordTrace_append hprefix tailTrace_1042568
  have hstable : (prefixWord ++ tailWord_1042568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042568).length < 2 ^ (prefixWord ++ tailWord_1042568).sum := by decide
  have hdescent : baseEnd_1042568 < baseStart_1042568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042622 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1042622 : Nat := 118140960795 + 1042622 * 2 ^ 59
def prefixEnd_1042622 : Nat := 4983230072969 + 3 ^ 40 * 1042622 * 2
def baseEnd_1042622 : Nat := 535366226952124970330075

theorem tailTrace_1042622 : CollatzResearch.WordTrace tailWord_1042622 prefixEnd_1042622 535366226952124970330075 := by
  unfold tailWord_1042622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753443553595754313272265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25351698952510689670785413 4753443553595754313272265)
  ·
    refine ⟨3565082665196815734954199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4753443553595754313272265 3565082665196815734954199)
    ·
      refine ⟨5347623997795223602431299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565082665196815734954199 5347623997795223602431299)
      ·
        refine ⟨8021435996692835403646949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347623997795223602431299 8021435996692835403646949)
        ·
          refine ⟨1504019249379906638183803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8021435996692835403646949 1504019249379906638183803)
          ·
            refine ⟨2256028874069859957275705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504019249379906638183803 2256028874069859957275705)
            ·
              refine ⟨1692021655552394967956779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256028874069859957275705 1692021655552394967956779)
              ·
                refine ⟨2538032483328592451935169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692021655552394967956779 2538032483328592451935169)
                ·
                  refine ⟨1903524362496444338951377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2538032483328592451935169 1903524362496444338951377)
                  ·
                    refine ⟨1427643271872333254213533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1903524362496444338951377 1427643271872333254213533)
                    ·
                      refine ⟨535366226952124970330075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1427643271872333254213533 535366226952124970330075)
                      ·
                        rfl

theorem cell23_1042622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1042622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042622 prefixEnd_1042622 := by exact prefixLift 1042622
  have htrace : WordTrace (prefixWord ++ tailWord_1042622) baseStart_1042622 baseEnd_1042622 := by
    simpa [prefixWord, tailWord_1042622, baseEnd_1042622] using wordTrace_append hprefix tailTrace_1042622
  have hstable : (prefixWord ++ tailWord_1042622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042622).length < 2 ^ (prefixWord ++ tailWord_1042622).sum := by decide
  have hdescent : baseEnd_1042622 < baseStart_1042622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042646 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1042646 : Nat := 118140960795 + 1042646 * 2 ^ 59
def prefixEnd_1042646 : Nat := 4983230072969 + 3 ^ 40 * 1042646 * 2
def baseEnd_1042646 : Nat := 178459516829277625476655

theorem tailTrace_1042646 : CollatzResearch.WordTrace tailWord_1042646 prefixEnd_1042646 178459516829277625476655 := by
  unfold tailWord_1042646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376776486292442912815737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25352282520452724403367861 2376776486292442912815737)
  ·
    refine ⟨1782582364719332184611803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2376776486292442912815737 1782582364719332184611803)
    ·
      refine ⟨2673873547078998276917705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782582364719332184611803 2673873547078998276917705)
      ·
        refine ⟨2005405160309248707688279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673873547078998276917705 2005405160309248707688279)
        ·
          refine ⟨3008107740463873061532419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005405160309248707688279 3008107740463873061532419)
          ·
            refine ⟨4512161610695809592298629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008107740463873061532419 4512161610695809592298629)
            ·
              refine ⟨846030302005464298555993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4512161610695809592298629 846030302005464298555993)
              ·
                refine ⟨634522726504098223916995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846030302005464298555993 634522726504098223916995)
                ·
                  refine ⟨951784089756147335875493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634522726504098223916995 951784089756147335875493)
                  ·
                    refine ⟨178459516829277625476655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 951784089756147335875493 178459516829277625476655)
                    ·
                      rfl

theorem cell23_1042646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1042646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042646 prefixEnd_1042646 := by exact prefixLift 1042646
  have htrace : WordTrace (prefixWord ++ tailWord_1042646) baseStart_1042646 baseEnd_1042646 := by
    simpa [prefixWord, tailWord_1042646, baseEnd_1042646] using wordTrace_append hprefix tailTrace_1042646
  have hstable : (prefixWord ++ tailWord_1042646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042646).length < 2 ^ (prefixWord ++ tailWord_1042646).sum := by decide
  have hdescent : baseEnd_1042646 < baseStart_1042646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042668 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_1042668 : Nat := 118140960795 + 1042668 * 2 ^ 59
def prefixEnd_1042668 : Nat := 4983230072969 + 3 ^ 40 * 1042668 * 2
def baseEnd_1042668 : Nat := 178463282354077263451621

theorem tailTrace_1042668 : CollatzResearch.WordTrace tailWord_1042668 prefixEnd_1042668 178463282354077263451621 := by
  unfold tailWord_1042668
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014613093299692181176329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25352817457732922908235105 19014613093299692181176329)
  ·
    refine ⟨14260959819974769135882247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19014613093299692181176329 14260959819974769135882247)
    ·
      refine ⟨21391439729962153703823371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14260959819974769135882247 21391439729962153703823371)
      ·
        refine ⟨32087159594943230555735057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21391439729962153703823371 32087159594943230555735057)
        ·
          refine ⟨24065369696207422916801293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32087159594943230555735057 24065369696207422916801293)
          ·
            refine ⟨9024513636077783593800485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24065369696207422916801293 9024513636077783593800485)
            ·
              refine ⟨1692096306764584423837591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9024513636077783593800485 1692096306764584423837591)
              ·
                refine ⟨2538144460146876635756387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692096306764584423837591 2538144460146876635756387)
                ·
                  refine ⟨3807216690220314953634581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538144460146876635756387 3807216690220314953634581)
                  ·
                    refine ⟨178463282354077263451621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3807216690220314953634581 178463282354077263451621)
                    ·
                      rfl

theorem cell23_1042668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_1042668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042668 prefixEnd_1042668 := by exact prefixLift 1042668
  have htrace : WordTrace (prefixWord ++ tailWord_1042668) baseStart_1042668 baseEnd_1042668 := by
    simpa [prefixWord, tailWord_1042668, baseEnd_1042668] using wordTrace_append hprefix tailTrace_1042668
  have hstable : (prefixWord ++ tailWord_1042668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042668).length < 2 ^ (prefixWord ++ tailWord_1042668).sum := by decide
  have hdescent : baseEnd_1042668 < baseStart_1042668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042688 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_1042688 : Nat := 118140960795 + 1042688 * 2 ^ 59
def prefixEnd_1042688 : Nat := 4983230072969 + 3 ^ 40 * 1042688 * 2
def baseEnd_1042688 : Nat := 535400116675321712104771

theorem tailTrace_1042688 : CollatzResearch.WordTrace tailWord_1042688 prefixEnd_1042688 535400116675321712104771 := by
  unfold tailWord_1042688
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014977823263463889040359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25353303764351285185387145 19014977823263463889040359)
  ·
    refine ⟨28522466734895195833560539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014977823263463889040359 28522466734895195833560539)
    ·
      refine ⟨42783700102342793750340809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28522466734895195833560539 42783700102342793750340809)
      ·
        refine ⟨32087775076757095312755607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42783700102342793750340809 32087775076757095312755607)
        ·
          refine ⟨48131662615135642969133411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32087775076757095312755607 48131662615135642969133411)
          ·
            refine ⟨72197493922703464453700117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48131662615135642969133411 72197493922703464453700117)
            ·
              refine ⟨3384257527626724896267193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72197493922703464453700117 3384257527626724896267193)
              ·
                refine ⟨2538193145720043672200395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384257527626724896267193 2538193145720043672200395)
                ·
                  refine ⟨3807289718580065508300593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538193145720043672200395 3807289718580065508300593)
                  ·
                    refine ⟨2855467288935049131225445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807289718580065508300593 2855467288935049131225445)
                    ·
                      refine ⟨535400116675321712104771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2855467288935049131225445 535400116675321712104771)
                      ·
                        rfl

theorem cell23_1042688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_1042688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042688 prefixEnd_1042688 := by exact prefixLift 1042688
  have htrace : WordTrace (prefixWord ++ tailWord_1042688) baseStart_1042688 baseEnd_1042688 := by
    simpa [prefixWord, tailWord_1042688, baseEnd_1042688] using wordTrace_append hprefix tailTrace_1042688
  have hstable : (prefixWord ++ tailWord_1042688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042688).length < 2 ^ (prefixWord ++ tailWord_1042688).sum := by decide
  have hdescent : baseEnd_1042688 < baseStart_1042688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042692 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1042692 : Nat := 118140960795 + 1042692 * 2 ^ 59
def prefixEnd_1042692 : Nat := 4983230072969 + 3 ^ 40 * 1042692 * 2
def baseEnd_1042692 : Nat := 535402170597939696454753

theorem tailTrace_1042692 : CollatzResearch.WordTrace tailWord_1042692 prefixEnd_1042692 535402170597939696454753 := by
  unfold tailWord_1042692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015050769256218230613165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25353401025674957640817553 19015050769256218230613165)
  ·
    refine ⟨7130644038471081836479937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19015050769256218230613165 7130644038471081836479937)
    ·
      refine ⟨5347983028853311377359953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7130644038471081836479937 5347983028853311377359953)
      ·
        refine ⟨4010987271639983533019965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5347983028853311377359953 4010987271639983533019965)
        ·
          refine ⟨1504120226864993824882487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4010987271639983533019965 1504120226864993824882487)
          ·
            refine ⟨2256180340297490737323731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504120226864993824882487 2256180340297490737323731)
            ·
              refine ⟨3384270510446236105985597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256180340297490737323731 3384270510446236105985597)
              ·
                refine ⟨1269101441417338539744599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3384270510446236105985597 1269101441417338539744599)
                ·
                  refine ⟨1903652162126007809616899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269101441417338539744599 1903652162126007809616899)
                  ·
                    refine ⟨2855478243189011714425349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1903652162126007809616899 2855478243189011714425349)
                    ·
                      refine ⟨535402170597939696454753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2855478243189011714425349 535402170597939696454753)
                      ·
                        rfl

theorem cell23_1042692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1042692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042692 prefixEnd_1042692 := by exact prefixLift 1042692
  have htrace : WordTrace (prefixWord ++ tailWord_1042692) baseStart_1042692 baseEnd_1042692 := by
    simpa [prefixWord, tailWord_1042692, baseEnd_1042692] using wordTrace_append hprefix tailTrace_1042692
  have hstable : (prefixWord ++ tailWord_1042692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042692).length < 2 ^ (prefixWord ++ tailWord_1042692).sum := by decide
  have hdescent : baseEnd_1042692 < baseStart_1042692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042709 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_1042709 : Nat := 118140960795 + 1042709 * 2 ^ 59
def prefixEnd_1042709 : Nat := 4983230072969 + 3 ^ 40 * 1042709 * 2
def baseEnd_1042709 : Nat := 535410899769066129942175

theorem tailTrace_1042709 : CollatzResearch.WordTrace tailWord_1042709 prefixEnd_1042709 535410899769066129942175 := by
  unfold tailWord_1042709
  simp only [CollatzResearch.WordTrace]
  refine ⟨38030721579450848364595181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25353814386300565576396787 38030721579450848364595181)
  ·
    refine ⟨14261520592294068136723193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38030721579450848364595181 14261520592294068136723193)
    ·
      refine ⟨10696140444220551102542395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14261520592294068136723193 10696140444220551102542395)
      ·
        refine ⟨16044210666330826653813593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696140444220551102542395 16044210666330826653813593)
        ·
          refine ⟨12033157999748119990360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16044210666330826653813593 12033157999748119990360195)
          ·
            refine ⟨18049736999622179985540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033157999748119990360195 18049736999622179985540293)
            ·
              refine ⟨3384325687429158747288805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18049736999622179985540293 3384325687429158747288805)
              ·
                refine ⟨634561066392967265116651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3384325687429158747288805 634561066392967265116651)
                ·
                  refine ⟨951841599589450897674977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634561066392967265116651 951841599589450897674977)
                  ·
                    refine ⟨713881199692088173256233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 951841599589450897674977 713881199692088173256233)
                    ·
                      refine ⟨535410899769066129942175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713881199692088173256233 535410899769066129942175)
                      ·
                        rfl

theorem cell23_1042709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_1042709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042709 prefixEnd_1042709 := by exact prefixLift 1042709
  have htrace : WordTrace (prefixWord ++ tailWord_1042709) baseStart_1042709 baseEnd_1042709 := by
    simpa [prefixWord, tailWord_1042709, baseEnd_1042709] using wordTrace_append hprefix tailTrace_1042709
  have hstable : (prefixWord ++ tailWord_1042709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042709).length < 2 ^ (prefixWord ++ tailWord_1042709).sum := by decide
  have hdescent : baseEnd_1042709 < baseStart_1042709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042722 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1042722 : Nat := 118140960795 + 1042722 * 2 ^ 59
def prefixEnd_1042722 : Nat := 4983230072969 + 3 ^ 40 * 1042722 * 2
def baseEnd_1042722 : Nat := 535417575017574579079615

theorem tailTrace_1042722 : CollatzResearch.WordTrace tailWord_1042722 prefixEnd_1042722 535417575017574579079615 := by
  unfold tailWord_1042722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507798932100937896204605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25354130485602501056545613 9507798932100937896204605)
  ·
    refine ⟨3565424599537851711076727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9507798932100937896204605 3565424599537851711076727)
    ·
      refine ⟨5348136899306777566615091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565424599537851711076727 5348136899306777566615091)
      ·
        refine ⟨8022205348960166349922637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348136899306777566615091 8022205348960166349922637)
        ·
          refine ⟨3008327005860062381220989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8022205348960166349922637 3008327005860062381220989)
          ·
            refine ⟨1128122627197523392957871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3008327005860062381220989 1128122627197523392957871)
            ·
              refine ⟨1692183940796285089436807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128122627197523392957871 1692183940796285089436807)
              ·
                refine ⟨2538275911194427634155211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692183940796285089436807 2538275911194427634155211)
                ·
                  refine ⟨3807413866791641451232817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538275911194427634155211 3807413866791641451232817)
                  ·
                    refine ⟨2855560400093731088424613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807413866791641451232817 2855560400093731088424613)
                    ·
                      refine ⟨535417575017574579079615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2855560400093731088424613 535417575017574579079615)
                      ·
                        rfl

theorem cell23_1042722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1042722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042722 prefixEnd_1042722 := by exact prefixLift 1042722
  have htrace : WordTrace (prefixWord ++ tailWord_1042722) baseStart_1042722 baseEnd_1042722 := by
    simpa [prefixWord, tailWord_1042722, baseEnd_1042722] using wordTrace_append hprefix tailTrace_1042722
  have hstable : (prefixWord ++ tailWord_1042722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042722).length < 2 ^ (prefixWord ++ tailWord_1042722).sum := by decide
  have hdescent : baseEnd_1042722 < baseStart_1042722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042735 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 3, 3, 2]
def baseStart_1042735 : Nat := 118140960795 + 1042735 * 2 ^ 59
def prefixEnd_1042735 : Nat := 4983230072969 + 3 ^ 40 * 1042735 * 2
def baseEnd_1042735 : Nat := 535424250266083028217055

theorem tailTrace_1042735 : CollatzResearch.WordTrace tailWord_1042735 prefixEnd_1042735 535424250266083028217055 := by
  unfold tailWord_1042735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38031669877356654805041659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25354446584904436536694439 38031669877356654805041659)
  ·
    refine ⟨57047504816034982207562489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38031669877356654805041659 57047504816034982207562489)
    ·
      refine ⟨42785628612026236655671867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57047504816034982207562489 42785628612026236655671867)
      ·
        refine ⟨64178442918039354983507801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42785628612026236655671867 64178442918039354983507801)
        ·
          refine ⟨48133832188529516237630851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64178442918039354983507801 48133832188529516237630851)
          ·
            refine ⟨72200748282794274356446277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48133832188529516237630851 72200748282794274356446277)
            ·
              refine ⟨13537640303023926441833677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72200748282794274356446277 13537640303023926441833677)
              ·
                refine ⟨5076615113633972415687629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13537640303023926441833677 5076615113633972415687629)
                ·
                  refine ⟨1903730667612739655882861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5076615113633972415687629 1903730667612739655882861)
                  ·
                    refine ⟨713899000354777370956073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903730667612739655882861 713899000354777370956073)
                    ·
                      refine ⟨535424250266083028217055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713899000354777370956073 535424250266083028217055)
                      ·
                        rfl

theorem cell23_1042735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3, 2].length) (baseStart_1042735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042735 prefixEnd_1042735 := by exact prefixLift 1042735
  have htrace : WordTrace (prefixWord ++ tailWord_1042735) baseStart_1042735 baseEnd_1042735 := by
    simpa [prefixWord, tailWord_1042735, baseEnd_1042735] using wordTrace_append hprefix tailTrace_1042735
  have hstable : (prefixWord ++ tailWord_1042735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042735).length < 2 ^ (prefixWord ++ tailWord_1042735).sum := by decide
  have hdescent : baseEnd_1042735 < baseStart_1042735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042778 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1042778 : Nat := 118140960795 + 1042778 * 2 ^ 59
def prefixEnd_1042778 : Nat := 4983230072969 + 3 ^ 40 * 1042778 * 2
def baseEnd_1042778 : Nat := 535446329934226359979357

theorem tailTrace_1042778 : CollatzResearch.WordTrace tailWord_1042778 prefixEnd_1042778 535446329934226359979357 := by
  unfold tailWord_1042778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508309554050218287214247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25355492144133915432571325 9508309554050218287214247)
  ·
    refine ⟨14262464331075327430821371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9508309554050218287214247 14262464331075327430821371)
    ·
      refine ⟨21393696496612991146232057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14262464331075327430821371 21393696496612991146232057)
      ·
        refine ⟨16045272372459743359674043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21393696496612991146232057 16045272372459743359674043)
        ·
          refine ⟨24067908558689615039511065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045272372459743359674043 24067908558689615039511065)
          ·
            refine ⟨18050931419017211279633299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24067908558689615039511065 18050931419017211279633299)
            ·
              refine ⟨27076397128525816919449949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18050931419017211279633299 27076397128525816919449949)
              ·
                refine ⟨10153648923197181344793731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27076397128525816919449949 10153648923197181344793731)
                ·
                  refine ⟨15230473384795772017190597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153648923197181344793731 15230473384795772017190597)
                  ·
                    refine ⟨2855713759649207253223237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15230473384795772017190597 2855713759649207253223237)
                    ·
                      refine ⟨535446329934226359979357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2855713759649207253223237 535446329934226359979357)
                      ·
                        rfl

theorem cell23_1042778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1042778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042778 prefixEnd_1042778 := by exact prefixLift 1042778
  have htrace : WordTrace (prefixWord ++ tailWord_1042778) baseStart_1042778 baseEnd_1042778 := by
    simpa [prefixWord, tailWord_1042778, baseEnd_1042778] using wordTrace_append hprefix tailTrace_1042778
  have hstable : (prefixWord ++ tailWord_1042778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042778).length < 2 ^ (prefixWord ++ tailWord_1042778).sum := by decide
  have hdescent : baseEnd_1042778 < baseStart_1042778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042786 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1042786 : Nat := 118140960795 + 1042786 * 2 ^ 59
def prefixEnd_1042786 : Nat := 4983230072969 + 3 ^ 40 * 1042786 * 2
def baseEnd_1042786 : Nat := 535450437779462328679321

theorem tailTrace_1042786 : CollatzResearch.WordTrace tailWord_1042786 prefixEnd_1042786 535450437779462328679321 := by
  unfold tailWord_1042786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508382500042972628787053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25355686666781260343432141 9508382500042972628787053)
  ·
    refine ⟨3565643437516114735795145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9508382500042972628787053 3565643437516114735795145)
    ·
      refine ⟨2674232578137086051846359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3565643437516114735795145 2674232578137086051846359)
      ·
        refine ⟨4011348867205629077769539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674232578137086051846359 4011348867205629077769539)
        ·
          refine ⟨6017023300808443616654309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011348867205629077769539 6017023300808443616654309)
          ·
            refine ⟨1128191868901583178122683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6017023300808443616654309 1128191868901583178122683)
            ·
              refine ⟨1692287803352374767184025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128191868901583178122683 1692287803352374767184025)
              ·
                refine ⟨1269215852514281075388019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692287803352374767184025 1269215852514281075388019)
                ·
                  refine ⟨1903823778771421613082029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269215852514281075388019 1903823778771421613082029)
                  ·
                    refine ⟨713933917039283104905761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1903823778771421613082029 713933917039283104905761)
                    ·
                      refine ⟨535450437779462328679321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 713933917039283104905761 535450437779462328679321)
                      ·
                        rfl

theorem cell23_1042786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1042786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042786 prefixEnd_1042786 := by exact prefixLift 1042786
  have htrace : WordTrace (prefixWord ++ tailWord_1042786) baseStart_1042786 baseEnd_1042786 := by
    simpa [prefixWord, tailWord_1042786, baseEnd_1042786] using wordTrace_append hprefix tailTrace_1042786
  have hstable : (prefixWord ++ tailWord_1042786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042786).length < 2 ^ (prefixWord ++ tailWord_1042786).sum := by decide
  have hdescent : baseEnd_1042786 < baseStart_1042786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042788 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 9]
def baseStart_1042788 : Nat := 118140960795 + 1042788 * 2 ^ 59
def prefixEnd_1042788 : Nat := 4983230072969 + 3 ^ 40 * 1042788 * 2
def baseEnd_1042788 : Nat := 59494607193419035650479

theorem tailTrace_1042788 : CollatzResearch.WordTrace tailWord_1042788 prefixEnd_1042788 59494607193419035650479 := by
  unfold tailWord_1042788
  simp only [CollatzResearch.WordTrace]
  refine ⟨19016801473082322428360509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25355735297443096571147345 19016801473082322428360509)
  ·
    refine ⟨7131300552405870910635191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19016801473082322428360509 7131300552405870910635191)
    ·
      refine ⟨10696950828608806365952787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131300552405870910635191 10696950828608806365952787)
      ·
        refine ⟨16045426242913209548929181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696950828608806365952787 16045426242913209548929181)
        ·
          refine ⟨6017034841092453580848443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16045426242913209548929181 6017034841092453580848443)
          ·
            refine ⟨9025552261638680371272665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017034841092453580848443 9025552261638680371272665)
            ·
              refine ⟨6769164196229010278454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025552261638680371272665 6769164196229010278454499)
              ·
                refine ⟨10153746294343515417681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769164196229010278454499 10153746294343515417681749)
                ·
                  refine ⟨59494607193419035650479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10153746294343515417681749 59494607193419035650479)
                  ·
                    rfl

theorem cell23_1042788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_1042788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042788 prefixEnd_1042788 := by exact prefixLift 1042788
  have htrace : WordTrace (prefixWord ++ tailWord_1042788) baseStart_1042788 baseEnd_1042788 := by
    simpa [prefixWord, tailWord_1042788, baseEnd_1042788] using wordTrace_append hprefix tailTrace_1042788
  have hstable : (prefixWord ++ tailWord_1042788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042788).length < 2 ^ (prefixWord ++ tailWord_1042788).sum := by decide
  have hdescent : baseEnd_1042788 < baseStart_1042788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042902 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1042902 : Nat := 118140960795 + 1042902 * 2 ^ 59
def prefixEnd_1042902 : Nat := 4983230072969 + 3 ^ 40 * 1042902 * 2
def baseEnd_1042902 : Nat := 535510001535383874828787

theorem tailTrace_1042902 : CollatzResearch.WordTrace tailWord_1042902 prefixEnd_1042902 535510001535383874828787 := by
  unfold tailWord_1042902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377360054234477645398185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25358507245167761550913973 2377360054234477645398185)
  ·
    refine ⟨1783020040675858234048639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2377360054234477645398185 1783020040675858234048639)
    ·
      refine ⟨2674530061013787351072959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783020040675858234048639 2674530061013787351072959)
      ·
        refine ⟨4011795091520681026609439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674530061013787351072959 4011795091520681026609439)
        ·
          refine ⟨6017692637281021539914159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011795091520681026609439 6017692637281021539914159)
          ·
            refine ⟨9026538955921532309871239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017692637281021539914159 9026538955921532309871239)
            ·
              refine ⟨13539808433882298464806859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026538955921532309871239 13539808433882298464806859)
              ·
                refine ⟨20309712650823447697210289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539808433882298464806859 20309712650823447697210289)
                ·
                  refine ⟨15232284488117585772907717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20309712650823447697210289 15232284488117585772907717)
                  ·
                    refine ⟨2856053341522047332420197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15232284488117585772907717 2856053341522047332420197)
                    ·
                      refine ⟨535510001535383874828787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2856053341522047332420197 535510001535383874828787)
                      ·
                        rfl

theorem cell23_1042902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1042902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042902 prefixEnd_1042902 := by exact prefixLift 1042902
  have htrace : WordTrace (prefixWord ++ tailWord_1042902) baseStart_1042902 baseEnd_1042902 := by
    simpa [prefixWord, tailWord_1042902, baseEnd_1042902] using wordTrace_append hprefix tailTrace_1042902
  have hstable : (prefixWord ++ tailWord_1042902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042902).length < 2 ^ (prefixWord ++ tailWord_1042902).sum := by decide
  have hdescent : baseEnd_1042902 < baseStart_1042902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042905 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_1042905 : Nat := 118140960795 + 1042905 * 2 ^ 59
def prefixEnd_1042905 : Nat := 4983230072969 + 3 ^ 40 * 1042905 * 2
def baseEnd_1042905 : Nat := 535511541977347363091273

theorem tailTrace_1042905 : CollatzResearch.WordTrace tailWord_1042905 prefixEnd_1042905 535511541977347363091273 := by
  unfold tailWord_1042905
  simp only [CollatzResearch.WordTrace]
  refine ⟨38037870286740773838730169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25358580191160515892486779 38037870286740773838730169)
  ·
    refine ⟨28528402715055580379047627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38037870286740773838730169 28528402715055580379047627)
    ·
      refine ⟨42792604072583370568571441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28528402715055580379047627 42792604072583370568571441)
      ·
        refine ⟨32094453054437527926428581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42792604072583370568571441 32094453054437527926428581)
        ·
          refine ⟨6017709947707036486205359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32094453054437527926428581 6017709947707036486205359)
          ·
            refine ⟨9026564921560554729308039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017709947707036486205359 9026564921560554729308039)
            ·
              refine ⟨13539847382340832093962059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026564921560554729308039 13539847382340832093962059)
              ·
                refine ⟨20309771073511248140943089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539847382340832093962059 20309771073511248140943089)
                ·
                  refine ⟨15232328305133436105707317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20309771073511248140943089 15232328305133436105707317)
                  ·
                    refine ⟨1428030778606259634910061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15232328305133436105707317 1428030778606259634910061)
                    ·
                      refine ⟨535511541977347363091273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428030778606259634910061 535511541977347363091273)
                      ·
                        rfl

theorem cell23_1042905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_1042905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042905 prefixEnd_1042905 := by exact prefixLift 1042905
  have htrace : WordTrace (prefixWord ++ tailWord_1042905) baseStart_1042905 baseEnd_1042905 := by
    simpa [prefixWord, tailWord_1042905, baseEnd_1042905] using wordTrace_append hprefix tailTrace_1042905
  have hstable : (prefixWord ++ tailWord_1042905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042905).length < 2 ^ (prefixWord ++ tailWord_1042905).sum := by decide
  have hdescent : baseEnd_1042905 < baseStart_1042905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042933 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1042933 : Nat := 118140960795 + 1042933 * 2 ^ 59
def prefixEnd_1042933 : Nat := 4983230072969 + 3 ^ 40 * 1042933 * 2
def baseEnd_1042933 : Nat := 178508639811891084513715

theorem tailTrace_1042933 : CollatzResearch.WordTrace tailWord_1042933 prefixEnd_1042933 178508639811891084513715 := by
  unfold tailWord_1042933
  simp only [CollatzResearch.WordTrace]
  refine ⟨38038891530639334620749453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25359261020426223080499635 38038891530639334620749453)
  ·
    refine ⟨14264584323989750482781045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38038891530639334620749453 14264584323989750482781045)
    ·
      refine ⟨1337304780374039107760723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14264584323989750482781045 1337304780374039107760723)
      ·
        refine ⟨2005957170561058661641085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337304780374039107760723 2005957170561058661641085)
        ·
          refine ⟨752233938960396998115407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005957170561058661641085 752233938960396998115407)
          ·
            refine ⟨1128350908440595497173111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752233938960396998115407 1128350908440595497173111)
            ·
              refine ⟨1692526362660893245759667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128350908440595497173111 1692526362660893245759667)
              ·
                refine ⟨2538789543991339868639501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692526362660893245759667 2538789543991339868639501)
                ·
                  refine ⟨952046078996752450739813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2538789543991339868639501 952046078996752450739813)
                  ·
                    refine ⟨178508639811891084513715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952046078996752450739813 178508639811891084513715)
                    ·
                      rfl

theorem cell23_1042933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1042933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042933 prefixEnd_1042933 := by exact prefixLift 1042933
  have htrace : WordTrace (prefixWord ++ tailWord_1042933) baseStart_1042933 baseEnd_1042933 := by
    simpa [prefixWord, tailWord_1042933, baseEnd_1042933] using wordTrace_append hprefix tailTrace_1042933
  have hstable : (prefixWord ++ tailWord_1042933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042933).length < 2 ^ (prefixWord ++ tailWord_1042933).sum := by decide
  have hdescent : baseEnd_1042933 < baseStart_1042933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042972 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1042972 : Nat := 118140960795 + 1042972 * 2 ^ 59
def prefixEnd_1042972 : Nat := 4983230072969 + 3 ^ 40 * 1042972 * 2
def baseEnd_1042972 : Nat := 178515315060399533651155

theorem tailTrace_1042972 : CollatzResearch.WordTrace tailWord_1042972 prefixEnd_1042972 178515315060399533651155 := by
  unfold tailWord_1042972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020156988749022140709585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25360209318332029520946113 19020156988749022140709585)
  ·
    refine ⟨14265117741561766605532189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19020156988749022140709585 14265117741561766605532189)
    ·
      refine ⟨5349419153085662477074571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14265117741561766605532189 5349419153085662477074571)
      ·
        refine ⟨8024128729628493715611857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349419153085662477074571 8024128729628493715611857)
        ·
          refine ⟨6018096547221370286708893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8024128729628493715611857 6018096547221370286708893)
          ·
            refine ⟨2256786205208013857515835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6018096547221370286708893 2256786205208013857515835)
            ·
              refine ⟨3385179307812020786273753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2256786205208013857515835 3385179307812020786273753)
              ·
                refine ⟨2538884480859015589705315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385179307812020786273753 2538884480859015589705315)
                ·
                  refine ⟨3808326721288523384557973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538884480859015589705315 3808326721288523384557973)
                  ·
                    refine ⟨178515315060399533651155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3808326721288523384557973 178515315060399533651155)
                    ·
                      rfl

theorem cell23_1042972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1042972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042972 prefixEnd_1042972 := by exact prefixLift 1042972
  have htrace : WordTrace (prefixWord ++ tailWord_1042972) baseStart_1042972 baseEnd_1042972 := by
    simpa [prefixWord, tailWord_1042972, baseEnd_1042972] using wordTrace_append hprefix tailTrace_1042972
  have hstable : (prefixWord ++ tailWord_1042972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042972).length < 2 ^ (prefixWord ++ tailWord_1042972).sum := by decide
  have hdescent : baseEnd_1042972 < baseStart_1042972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042976 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 1, 5]
def baseStart_1042976 : Nat := 118140960795 + 1042976 * 2 ^ 59
def prefixEnd_1042976 : Nat := 4983230072969 + 3 ^ 40 * 1042976 * 2
def baseEnd_1042976 : Nat := 178515999701272195101149

theorem tailTrace_1042976 : CollatzResearch.WordTrace tailWord_1042976 prefixEnd_1042976 178515999701272195101149 := by
  unfold tailWord_1042976
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020229934741776482282391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25360306579655701976376521 19020229934741776482282391)
  ·
    refine ⟨28530344902112664723423587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19020229934741776482282391 28530344902112664723423587)
    ·
      refine ⟨42795517353168997085135381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28530344902112664723423587 42795517353168997085135381)
      ·
        refine ⟨2006039875929796738365721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42795517353168997085135381 2006039875929796738365721)
        ·
          refine ⟨1504529906947347553774291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2006039875929796738365721 1504529906947347553774291)
          ·
            refine ⟨2256794860421021330661437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504529906947347553774291 2256794860421021330661437)
            ·
              refine ⟨846298072657882998998039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2256794860421021330661437 846298072657882998998039)
              ·
                refine ⟨1269447108986824498497059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846298072657882998998039 1269447108986824498497059)
                ·
                  refine ⟨1904170663480236747745589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269447108986824498497059 1904170663480236747745589)
                  ·
                    refine ⟨178515999701272195101149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1904170663480236747745589 178515999701272195101149)
                    ·
                      rfl

theorem cell23_1042976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_1042976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1042976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1042976 prefixEnd_1042976 := by exact prefixLift 1042976
  have htrace : WordTrace (prefixWord ++ tailWord_1042976) baseStart_1042976 baseEnd_1042976 := by
    simpa [prefixWord, tailWord_1042976, baseEnd_1042976] using wordTrace_append hprefix tailTrace_1042976
  have hstable : (prefixWord ++ tailWord_1042976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042976).length < 2 ^ (prefixWord ++ tailWord_1042976).sum := by decide
  have hdescent : baseEnd_1042976 < baseStart_1042976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043002 : List Nat := [3, 1, 1, 1, 3, 5, 1, 8]
def baseStart_1043002 : Nat := 118140960795 + 1043002 * 2 ^ 59
def prefixEnd_1043002 : Nat := 4983230072969 + 3 ^ 40 * 1043002 * 2
def baseEnd_1043002 : Nat := 19835605540771610502901

theorem tailTrace_1043002 : CollatzResearch.WordTrace tailWord_1043002 prefixEnd_1043002 19835605540771610502901 := by
  unfold tailWord_1043002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510352041847339851252815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25360938778259572936674173 9510352041847339851252815)
  ·
    refine ⟨14265528062771009776879223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9510352041847339851252815 14265528062771009776879223)
    ·
      refine ⟨21398292094156514665318835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14265528062771009776879223 21398292094156514665318835)
      ·
        refine ⟨32097438141234771997978253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398292094156514665318835 32097438141234771997978253)
        ·
          refine ⟨12036539302963039499241845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32097438141234771997978253 12036539302963039499241845)
          ·
            refine ⟨1128425559652784953053923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12036539302963039499241845 1128425559652784953053923)
            ·
              refine ⟨1692638339479177429580885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128425559652784953053923 1692638339479177429580885)
              ·
                refine ⟨19835605540771610502901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1692638339479177429580885 19835605540771610502901)
                ·
                  rfl

theorem cell23_1043002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_1043002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043002 prefixEnd_1043002 := by exact prefixLift 1043002
  have htrace : WordTrace (prefixWord ++ tailWord_1043002) baseStart_1043002 baseEnd_1043002 := by
    simpa [prefixWord, tailWord_1043002, baseEnd_1043002] using wordTrace_append hprefix tailTrace_1043002
  have hstable : (prefixWord ++ tailWord_1043002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043002).length < 2 ^ (prefixWord ++ tailWord_1043002).sum := by decide
  have hdescent : baseEnd_1043002 < baseStart_1043002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043006 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1043006 : Nat := 118140960795 + 1043006 * 2 ^ 59
def prefixEnd_1043006 : Nat := 4983230072969 + 3 ^ 40 * 1043006 * 2
def baseEnd_1043006 : Nat := 178521134507817155976103

theorem tailTrace_1043006 : CollatzResearch.WordTrace tailWord_1043006 prefixEnd_1043006 178521134507817155976103 := by
  unfold tailWord_1043006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755194257421858511019609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25361036039583245392104581 4755194257421858511019609)
  ·
    refine ⟨3566395693066393883264707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4755194257421858511019609 3566395693066393883264707)
    ·
      refine ⟨5349593539599590824897061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566395693066393883264707 5349593539599590824897061)
      ·
        refine ⟨1003048788674923279668199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5349593539599590824897061 1003048788674923279668199)
        ·
          refine ⟨1504573183012384919502299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003048788674923279668199 1504573183012384919502299)
          ·
            refine ⟨2256859774518577379253449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504573183012384919502299 2256859774518577379253449)
            ·
              refine ⟨1692644830888933034440087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256859774518577379253449 1692644830888933034440087)
              ·
                refine ⟨2538967246333399551660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692644830888933034440087 2538967246333399551660131)
                ·
                  refine ⟨3808450869500099327490197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538967246333399551660131 3808450869500099327490197)
                  ·
                    refine ⟨178521134507817155976103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3808450869500099327490197 178521134507817155976103)
                    ·
                      rfl

theorem cell23_1043006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1043006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043006 prefixEnd_1043006 := by exact prefixLift 1043006
  have htrace : WordTrace (prefixWord ++ tailWord_1043006) baseStart_1043006 baseEnd_1043006 := by
    simpa [prefixWord, tailWord_1043006, baseEnd_1043006] using wordTrace_append hprefix tailTrace_1043006
  have hstable : (prefixWord ++ tailWord_1043006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043006).length < 2 ^ (prefixWord ++ tailWord_1043006).sum := by decide
  have hdescent : baseEnd_1043006 < baseStart_1043006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043009 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1043009 : Nat := 118140960795 + 1043009 * 2 ^ 59
def prefixEnd_1043009 : Nat := 4983230072969 + 3 ^ 40 * 1043009 * 2
def baseEnd_1043009 : Nat := 535564943965414956190795

theorem tailTrace_1043009 : CollatzResearch.WordTrace tailWord_1043009 prefixEnd_1043009 535564943965414956190795 := by
  unfold tailWord_1043009
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041663478363999600516081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25361108985575999733677387 38041663478363999600516081)
  ·
    refine ⟨28531247608772999700387061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38041663478363999600516081 28531247608772999700387061)
    ·
      refine ⟨2674804463322468721911287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28531247608772999700387061 2674804463322468721911287)
      ·
        refine ⟨4012206694983703082866931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674804463322468721911287 4012206694983703082866931)
        ·
          refine ⟨6018310042475554624300397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012206694983703082866931 6018310042475554624300397)
          ·
            refine ⟨2256866265928332984112649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6018310042475554624300397 2256866265928332984112649)
            ·
              refine ⟨1692649699446249738084487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256866265928332984112649 1692649699446249738084487)
              ·
                refine ⟨2538974549169374607126731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692649699446249738084487 2538974549169374607126731)
                ·
                  refine ⟨3808461823754061910690097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538974549169374607126731 3808461823754061910690097)
                  ·
                    refine ⟨2856346367815546433017573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808461823754061910690097 2856346367815546433017573)
                    ·
                      refine ⟨535564943965414956190795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2856346367815546433017573 535564943965414956190795)
                      ·
                        rfl

theorem cell23_1043009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1043009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043009 prefixEnd_1043009 := by exact prefixLift 1043009
  have htrace : WordTrace (prefixWord ++ tailWord_1043009) baseStart_1043009 baseEnd_1043009 := by
    simpa [prefixWord, tailWord_1043009, baseEnd_1043009] using wordTrace_append hprefix tailTrace_1043009
  have hstable : (prefixWord ++ tailWord_1043009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043009).length < 2 ^ (prefixWord ++ tailWord_1043009).sum := by decide
  have hdescent : baseEnd_1043009 < baseStart_1043009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043086 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1043086 : Nat := 118140960795 + 1043086 * 2 ^ 59
def prefixEnd_1043086 : Nat := 4983230072969 + 3 ^ 40 * 1043086 * 2
def baseEnd_1043086 : Nat := 535604481975811154927941

theorem tailTrace_1043086 : CollatzResearch.WordTrace tailWord_1043086 prefixEnd_1043086 535604481975811154927941 := by
  unfold tailWord_1043086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755558987385630218883639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25362981266056694500712741 4755558987385630218883639)
  ·
    refine ⟨7133338481078445328325459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4755558987385630218883639 7133338481078445328325459)
    ·
      refine ⟨10700007721617667992488189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7133338481078445328325459 10700007721617667992488189)
      ·
        refine ⟨4012502895606625497183071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10700007721617667992488189 4012502895606625497183071)
        ·
          refine ⟨6018754343409938245774607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012502895606625497183071 6018754343409938245774607)
          ·
            refine ⟨9028131515114907368661911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018754343409938245774607 9028131515114907368661911)
            ·
              refine ⟨13542197272672361052992867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028131515114907368661911 13542197272672361052992867)
              ·
                refine ⟨20313295909008541579489301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13542197272672361052992867 20313295909008541579489301)
                ·
                  refine ⟨952185745734775386538561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20313295909008541579489301 952185745734775386538561)
                  ·
                    refine ⟨714139309301081539903921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952185745734775386538561 714139309301081539903921)
                    ·
                      refine ⟨535604481975811154927941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714139309301081539903921 535604481975811154927941)
                      ·
                        rfl

theorem cell23_1043086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1043086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043086 prefixEnd_1043086 := by exact prefixLift 1043086
  have htrace : WordTrace (prefixWord ++ tailWord_1043086) baseStart_1043086 baseEnd_1043086 := by
    simpa [prefixWord, tailWord_1043086, baseEnd_1043086] using wordTrace_append hprefix tailTrace_1043086
  have hstable : (prefixWord ++ tailWord_1043086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043086).length < 2 ^ (prefixWord ++ tailWord_1043086).sum := by decide
  have hdescent : baseEnd_1043086 < baseStart_1043086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043114 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1043114 : Nat := 118140960795 + 1043114 * 2 ^ 59
def prefixEnd_1043114 : Nat := 4983230072969 + 3 ^ 40 * 1043114 * 2
def baseEnd_1043114 : Nat := 535618859434137045377813

theorem tailTrace_1043114 : CollatzResearch.WordTrace tailWord_1043114 prefixEnd_1043114 535618859434137045377813 := by
  unfold tailWord_1043114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511373285745900633272099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25363662095322401688725597 9511373285745900633272099)
  ·
    refine ⟨14267059928618850949908149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9511373285745900633272099 14267059928618850949908149)
    ·
      refine ⟨1337536868308017276553889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14267059928618850949908149 1337536868308017276553889)
      ·
        refine ⟨1003152651231012957415417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337536868308017276553889 1003152651231012957415417)
        ·
          refine ⟨752364488423259718061563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003152651231012957415417 752364488423259718061563)
          ·
            refine ⟨1128546732634889577092345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752364488423259718061563 1128546732634889577092345)
            ·
              refine ⟨846410049476167182819259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128546732634889577092345 846410049476167182819259)
              ·
                refine ⟨1269615074214250774228889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846410049476167182819259 1269615074214250774228889)
                ·
                  refine ⟨952211305660688080671667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1269615074214250774228889 952211305660688080671667)
                  ·
                    refine ⟨1428316958491032121007501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 952211305660688080671667 1428316958491032121007501)
                    ·
                      refine ⟨535618859434137045377813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428316958491032121007501 535618859434137045377813)
                      ·
                        rfl

theorem cell23_1043114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1043114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043114 prefixEnd_1043114 := by exact prefixLift 1043114
  have htrace : WordTrace (prefixWord ++ tailWord_1043114) baseStart_1043114 baseEnd_1043114 := by
    simpa [prefixWord, tailWord_1043114, baseEnd_1043114] using wordTrace_append hprefix tailTrace_1043114
  have hstable : (prefixWord ++ tailWord_1043114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043114).length < 2 ^ (prefixWord ++ tailWord_1043114).sum := by decide
  have hdescent : baseEnd_1043114 < baseStart_1043114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043122 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1043122 : Nat := 118140960795 + 1043122 * 2 ^ 59
def prefixEnd_1043122 : Nat := 4983230072969 + 3 ^ 40 * 1043122 * 2
def baseEnd_1043122 : Nat := 178540989093124338025925

theorem tailTrace_1043122 : CollatzResearch.WordTrace tailWord_1043122 prefixEnd_1043122 178540989093124338025925 := by
  unfold tailWord_1043122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511446231738654974844905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25363856617969746599586413 9511446231738654974844905)
  ·
    refine ⟨7133584673803991231133679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9511446231738654974844905 7133584673803991231133679)
    ·
      refine ⟨10700377010705986846700519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7133584673803991231133679 10700377010705986846700519)
      ·
        refine ⟨16050565516058980270050779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10700377010705986846700519 16050565516058980270050779)
        ·
          refine ⟨24075848274088470405076169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16050565516058980270050779 24075848274088470405076169)
          ·
            refine ⟨18056886205566352803807127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24075848274088470405076169 18056886205566352803807127)
            ·
              refine ⟨27085329308349529205710691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18056886205566352803807127 27085329308349529205710691)
              ·
                refine ⟨40627993962524293808566037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27085329308349529205710691 40627993962524293808566037)
                ·
                  refine ⟨1904437216993326272276533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40627993962524293808566037 1904437216993326272276533)
                  ·
                    refine ⟨178540989093124338025925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1904437216993326272276533 178540989093124338025925)
                    ·
                      rfl

theorem cell23_1043122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1043122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043122 prefixEnd_1043122 := by exact prefixLift 1043122
  have htrace : WordTrace (prefixWord ++ tailWord_1043122) baseStart_1043122 baseEnd_1043122 := by
    simpa [prefixWord, tailWord_1043122, baseEnd_1043122] using wordTrace_append hprefix tailTrace_1043122
  have hstable : (prefixWord ++ tailWord_1043122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043122).length < 2 ^ (prefixWord ++ tailWord_1043122).sum := by decide
  have hdescent : baseEnd_1043122 < baseStart_1043122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043132 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1043132 : Nat := 118140960795 + 1043132 * 2 ^ 59
def prefixEnd_1043132 : Nat := 4983230072969 + 3 ^ 40 * 1043132 * 2
def baseEnd_1043132 : Nat := 535628102085917974952729

theorem tailTrace_1043132 : CollatzResearch.WordTrace tailWord_1043132 prefixEnd_1043132 535628102085917974952729 := by
  unfold tailWord_1043132
  simp only [CollatzResearch.WordTrace]
  refine ⟨19023074828459195803621825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25364099771278927738162433 19023074828459195803621825)
  ·
    refine ⟨14267306121344396852716369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19023074828459195803621825 14267306121344396852716369)
    ·
      refine ⟨10700479591008297639537277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14267306121344396852716369 10700479591008297639537277)
      ·
        refine ⟨4012679846628111614826479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10700479591008297639537277 4012679846628111614826479)
        ·
          refine ⟨6019019769942167422239719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012679846628111614826479 6019019769942167422239719)
          ·
            refine ⟨9028529654913251133359579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019019769942167422239719 9028529654913251133359579)
            ·
              refine ⟨13542794482369876700039369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028529654913251133359579 13542794482369876700039369)
              ·
                refine ⟨10157095861777407525029527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13542794482369876700039369 10157095861777407525029527)
                ·
                  refine ⟨15235643792666111287544291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10157095861777407525029527 15235643792666111287544291)
                  ·
                    refine ⟨22853465688999166931316437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15235643792666111287544291 22853465688999166931316437)
                    ·
                      refine ⟨535628102085917974952729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22853465688999166931316437 535628102085917974952729)
                      ·
                        rfl

theorem cell23_1043132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1043132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043132 prefixEnd_1043132 := by exact prefixLift 1043132
  have htrace : WordTrace (prefixWord ++ tailWord_1043132) baseStart_1043132 baseEnd_1043132 := by
    simpa [prefixWord, tailWord_1043132, baseEnd_1043132] using wordTrace_append hprefix tailTrace_1043132
  have hstable : (prefixWord ++ tailWord_1043132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043132).length < 2 ^ (prefixWord ++ tailWord_1043132).sum := by decide
  have hdescent : baseEnd_1043132 < baseStart_1043132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043159 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1043159 : Nat := 118140960795 + 1043159 * 2 ^ 59
def prefixEnd_1043159 : Nat := 4983230072969 + 3 ^ 40 * 1043159 * 2
def baseEnd_1043159 : Nat := 535641966063589369315105

theorem tailTrace_1043159 : CollatzResearch.WordTrace tailWord_1043159 prefixEnd_1043159 535641966063589369315105 := by
  unfold tailWord_1043159
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047134427820575218476531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25364756285213716812317687 38047134427820575218476531)
  ·
    refine ⟨57070701641730862827714797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38047134427820575218476531 57070701641730862827714797)
    ·
      refine ⟨21401513115649073560393049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57070701641730862827714797 21401513115649073560393049)
      ·
        refine ⟨16051134836736805170294787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21401513115649073560393049 16051134836736805170294787)
        ·
          refine ⟨24076702255105207755442181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16051134836736805170294787 24076702255105207755442181)
          ·
            refine ⟨4514381672832226454145409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24076702255105207755442181 4514381672832226454145409)
            ·
              refine ⟨3385786254624169840609057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4514381672832226454145409 3385786254624169840609057)
              ·
                refine ⟨2539339690968127380456793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385786254624169840609057 2539339690968127380456793)
                ·
                  refine ⟨1904504768226095535342595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539339690968127380456793 1904504768226095535342595)
                  ·
                    refine ⟨2856757152339143303013893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1904504768226095535342595 2856757152339143303013893)
                    ·
                      refine ⟨535641966063589369315105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2856757152339143303013893 535641966063589369315105)
                      ·
                        rfl

theorem cell23_1043159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1043159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043159 prefixEnd_1043159 := by exact prefixLift 1043159
  have htrace : WordTrace (prefixWord ++ tailWord_1043159) baseStart_1043159 baseEnd_1043159 := by
    simpa [prefixWord, tailWord_1043159, baseEnd_1043159] using wordTrace_append hprefix tailTrace_1043159
  have hstable : (prefixWord ++ tailWord_1043159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043159).length < 2 ^ (prefixWord ++ tailWord_1043159).sum := by decide
  have hdescent : baseEnd_1043159 < baseStart_1043159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043162 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1043162 : Nat := 118140960795 + 1043162 * 2 ^ 59
def prefixEnd_1043162 : Nat := 4983230072969 + 3 ^ 40 * 1043162 * 2
def baseEnd_1043162 : Nat := 535643506505552857577591

theorem tailTrace_1043162 : CollatzResearch.WordTrace tailWord_1043162 prefixEnd_1043162 535643506505552857577591 := by
  unfold tailWord_1043162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511810961702426682708935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25364829231206471153890493 9511810961702426682708935)
  ·
    refine ⟨14267716442553640024063403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9511810961702426682708935 14267716442553640024063403)
    ·
      refine ⟨21401574663830460036095105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14267716442553640024063403 21401574663830460036095105)
      ·
        refine ⟨16051180997872845027071329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21401574663830460036095105 16051180997872845027071329)
        ·
          refine ⟨12038385748404633770303497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16051180997872845027071329 12038385748404633770303497)
          ·
            refine ⟨9028789311303475327727623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12038385748404633770303497 9028789311303475327727623)
            ·
              refine ⟨13543183966955212991591435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028789311303475327727623 13543183966955212991591435)
              ·
                refine ⟨20314775950432819487387153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543183966955212991591435 20314775950432819487387153)
                ·
                  refine ⟨15236081962824614615540365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20314775950432819487387153 15236081962824614615540365)
                  ·
                    refine ⟨5713530736059230480827637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15236081962824614615540365 5713530736059230480827637)
                    ·
                      refine ⟨535643506505552857577591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5713530736059230480827637 535643506505552857577591)
                      ·
                        rfl

theorem cell23_1043162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1043162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043162 prefixEnd_1043162 := by exact prefixLift 1043162
  have htrace : WordTrace (prefixWord ++ tailWord_1043162) baseStart_1043162 baseEnd_1043162 := by
    simpa [prefixWord, tailWord_1043162, baseEnd_1043162] using wordTrace_append hprefix tailTrace_1043162
  have hstable : (prefixWord ++ tailWord_1043162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043162).length < 2 ^ (prefixWord ++ tailWord_1043162).sum := by decide
  have hdescent : baseEnd_1043162 < baseStart_1043162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043186 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1043186 : Nat := 118140960795 + 1043186 * 2 ^ 59
def prefixEnd_1043186 : Nat := 4983230072969 + 3 ^ 40 * 1043186 * 2
def baseEnd_1043186 : Nat := 178551943347086921225827

theorem tailTrace_1043186 : CollatzResearch.WordTrace tailWord_1043186 prefixEnd_1043186 178551943347086921225827 := by
  unfold tailWord_1043186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512029799680689707427353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25365412799148505886472941 9512029799680689707427353)
  ·
    refine ⟨7134022349760517280570515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9512029799680689707427353 7134022349760517280570515)
    ·
      refine ⟨10701033524640775920855773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134022349760517280570515 10701033524640775920855773)
      ·
        refine ⟨4012887571740290970320915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10701033524640775920855773 4012887571740290970320915)
        ·
          refine ⟨6019331357610436455481373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012887571740290970320915 6019331357610436455481373)
          ·
            refine ⟨2257249259103913670805515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6019331357610436455481373 2257249259103913670805515)
            ·
              refine ⟨3385873888655870506208273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257249259103913670805515 3385873888655870506208273)
              ·
                refine ⟨2539405416491902879656205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385873888655870506208273 2539405416491902879656205)
                ·
                  refine ⟨952277031184463579871077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2539405416491902879656205 952277031184463579871077)
                  ·
                    refine ⟨178551943347086921225827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952277031184463579871077 178551943347086921225827)
                    ·
                      rfl

theorem cell23_1043186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1043186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043186 prefixEnd_1043186 := by exact prefixLift 1043186
  have htrace : WordTrace (prefixWord ++ tailWord_1043186) baseStart_1043186 baseEnd_1043186 := by
    simpa [prefixWord, tailWord_1043186, baseEnd_1043186] using wordTrace_append hprefix tailTrace_1043186
  have hstable : (prefixWord ++ tailWord_1043186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043186).length < 2 ^ (prefixWord ++ tailWord_1043186).sum := by decide
  have hdescent : baseEnd_1043186 < baseStart_1043186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043196 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_1043196 : Nat := 118140960795 + 1043196 * 2 ^ 59
def prefixEnd_1043196 : Nat := 4983230072969 + 3 ^ 40 * 1043196 * 2
def baseEnd_1043196 : Nat := 535660964847805724552435

theorem tailTrace_1043196 : CollatzResearch.WordTrace tailWord_1043196 prefixEnd_1043196 535660964847805724552435 := by
  unfold tailWord_1043196
  simp only [CollatzResearch.WordTrace]
  refine ⟨19024241964343265268786721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25365655952457687025048961 19024241964343265268786721)
  ·
    refine ⟨14268181473257448951590041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19024241964343265268786721 14268181473257448951590041)
    ·
      refine ⟨10701136104943086713692531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14268181473257448951590041 10701136104943086713692531)
      ·
        refine ⟨16051704157414630070538797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10701136104943086713692531 16051704157414630070538797)
        ·
          refine ⟨6019389059030486276452049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16051704157414630070538797 6019389059030486276452049)
          ·
            refine ⟨4514541794272864707339037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019389059030486276452049 4514541794272864707339037)
            ·
              refine ⟨1692953172852324265252139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4514541794272864707339037 1692953172852324265252139)
              ·
                refine ⟨2539429759278486397878209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692953172852324265252139 2539429759278486397878209)
                ·
                  refine ⟨1904572319458864798408657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539429759278486397878209 1904572319458864798408657)
                  ·
                    refine ⟨1428429239594148598806493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1904572319458864798408657 1428429239594148598806493)
                    ·
                      refine ⟨535660964847805724552435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428429239594148598806493 535660964847805724552435)
                      ·
                        rfl

theorem cell23_1043196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_1043196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043196 prefixEnd_1043196 := by exact prefixLift 1043196
  have htrace : WordTrace (prefixWord ++ tailWord_1043196) baseStart_1043196 baseEnd_1043196 := by
    simpa [prefixWord, tailWord_1043196, baseEnd_1043196] using wordTrace_append hprefix tailTrace_1043196
  have hstable : (prefixWord ++ tailWord_1043196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043196).length < 2 ^ (prefixWord ++ tailWord_1043196).sum := by decide
  have hdescent : baseEnd_1043196 < baseStart_1043196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043254 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1043254 : Nat := 118140960795 + 1043254 * 2 ^ 59
def prefixEnd_1043254 : Nat := 4983230072969 + 3 ^ 40 * 1043254 * 2
def baseEnd_1043254 : Nat := 178563582241922165875723

theorem tailTrace_1043254 : CollatzResearch.WordTrace tailWord_1043254 prefixEnd_1043254 178563582241922165875723 := by
  unfold tailWord_1043254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378162460154775402699051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25367066241650937628789877 2378162460154775402699051)
  ·
    refine ⟨3567243690232163104048577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378162460154775402699051 3567243690232163104048577)
    ·
      refine ⟨2675432767674122328036433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3567243690232163104048577 2675432767674122328036433)
      ·
        refine ⟨2006574575755591746027325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675432767674122328036433 2006574575755591746027325)
        ·
          refine ⟨752465465908346904760247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2006574575755591746027325 752465465908346904760247)
          ·
            refine ⟨1128698198862520357140371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752465465908346904760247 1128698198862520357140371)
            ·
              refine ⟨1693047298293780535710557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128698198862520357140371 1693047298293780535710557)
              ·
                refine ⟨634892736860167700891459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1693047298293780535710557 634892736860167700891459)
                ·
                  refine ⟨952339105290251551337189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 634892736860167700891459 952339105290251551337189)
                  ·
                    refine ⟨178563582241922165875723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952339105290251551337189 178563582241922165875723)
                    ·
                      rfl

theorem cell23_1043254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1043254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043254 prefixEnd_1043254 := by exact prefixLift 1043254
  have htrace : WordTrace (prefixWord ++ tailWord_1043254) baseStart_1043254 baseEnd_1043254 := by
    simpa [prefixWord, tailWord_1043254, baseEnd_1043254] using wordTrace_append hprefix tailTrace_1043254
  have hstable : (prefixWord ++ tailWord_1043254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043254).length < 2 ^ (prefixWord ++ tailWord_1043254).sum := by decide
  have hdescent : baseEnd_1043254 < baseStart_1043254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043276 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_1043276 : Nat := 118140960795 + 1043276 * 2 ^ 59
def prefixEnd_1043276 : Nat := 4983230072969 + 3 ^ 40 * 1043276 * 2
def baseEnd_1043276 : Nat := 178567347766721803850689

theorem tailTrace_1043276 : CollatzResearch.WordTrace tailWord_1043276 prefixEnd_1043276 178567347766721803850689 := by
  unfold tailWord_1043276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025700884198352100242841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25367601178931136133657121 19025700884198352100242841)
  ·
    refine ⟨14269275663148764075182131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19025700884198352100242841 14269275663148764075182131)
    ·
      refine ⟨21403913494723146112773197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269275663148764075182131 21403913494723146112773197)
      ·
        refine ⟨8026467560521179792289949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21403913494723146112773197 8026467560521179792289949)
        ·
          refine ⟨3009925335195442422108731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8026467560521179792289949 3009925335195442422108731)
          ·
            refine ⟨4514888002793163633163097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009925335195442422108731 4514888002793163633163097)
            ·
              refine ⟨3386166002094872724872323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4514888002793163633163097 3386166002094872724872323)
              ·
                refine ⟨5079249003142309087308485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386166002094872724872323 5079249003142309087308485)
                ·
                  refine ⟨952359188089182953870341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5079249003142309087308485 952359188089182953870341)
                  ·
                    refine ⟨178567347766721803850689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952359188089182953870341 178567347766721803850689)
                    ·
                      rfl

theorem cell23_1043276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_1043276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043276 prefixEnd_1043276 := by exact prefixLift 1043276
  have htrace : WordTrace (prefixWord ++ tailWord_1043276) baseStart_1043276 baseEnd_1043276 := by
    simpa [prefixWord, tailWord_1043276, baseEnd_1043276] using wordTrace_append hprefix tailTrace_1043276
  have hstable : (prefixWord ++ tailWord_1043276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043276).length < 2 ^ (prefixWord ++ tailWord_1043276).sum := by decide
  have hdescent : baseEnd_1043276 < baseStart_1043276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043277 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1043277 : Nat := 118140960795 + 1043277 * 2 ^ 59
def prefixEnd_1043277 : Nat := 4983230072969 + 3 ^ 40 * 1043277 * 2
def baseEnd_1043277 : Nat := 535702556780819907639563

theorem tailTrace_1043277 : CollatzResearch.WordTrace tailWord_1043277 prefixEnd_1043277 535702556780819907639563 := by
  unfold tailWord_1043277
  simp only [CollatzResearch.WordTrace]
  refine ⟨38051438241393081371272085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25367625494262054247514723 38051438241393081371272085)
  ·
    refine ⟨1783661167565300689278379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38051438241393081371272085 1783661167565300689278379)
    ·
      refine ⟨2675491751347951033917569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783661167565300689278379 2675491751347951033917569)
      ·
        refine ⟨2006618813510963275438177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675491751347951033917569 2006618813510963275438177)
        ·
          refine ⟨1504964110133222456578633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2006618813510963275438177 1504964110133222456578633)
          ·
            refine ⟨1128723082599916842433975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504964110133222456578633 1128723082599916842433975)
            ·
              refine ⟨1693084623899875263650963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128723082599916842433975 1693084623899875263650963)
              ·
                refine ⟨2539626935849812895476445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693084623899875263650963 2539626935849812895476445)
                ·
                  refine ⟨952360100943679835803667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2539626935849812895476445 952360100943679835803667)
                  ·
                    refine ⟨1428540151415519753705501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 952360100943679835803667 1428540151415519753705501)
                    ·
                      refine ⟨535702556780819907639563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428540151415519753705501 535702556780819907639563)
                      ·
                        rfl

theorem cell23_1043277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1043277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043277 prefixEnd_1043277 := by exact prefixLift 1043277
  have htrace : WordTrace (prefixWord ++ tailWord_1043277) baseStart_1043277 baseEnd_1043277 := by
    simpa [prefixWord, tailWord_1043277, baseEnd_1043277] using wordTrace_append hprefix tailTrace_1043277
  have hstable : (prefixWord ++ tailWord_1043277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043277).length < 2 ^ (prefixWord ++ tailWord_1043277).sum := by decide
  have hdescent : baseEnd_1043277 < baseStart_1043277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043289 : List Nat := [1, 2, 1, 2, 2, 5, 2, 8]
def baseStart_1043289 : Nat := 118140960795 + 1043289 * 2 ^ 59
def prefixEnd_1043289 : Nat := 4983230072969 + 3 ^ 40 * 1043289 * 2
def baseEnd_1043289 : Nat := 19841063649950883729241

theorem tailTrace_1043289 : CollatzResearch.WordTrace tailWord_1043289 prefixEnd_1043289 19841063649950883729241 := by
  unfold tailWord_1043289
  simp only [CollatzResearch.WordTrace]
  refine ⟨38051875917349607420708921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25367917278233071613805947 38051875917349607420708921)
  ·
    refine ⟨28538906938012205565531691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38051875917349607420708921 28538906938012205565531691)
    ·
      refine ⟨42808360407018308348297537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28538906938012205565531691 42808360407018308348297537)
      ·
        refine ⟨32106270305263731261223153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42808360407018308348297537 32106270305263731261223153)
        ·
          refine ⟨24079702728947798445917365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32106270305263731261223153 24079702728947798445917365)
          ·
            refine ⟨2257472130838856104304753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24079702728947798445917365 2257472130838856104304753)
            ·
              refine ⟨1693104098129142078228565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257472130838856104304753 1693104098129142078228565)
              ·
                refine ⟨19841063649950883729241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1693104098129142078228565 19841063649950883729241)
                ·
                  rfl

theorem cell23_1043289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 8].length) (baseStart_1043289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043289 prefixEnd_1043289 := by exact prefixLift 1043289
  have htrace : WordTrace (prefixWord ++ tailWord_1043289) baseStart_1043289 baseEnd_1043289 := by
    simpa [prefixWord, tailWord_1043289, baseEnd_1043289] using wordTrace_append hprefix tailTrace_1043289
  have hstable : (prefixWord ++ tailWord_1043289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043289).length < 2 ^ (prefixWord ++ tailWord_1043289).sum := by decide
  have hdescent : baseEnd_1043289 < baseStart_1043289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043303 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_1043303 : Nat := 118140960795 + 1043303 * 2 ^ 59
def prefixEnd_1043303 : Nat := 4983230072969 + 3 ^ 40 * 1043303 * 2
def baseEnd_1043303 : Nat := 535715907277836805914443

theorem tailTrace_1043303 : CollatzResearch.WordTrace tailWord_1043303 prefixEnd_1043303 535715907277836805914443 := by
  unfold tailWord_1043303
  simp only [CollatzResearch.WordTrace]
  refine ⟨38052386539298887811718563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25368257692865925207812375 38052386539298887811718563)
  ·
    refine ⟨57078579808948331717577845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38052386539298887811718563 57078579808948331717577845)
    ·
      refine ⟨5351116857088906098522923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57078579808948331717577845 5351116857088906098522923)
      ·
        refine ⟨8026675285633359147784385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351116857088906098522923 8026675285633359147784385)
        ·
          refine ⟨6020006464225019360838289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8026675285633359147784385 6020006464225019360838289)
          ·
            refine ⟨4515004848168764520628717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020006464225019360838289 4515004848168764520628717)
            ·
              refine ⟨1693126818063286695235769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4515004848168764520628717 1693126818063286695235769)
              ·
                refine ⟨1269845113547465021426827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693126818063286695235769 1269845113547465021426827)
                ·
                  refine ⟨1904767670321197532140241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1269845113547465021426827 1904767670321197532140241)
                  ·
                    refine ⟨1428575752740898149105181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1904767670321197532140241 1428575752740898149105181)
                    ·
                      refine ⟨535715907277836805914443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428575752740898149105181 535715907277836805914443)
                      ·
                        rfl

theorem cell23_1043303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_1043303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043303 prefixEnd_1043303 := by exact prefixLift 1043303
  have htrace : WordTrace (prefixWord ++ tailWord_1043303) baseStart_1043303 baseEnd_1043303 := by
    simpa [prefixWord, tailWord_1043303, baseEnd_1043303] using wordTrace_append hprefix tailTrace_1043303
  have hstable : (prefixWord ++ tailWord_1043303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043303).length < 2 ^ (prefixWord ++ tailWord_1043303).sum := by decide
  have hdescent : baseEnd_1043303 < baseStart_1043303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043333 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_1043333 : Nat := 118140960795 + 1043333 * 2 ^ 59
def prefixEnd_1043333 : Nat := 4983230072969 + 3 ^ 40 * 1043333 * 2
def baseEnd_1043333 : Nat := 535731311697471688539305

theorem tailTrace_1043333 : CollatzResearch.WordTrace tailWord_1043333 prefixEnd_1043333 535731311697471688539305 := by
  unfold tailWord_1043333
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053480729190202935310653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25368987152793468623540435 38053480729190202935310653)
  ·
    refine ⟨14270055273446326100741495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38053480729190202935310653 14270055273446326100741495)
    ·
      refine ⟨21405082910169489151112243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14270055273446326100741495 21405082910169489151112243)
      ·
        refine ⟨32107624365254233726668365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21405082910169489151112243 32107624365254233726668365)
        ·
          refine ⟨12040359136970337647500637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32107624365254233726668365 12040359136970337647500637)
          ·
            refine ⟨4515134676363876617812739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12040359136970337647500637 4515134676363876617812739)
            ·
              refine ⟨6772702014545814926719109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515134676363876617812739 6772702014545814926719109)
              ·
                refine ⟨1269881627727340298759833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6772702014545814926719109 1269881627727340298759833)
                ·
                  refine ⟨952411220795505224069875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1269881627727340298759833 952411220795505224069875)
                  ·
                    refine ⟨1428616831193257836104813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 952411220795505224069875 1428616831193257836104813)
                    ·
                      refine ⟨535731311697471688539305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428616831193257836104813 535731311697471688539305)
                      ·
                        rfl

theorem cell23_1043333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_1043333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043333 prefixEnd_1043333 := by exact prefixLift 1043333
  have htrace : WordTrace (prefixWord ++ tailWord_1043333) baseStart_1043333 baseEnd_1043333 := by
    simpa [prefixWord, tailWord_1043333, baseEnd_1043333] using wordTrace_append hprefix tailTrace_1043333
  have hstable : (prefixWord ++ tailWord_1043333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043333).length < 2 ^ (prefixWord ++ tailWord_1043333).sum := by decide
  have hdescent : baseEnd_1043333 < baseStart_1043333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043339 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_1043339 : Nat := 118140960795 + 1043339 * 2 ^ 59
def prefixEnd_1043339 : Nat := 4983230072969 + 3 ^ 40 * 1043339 * 2
def baseEnd_1043339 : Nat := 535734392581398665064277

theorem tailTrace_1043339 : CollatzResearch.WordTrace tailWord_1043339 prefixEnd_1043339 535734392581398665064277 := by
  unfold tailWord_1043339
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053699567168465960029071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369133044778977306686047 38053699567168465960029071)
  ·
    refine ⟨57080549350752698940043607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38053699567168465960029071 57080549350752698940043607)
    ·
      refine ⟨85620824026129048410065411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57080549350752698940043607 85620824026129048410065411)
      ·
        refine ⟨128431236039193572615098117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85620824026129048410065411 128431236039193572615098117)
        ·
          refine ⟨24080856757348794865330897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128431236039193572615098117 24080856757348794865330897)
          ·
            refine ⟨18060642568011596148998173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24080856757348794865330897 18060642568011596148998173)
            ·
              refine ⟨6772740963004348555874315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18060642568011596148998173 6772740963004348555874315)
              ·
                refine ⟨10159111444506522833811473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772740963004348555874315 10159111444506522833811473)
                ·
                  refine ⟨7619333583379892125358605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10159111444506522833811473 7619333583379892125358605)
                  ·
                    refine ⟨2857250093767459547009477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7619333583379892125358605 2857250093767459547009477)
                    ·
                      refine ⟨535734392581398665064277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2857250093767459547009477 535734392581398665064277)
                      ·
                        rfl

theorem cell23_1043339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_1043339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043339 prefixEnd_1043339 := by exact prefixLift 1043339
  have htrace : WordTrace (prefixWord ++ tailWord_1043339) baseStart_1043339 baseEnd_1043339 := by
    simpa [prefixWord, tailWord_1043339, baseEnd_1043339] using wordTrace_append hprefix tailTrace_1043339
  have hstable : (prefixWord ++ tailWord_1043339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043339).length < 2 ^ (prefixWord ++ tailWord_1043339).sum := by decide
  have hdescent : baseEnd_1043339 < baseStart_1043339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043349 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1043349 : Nat := 118140960795 + 1043349 * 2 ^ 59
def prefixEnd_1043349 : Nat := 4983230072969 + 3 ^ 40 * 1043349 * 2
def baseEnd_1043349 : Nat := 178579842462647875313077

theorem tailTrace_1043349 : CollatzResearch.WordTrace tailWord_1043349 prefixEnd_1043349 178579842462647875313077 := by
  unfold tailWord_1043349
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054064297132237667893101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369376198088158445262067 38054064297132237667893101)
  ·
    refine ⟨14270274111424589125459913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38054064297132237667893101 14270274111424589125459913)
    ·
      refine ⟨10702705583568441844094935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14270274111424589125459913 10702705583568441844094935)
      ·
        refine ⟨16054058375352662766142403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702705583568441844094935 16054058375352662766142403)
        ·
          refine ⟨24081087563028994149213605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16054058375352662766142403 24081087563028994149213605)
          ·
            refine ⟨4515203918067936402977551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24081087563028994149213605 4515203918067936402977551)
            ·
              refine ⟨6772805877101904604466327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515203918067936402977551 6772805877101904604466327)
              ·
                refine ⟨10159208815652856906699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772805877101904604466327 10159208815652856906699491)
                ·
                  refine ⟨15238813223479285360049237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159208815652856906699491 15238813223479285360049237)
                  ·
                    refine ⟨178579842462647875313077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15238813223479285360049237 178579842462647875313077)
                    ·
                      rfl

theorem cell23_1043349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1043349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043349 prefixEnd_1043349 := by exact prefixLift 1043349
  have htrace : WordTrace (prefixWord ++ tailWord_1043349) baseStart_1043349 baseEnd_1043349 := by
    simpa [prefixWord, tailWord_1043349, baseEnd_1043349] using wordTrace_append hprefix tailTrace_1043349
  have hstable : (prefixWord ++ tailWord_1043349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043349).length < 2 ^ (prefixWord ++ tailWord_1043349).sum := by decide
  have hdescent : baseEnd_1043349 < baseStart_1043349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043369 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_1043369 : Nat := 118140960795 + 1043369 * 2 ^ 59
def prefixEnd_1043369 : Nat := 4983230072969 + 3 ^ 40 * 1043369 * 2
def baseEnd_1043369 : Nat := 535749797001033547689139

theorem tailTrace_1043369 : CollatzResearch.WordTrace tailWord_1043369 prefixEnd_1043369 535749797001033547689139 := by
  unfold tailWord_1043369
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054793757059781083621161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369862504706520722414107 38054793757059781083621161)
  ·
    refine ⟨28541095317794835812715871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38054793757059781083621161 28541095317794835812715871)
    ·
      refine ⟨42811642976692253719073807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28541095317794835812715871 42811642976692253719073807)
      ·
        refine ⟨64217464465038380578610711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42811642976692253719073807 64217464465038380578610711)
        ·
          refine ⟨96326196697557570867916067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64217464465038380578610711 96326196697557570867916067)
          ·
            refine ⟨144489295046336356301874101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96326196697557570867916067 144489295046336356301874101)
            ·
              refine ⟨13545871410594033403300697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144489295046336356301874101 13545871410594033403300697)
              ·
                refine ⟨10159403557945525052475523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13545871410594033403300697 10159403557945525052475523)
                ·
                  refine ⟨15239105336918287578713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159403557945525052475523 15239105336918287578713285)
                  ·
                    refine ⟨2857332250672178921008741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15239105336918287578713285 2857332250672178921008741)
                    ·
                      refine ⟨535749797001033547689139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2857332250672178921008741 535749797001033547689139)
                      ·
                        rfl

theorem cell23_1043369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_1043369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043369 prefixEnd_1043369 := by exact prefixLift 1043369
  have htrace : WordTrace (prefixWord ++ tailWord_1043369) baseStart_1043369 baseEnd_1043369 := by
    simpa [prefixWord, tailWord_1043369, baseEnd_1043369] using wordTrace_append hprefix tailTrace_1043369
  have hstable : (prefixWord ++ tailWord_1043369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043369).length < 2 ^ (prefixWord ++ tailWord_1043369).sum := by decide
  have hdescent : baseEnd_1043369 < baseStart_1043369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043390 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_1043390 : Nat := 118140960795 + 1043390 * 2 ^ 59
def prefixEnd_1043390 : Nat := 4983230072969 + 3 ^ 40 * 1043390 * 2
def baseEnd_1043390 : Nat := 535760580094777965526543

theorem tailTrace_1043390 : CollatzResearch.WordTrace tailWord_1043390 prefixEnd_1043390 535760580094777965526543 := by
  unfold tailWord_1043390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756944961247962708766953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25370373126655801113423749 4756944961247962708766953)
  ·
    refine ⟨3567708720935972031575215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4756944961247962708766953 3567708720935972031575215)
    ·
      refine ⟨5351563081403958047362823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567708720935972031575215 5351563081403958047362823)
      ·
        refine ⟨8027344622105937071044235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351563081403958047362823 8027344622105937071044235)
        ·
          refine ⟨12041016933158905606566353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027344622105937071044235 12041016933158905606566353)
          ·
            refine ⟨9030762699869179204924765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12041016933158905606566353 9030762699869179204924765)
            ·
              refine ⟨3386536012450942201846787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9030762699869179204924765 3386536012450942201846787)
              ·
                refine ⟨5079804018676413302770181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386536012450942201846787 5079804018676413302770181)
                ·
                  refine ⟨952463253501827494269409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5079804018676413302770181 952463253501827494269409)
                  ·
                    refine ⟨714347440126370620702057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952463253501827494269409 714347440126370620702057)
                    ·
                      refine ⟨535760580094777965526543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714347440126370620702057 535760580094777965526543)
                      ·
                        rfl

theorem cell23_1043390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_1043390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043390 prefixEnd_1043390 := by exact prefixLift 1043390
  have htrace : WordTrace (prefixWord ++ tailWord_1043390) baseStart_1043390 baseEnd_1043390 := by
    simpa [prefixWord, tailWord_1043390, baseEnd_1043390] using wordTrace_append hprefix tailTrace_1043390
  have hstable : (prefixWord ++ tailWord_1043390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043390).length < 2 ^ (prefixWord ++ tailWord_1043390).sum := by decide
  have hdescent : baseEnd_1043390 < baseStart_1043390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043407 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 2, 2, 2]
def baseStart_1043407 : Nat := 118140960795 + 1043407 * 2 ^ 59
def prefixEnd_1043407 : Nat := 4983230072969 + 3 ^ 40 * 1043407 * 2
def baseEnd_1043407 : Nat := 535769309265904399013965

theorem tailTrace_1043407 : CollatzResearch.WordTrace tailWord_1043407 prefixEnd_1043407 535769309265904399013965 := by
  unfold tailWord_1043407
  simp only [CollatzResearch.WordTrace]
  refine ⟨38056179730922113573504475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25370786487281409049002983 38056179730922113573504475)
  ·
    refine ⟨57084269596383170360256713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38056179730922113573504475 57084269596383170360256713)
    ·
      refine ⟨42813202197287377770192535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57084269596383170360256713 42813202197287377770192535)
      ·
        refine ⟨64219803295931066655288803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42813202197287377770192535 64219803295931066655288803)
        ·
          refine ⟨96329704943896599982933205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64219803295931066655288803 96329704943896599982933205)
          ·
            refine ⟨2257727459622576562099997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 96329704943896599982933205 2257727459622576562099997)
            ·
              refine ⟨846647797358466210787499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257727459622576562099997 846647797358466210787499)
              ·
                refine ⟨1269971696037699316181249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846647797358466210787499 1269971696037699316181249)
                ·
                  refine ⟨952478772028274487135937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1269971696037699316181249 952478772028274487135937)
                  ·
                    refine ⟨714359079021205865351953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952478772028274487135937 714359079021205865351953)
                    ·
                      refine ⟨535769309265904399013965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714359079021205865351953 535769309265904399013965)
                      ·
                        rfl

theorem cell23_1043407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 2, 2].length) (baseStart_1043407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043407 prefixEnd_1043407 := by exact prefixLift 1043407
  have htrace : WordTrace (prefixWord ++ tailWord_1043407) baseStart_1043407 baseEnd_1043407 := by
    simpa [prefixWord, tailWord_1043407, baseEnd_1043407] using wordTrace_append hprefix tailTrace_1043407
  have hstable : (prefixWord ++ tailWord_1043407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043407).length < 2 ^ (prefixWord ++ tailWord_1043407).sum := by decide
  have hdescent : baseEnd_1043407 < baseStart_1043407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043409 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_1043409 : Nat := 118140960795 + 1043409 * 2 ^ 59
def prefixEnd_1043409 : Nat := 4983230072969 + 3 ^ 40 * 1043409 * 2
def baseEnd_1043409 : Nat := 178590112075737797062985

theorem tailTrace_1043409 : CollatzResearch.WordTrace tailWord_1043409 prefixEnd_1043409 178590112075737797062985 := by
  unfold tailWord_1043409
  simp only [CollatzResearch.WordTrace]
  refine ⟨38056252676914867915077281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25370835117943245276718187 38056252676914867915077281)
  ·
    refine ⟨28542189507686150936307961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38056252676914867915077281 28542189507686150936307961)
    ·
      refine ⟨21406642130764613202230971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28542189507686150936307961 21406642130764613202230971)
      ·
        refine ⟨32109963196146919803346457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406642130764613202230971 32109963196146919803346457)
        ·
          refine ⟨24082472397110189852509843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32109963196146919803346457 24082472397110189852509843)
          ·
            refine ⟨36123708595665284778764765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24082472397110189852509843 36123708595665284778764765)
            ·
              refine ⟨13546390723374481792036787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36123708595665284778764765 13546390723374481792036787)
              ·
                refine ⟨20319586085061722688055181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13546390723374481792036787 20319586085061722688055181)
                ·
                  refine ⟨7619844781898146008020693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20319586085061722688055181 7619844781898146008020693)
                  ·
                    refine ⟨178590112075737797062985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7619844781898146008020693 178590112075737797062985)
                    ·
                      rfl

theorem cell23_1043409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_1043409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043409 prefixEnd_1043409 := by exact prefixLift 1043409
  have htrace : WordTrace (prefixWord ++ tailWord_1043409) baseStart_1043409 baseEnd_1043409 := by
    simpa [prefixWord, tailWord_1043409, baseEnd_1043409] using wordTrace_append hprefix tailTrace_1043409
  have hstable : (prefixWord ++ tailWord_1043409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043409).length < 2 ^ (prefixWord ++ tailWord_1043409).sum := by decide
  have hdescent : baseEnd_1043409 < baseStart_1043409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043458 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1043458 : Nat := 118140960795 + 1043458 * 2 ^ 59
def prefixEnd_1043458 : Nat := 4983230072969 + 3 ^ 40 * 1043458 * 2
def baseEnd_1043458 : Nat := 535795496779283699476231

theorem tailTrace_1043458 : CollatzResearch.WordTrace tailWord_1043458 prefixEnd_1043458 535795496779283699476231 := by
  unfold tailWord_1043458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514509963434337320902757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25372026569158232855740685 9514509963434337320902757)
  ·
    refine ⟨1783970618143938247669267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9514509963434337320902757 1783970618143938247669267)
    ·
      refine ⟨2675955927215907371503901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783970618143938247669267 2675955927215907371503901)
      ·
        refine ⟨1003483472705965264313963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2675955927215907371503901 1003483472705965264313963)
        ·
          refine ⟨1505225209058947896470945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003483472705965264313963 1505225209058947896470945)
          ·
            refine ⟨1128918906794210922353209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505225209058947896470945 1128918906794210922353209)
            ·
              refine ⟨846689180095658191764907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128918906794210922353209 846689180095658191764907)
              ·
                refine ⟨1270033770143487287647361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846689180095658191764907 1270033770143487287647361)
                ·
                  refine ⟨952525327607615465735521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270033770143487287647361 952525327607615465735521)
                  ·
                    refine ⟨714393995705711599301641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952525327607615465735521 714393995705711599301641)
                    ·
                      refine ⟨535795496779283699476231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714393995705711599301641 535795496779283699476231)
                      ·
                        rfl

theorem cell23_1043458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1043458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043458 prefixEnd_1043458 := by exact prefixLift 1043458
  have htrace : WordTrace (prefixWord ++ tailWord_1043458) baseStart_1043458 baseEnd_1043458 := by
    simpa [prefixWord, tailWord_1043458, baseEnd_1043458] using wordTrace_append hprefix tailTrace_1043458
  have hstable : (prefixWord ++ tailWord_1043458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043458).length < 2 ^ (prefixWord ++ tailWord_1043458).sum := by decide
  have hdescent : baseEnd_1043458 < baseStart_1043458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043463 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_1043463 : Nat := 118140960795 + 1043463 * 2 ^ 59
def prefixEnd_1043463 : Nat := 4983230072969 + 3 ^ 40 * 1043463 * 2
def baseEnd_1043463 : Nat := 535798064182556179913707

theorem tailTrace_1043463 : CollatzResearch.WordTrace tailWord_1043463 prefixEnd_1043463 535798064182556179913707 := by
  unfold tailWord_1043463
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058222218719235137543043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25372148145812823425028695 38058222218719235137543043)
  ·
    refine ⟨57087333328078852706314565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38058222218719235137543043 57087333328078852706314565)
    ·
      refine ⟨10703874999014784882433981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57087333328078852706314565 10703874999014784882433981)
      ·
        refine ⟨4013953124630544330912743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10703874999014784882433981 4013953124630544330912743)
        ·
          refine ⟨6020929686945816496369115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013953124630544330912743 6020929686945816496369115)
          ·
            refine ⟨9031394530418724744553673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020929686945816496369115 9031394530418724744553673)
            ·
              refine ⟨6773545897814043558415255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031394530418724744553673 6773545897814043558415255)
              ·
                refine ⟨10160318846721065337622883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773545897814043558415255 10160318846721065337622883)
                ·
                  refine ⟨15240478270081598006434325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160318846721065337622883 15240478270081598006434325)
                  ·
                    refine ⟨714397418910074906551609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15240478270081598006434325 714397418910074906551609)
                    ·
                      refine ⟨535798064182556179913707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714397418910074906551609 535798064182556179913707)
                      ·
                        rfl

theorem cell23_1043463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_1043463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043463 prefixEnd_1043463 := by exact prefixLift 1043463
  have htrace : WordTrace (prefixWord ++ tailWord_1043463) baseStart_1043463 baseEnd_1043463 := by
    simpa [prefixWord, tailWord_1043463, baseEnd_1043463] using wordTrace_append hprefix tailTrace_1043463
  have hstable : (prefixWord ++ tailWord_1043463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043463).length < 2 ^ (prefixWord ++ tailWord_1043463).sum := by decide
  have hdescent : baseEnd_1043463 < baseStart_1043463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043506 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1043506 : Nat := 118140960795 + 1043506 * 2 ^ 59
def prefixEnd_1043506 : Nat := 4983230072969 + 3 ^ 40 * 1043506 * 2
def baseEnd_1043506 : Nat := 535820143850699511676009

theorem tailTrace_1043506 : CollatzResearch.WordTrace tailWord_1043506 prefixEnd_1043506 535820143850699511676009 := by
  unfold tailWord_1043506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514947639390863370339593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25373193705042302320905581 9514947639390863370339593)
  ·
    refine ⟨7136210729543147527754695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9514947639390863370339593 7136210729543147527754695)
    ·
      refine ⟨10704316094314721291632043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136210729543147527754695 10704316094314721291632043)
      ·
        refine ⟨16056474141472081937448065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704316094314721291632043 16056474141472081937448065)
        ·
          refine ⟨12042355606104061453086049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16056474141472081937448065 12042355606104061453086049)
          ·
            refine ⟨9031766704578046089814537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12042355606104061453086049 9031766704578046089814537)
            ·
              refine ⟨6773825028433534567360903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031766704578046089814537 6773825028433534567360903)
              ·
                refine ⟨10160737542650301851041355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773825028433534567360903 10160737542650301851041355)
                ·
                  refine ⟨15241106313975452776562033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10160737542650301851041355 15241106313975452776562033)
                  ·
                    refine ⟨11430829735481589582421525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15241106313975452776562033 11430829735481589582421525)
                    ·
                      refine ⟨535820143850699511676009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11430829735481589582421525 535820143850699511676009)
                      ·
                        rfl

theorem cell23_1043506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1043506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043506 prefixEnd_1043506 := by exact prefixLift 1043506
  have htrace : WordTrace (prefixWord ++ tailWord_1043506) baseStart_1043506 baseEnd_1043506 := by
    simpa [prefixWord, tailWord_1043506, baseEnd_1043506] using wordTrace_append hprefix tailTrace_1043506
  have hstable : (prefixWord ++ tailWord_1043506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043506).length < 2 ^ (prefixWord ++ tailWord_1043506).sum := by decide
  have hdescent : baseEnd_1043506 < baseStart_1043506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043523 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 5, 2]
def baseStart_1043523 : Nat := 118140960795 + 1043523 * 2 ^ 59
def prefixEnd_1043523 : Nat := 4983230072969 + 3 ^ 40 * 1043523 * 2
def baseEnd_1043523 : Nat := 535828873021825945163431

theorem tailTrace_1043523 : CollatzResearch.WordTrace tailWord_1043523 prefixEnd_1043523 535828873021825945163431 := by
  unfold tailWord_1043523
  simp only [CollatzResearch.WordTrace]
  refine ⟨38060410598501865384727223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25373607065667910256484815 38060410598501865384727223)
  ·
    refine ⟨57090615897752798077090835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38060410598501865384727223 57090615897752798077090835)
    ·
      refine ⟨85635923846629197115636253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57090615897752798077090835 85635923846629197115636253)
      ·
        refine ⟨32113471442485948918363595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85635923846629197115636253 32113471442485948918363595)
        ·
          refine ⟨48170207163728923377545393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32113471442485948918363595 48170207163728923377545393)
          ·
            refine ⟨36127655372796692533159045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48170207163728923377545393 36127655372796692533159045)
            ·
              refine ⟨6773935382399379849967321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36127655372796692533159045 6773935382399379849967321)
              ·
                refine ⟨5080451536799534887475491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6773935382399379849967321 5080451536799534887475491)
                ·
                  refine ⟨7620677305199302331213237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5080451536799534887475491 7620677305199302331213237)
                  ·
                    refine ⟨714438497362434593551241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7620677305199302331213237 714438497362434593551241)
                    ·
                      refine ⟨535828873021825945163431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714438497362434593551241 535828873021825945163431)
                      ·
                        rfl

theorem cell23_1043523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_1043523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043523 prefixEnd_1043523 := by exact prefixLift 1043523
  have htrace : WordTrace (prefixWord ++ tailWord_1043523) baseStart_1043523 baseEnd_1043523 := by
    simpa [prefixWord, tailWord_1043523, baseEnd_1043523] using wordTrace_append hprefix tailTrace_1043523
  have hstable : (prefixWord ++ tailWord_1043523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043523).length < 2 ^ (prefixWord ++ tailWord_1043523).sum := by decide
  have hdescent : baseEnd_1043523 < baseStart_1043523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043546 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_1043546 : Nat := 118140960795 + 1043546 * 2 ^ 59
def prefixEnd_1043546 : Nat := 4983230072969 + 3 ^ 40 * 1043546 * 2
def baseEnd_1043546 : Nat := 178613561025626451725275

theorem tailTrace_1043546 : CollatzResearch.WordTrace tailWord_1043546 prefixEnd_1043546 178613561025626451725275 := by
  unfold tailWord_1043546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515312369354635078203623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25374166318279026875209661 9515312369354635078203623)
  ·
    refine ⟨14272968554031952617305435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515312369354635078203623 14272968554031952617305435)
    ·
      refine ⟨21409452831047928925958153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14272968554031952617305435 21409452831047928925958153)
      ·
        refine ⟨16057089623285946694468615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21409452831047928925958153 16057089623285946694468615)
        ·
          refine ⟨24085634434928920041702923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057089623285946694468615 24085634434928920041702923)
          ·
            refine ⟨36128451652393380062554385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24085634434928920041702923 36128451652393380062554385)
            ·
              refine ⟨27096338739295035046915789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36128451652393380062554385 27096338739295035046915789)
              ·
                refine ⟨10161127027235638142593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27096338739295035046915789 10161127027235638142593421)
                ·
                  refine ⟨3810422635213364303472533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10161127027235638142593421 3810422635213364303472533)
                  ·
                    refine ⟨178613561025626451725275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3810422635213364303472533 178613561025626451725275)
                    ·
                      rfl

theorem cell23_1043546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_1043546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043546 prefixEnd_1043546 := by exact prefixLift 1043546
  have htrace : WordTrace (prefixWord ++ tailWord_1043546) baseStart_1043546 baseEnd_1043546 := by
    simpa [prefixWord, tailWord_1043546, baseEnd_1043546] using wordTrace_append hprefix tailTrace_1043546
  have hstable : (prefixWord ++ tailWord_1043546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043546).length < 2 ^ (prefixWord ++ tailWord_1043546).sum := by decide
  have hdescent : baseEnd_1043546 < baseStart_1043546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043593 : List Nat := [1, 2, 1, 1, 4, 3, 4, 7]
def baseStart_1043593 : Nat := 118140960795 + 1043593 * 2 ^ 59
def prefixEnd_1043593 : Nat := 4983230072969 + 3 ^ 40 * 1043593 * 2
def baseEnd_1043593 : Nat := 19846845061764469306967

theorem tailTrace_1043593 : CollatzResearch.WordTrace tailWord_1043593 prefixEnd_1043593 19846845061764469306967 := by
  unfold tailWord_1043593
  simp only [CollatzResearch.WordTrace]
  refine ⟨38062963708248267339775433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25375309138832178226516955 38062963708248267339775433)
  ·
    refine ⟨28547222781186200504831575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38062963708248267339775433 28547222781186200504831575)
    ·
      refine ⟨42820834171779300757247363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28547222781186200504831575 42820834171779300757247363)
      ·
        refine ⟨64231251257668951135871045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42820834171779300757247363 64231251257668951135871045)
        ·
          refine ⟨12043359610812928337975821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64231251257668951135871045 12043359610812928337975821)
          ·
            refine ⟨4516259854054848126740933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12043359610812928337975821 4516259854054848126740933)
            ·
              refine ⟨846798722635284023763925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4516259854054848126740933 846798722635284023763925)
              ·
                refine ⟨19846845061764469306967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 846798722635284023763925 19846845061764469306967)
                ·
                  rfl

theorem cell23_1043593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 7].length) (baseStart_1043593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043593 prefixEnd_1043593 := by exact prefixLift 1043593
  have htrace : WordTrace (prefixWord ++ tailWord_1043593) baseStart_1043593 baseEnd_1043593 := by
    simpa [prefixWord, tailWord_1043593, baseEnd_1043593] using wordTrace_append hprefix tailTrace_1043593
  have hstable : (prefixWord ++ tailWord_1043593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043593).length < 2 ^ (prefixWord ++ tailWord_1043593).sum := by decide
  have hdescent : baseEnd_1043593 < baseStart_1043593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043596 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1043596 : Nat := 118140960795 + 1043596 * 2 ^ 59
def prefixEnd_1043596 : Nat := 4983230072969 + 3 ^ 40 * 1043596 * 2
def baseEnd_1043596 : Nat := 535866357109604159550595

theorem tailTrace_1043596 : CollatzResearch.WordTrace tailWord_1043596 prefixEnd_1043596 535866357109604159550595 := by
  unfold tailWord_1043596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031536563618699426067321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25375382084824932568089761 19031536563618699426067321)
  ·
    refine ⟨14273652422714024569550491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19031536563618699426067321 14273652422714024569550491)
    ·
      refine ⟨21410478634071036854325737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273652422714024569550491 21410478634071036854325737)
      ·
        refine ⟨16057858975553277640744303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410478634071036854325737 16057858975553277640744303)
        ·
          refine ⟨24086788463329916461116455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057858975553277640744303 24086788463329916461116455)
          ·
            refine ⟨36130182694994874691674683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24086788463329916461116455 36130182694994874691674683)
            ·
              refine ⟨54195274042492312037512025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36130182694994874691674683 54195274042492312037512025)
              ·
                refine ⟨40646455531869234028134019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54195274042492312037512025 40646455531869234028134019)
                ·
                  refine ⟨60969683297803851042201029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40646455531869234028134019 60969683297803851042201029)
                  ·
                    refine ⟨11431815618338222070412693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60969683297803851042201029 11431815618338222070412693)
                    ·
                      refine ⟨535866357109604159550595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11431815618338222070412693 535866357109604159550595)
                      ·
                        rfl

theorem cell23_1043596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1043596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043596 prefixEnd_1043596 := by exact prefixLift 1043596
  have htrace : WordTrace (prefixWord ++ tailWord_1043596) baseStart_1043596 baseEnd_1043596 := by
    simpa [prefixWord, tailWord_1043596, baseEnd_1043596] using wordTrace_append hprefix tailTrace_1043596
  have hstable : (prefixWord ++ tailWord_1043596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043596).length < 2 ^ (prefixWord ++ tailWord_1043596).sum := by decide
  have hdescent : baseEnd_1043596 < baseStart_1043596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043603 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3]
def baseStart_1043603 : Nat := 118140960795 + 1043603 * 2 ^ 59
def prefixEnd_1043603 : Nat := 4983230072969 + 3 ^ 40 * 1043603 * 2
def baseEnd_1043603 : Nat := 535869951474185632163063

theorem tailTrace_1043603 : CollatzResearch.WordTrace tailWord_1043603 prefixEnd_1043603 535869951474185632163063 := by
  unfold tailWord_1043603
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063328438212039047639463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25375552292141359365092975 38063328438212039047639463)
  ·
    refine ⟨57094992657318058571459195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38063328438212039047639463 57094992657318058571459195)
    ·
      refine ⟨85642488985977087857188793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57094992657318058571459195 85642488985977087857188793)
      ·
        refine ⟨64231866739482815892891595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85642488985977087857188793 64231866739482815892891595)
        ·
          refine ⟨96347800109224223839337393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64231866739482815892891595 96347800109224223839337393)
          ·
            refine ⟨72260850081918167879503045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96347800109224223839337393 72260850081918167879503045)
            ·
              refine ⟨13548909390359656477406821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72260850081918167879503045 13548909390359656477406821)
              ·
                refine ⟨2540420510692435589513779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13548909390359656477406821 2540420510692435589513779)
                ·
                  refine ⟨3810630766038653384270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2540420510692435589513779 3810630766038653384270669)
                  ·
                    refine ⟨1428986537264495019101501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3810630766038653384270669 1428986537264495019101501)
                    ·
                      refine ⟨535869951474185632163063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1428986537264495019101501 535869951474185632163063)
                      ·
                        rfl

theorem cell23_1043603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_1043603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043603 prefixEnd_1043603 := by exact prefixLift 1043603
  have htrace : WordTrace (prefixWord ++ tailWord_1043603) baseStart_1043603 baseEnd_1043603 := by
    simpa [prefixWord, tailWord_1043603, baseEnd_1043603] using wordTrace_append hprefix tailTrace_1043603
  have hstable : (prefixWord ++ tailWord_1043603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043603).length < 2 ^ (prefixWord ++ tailWord_1043603).sum := by decide
  have hdescent : baseEnd_1043603 < baseStart_1043603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043621 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 1, 2, 2]
def baseStart_1043621 : Nat := 118140960795 + 1043621 * 2 ^ 59
def prefixEnd_1043621 : Nat := 4983230072969 + 3 ^ 40 * 1043621 * 2
def baseEnd_1043621 : Nat := 535879194125966561737981

theorem tailTrace_1043621 : CollatzResearch.WordTrace tailWord_1043621 prefixEnd_1043621 535879194125966561737981 := by
  unfold tailWord_1043621
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063984952146828121794717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25375989968097885414529811 38063984952146828121794717)
  ·
    refine ⟨14273994357055060545673019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38063984952146828121794717 14273994357055060545673019)
    ·
      refine ⟨21410991535582590818509529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273994357055060545673019 21410991535582590818509529)
      ·
        refine ⟨16058243651686943113882147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410991535582590818509529 16058243651686943113882147)
        ·
          refine ⟨24087365477530414670823221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16058243651686943113882147 24087365477530414670823221)
          ·
            refine ⟨2258190513518476375389677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24087365477530414670823221 2258190513518476375389677)
            ·
              refine ⟨846821442569428640771129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2258190513518476375389677 846821442569428640771129)
              ·
                refine ⟨635116081927071480578347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846821442569428640771129 635116081927071480578347)
                ·
                  refine ⟨952674122890607220867521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635116081927071480578347 952674122890607220867521)
                  ·
                    refine ⟨714505592167955415650641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952674122890607220867521 714505592167955415650641)
                    ·
                      refine ⟨535879194125966561737981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714505592167955415650641 535879194125966561737981)
                      ·
                        rfl

theorem cell23_1043621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_1043621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043621 prefixEnd_1043621 := by exact prefixLift 1043621
  have htrace : WordTrace (prefixWord ++ tailWord_1043621) baseStart_1043621 baseEnd_1043621 := by
    simpa [prefixWord, tailWord_1043621, baseEnd_1043621] using wordTrace_append hprefix tailTrace_1043621
  have hstable : (prefixWord ++ tailWord_1043621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043621).length < 2 ^ (prefixWord ++ tailWord_1043621).sum := by decide
  have hdescent : baseEnd_1043621 < baseStart_1043621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043638 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1043638 : Nat := 118140960795 + 1043638 * 2 ^ 59
def prefixEnd_1043638 : Nat := 4983230072969 + 3 ^ 40 * 1043638 * 2
def baseEnd_1043638 : Nat := 535887923297092995225403

theorem tailTrace_1043638 : CollatzResearch.WordTrace tailWord_1043638 prefixEnd_1043638 535887923297092995225403 := by
  unfold tailWord_1043638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379037812067827501572723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25376403328723493350109045 2379037812067827501572723)
  ·
    refine ⟨3568556718101741252359085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379037812067827501572723 3568556718101741252359085)
    ·
      refine ⟨1338208769288152969634657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3568556718101741252359085 1338208769288152969634657)
      ·
        refine ⟨1003656576966114727225993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1338208769288152969634657 1003656576966114727225993)
        ·
          refine ⟨752742432724586045419495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003656576966114727225993 752742432724586045419495)
          ·
            refine ⟨1129113649086879068129243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752742432724586045419495 1129113649086879068129243)
            ·
              refine ⟨1693670473630318602193865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129113649086879068129243 1693670473630318602193865)
              ·
                refine ⟨1270252855222738951645399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693670473630318602193865 1270252855222738951645399)
                ·
                  refine ⟨1905379282834108427468099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270252855222738951645399 1905379282834108427468099)
                  ·
                    refine ⟨2858068924251162641202149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1905379282834108427468099 2858068924251162641202149)
                    ·
                      refine ⟨535887923297092995225403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2858068924251162641202149 535887923297092995225403)
                      ·
                        rfl

theorem cell23_1043638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1043638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043638 prefixEnd_1043638 := by exact prefixLift 1043638
  have htrace : WordTrace (prefixWord ++ tailWord_1043638) baseStart_1043638 baseEnd_1043638 := by
    simpa [prefixWord, tailWord_1043638, baseEnd_1043638] using wordTrace_append hprefix tailTrace_1043638
  have hstable : (prefixWord ++ tailWord_1043638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043638).length < 2 ^ (prefixWord ++ tailWord_1043638).sum := by decide
  have hdescent : baseEnd_1043638 < baseStart_1043638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043647 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 1, 3, 2]
def baseStart_1043647 : Nat := 118140960795 + 1043647 * 2 ^ 59
def prefixEnd_1043647 : Nat := 4983230072969 + 3 ^ 40 * 1043647 * 2
def baseEnd_1043647 : Nat := 535892544622983460012861

theorem tailTrace_1043647 : CollatzResearch.WordTrace tailWord_1043647 prefixEnd_1043647 535892544622983460012861 := by
  unfold tailWord_1043647
  simp only [CollatzResearch.WordTrace]
  refine ⟨38064933250052634562241195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25376622166701756374827463 38064933250052634562241195)
  ·
    refine ⟨57097399875078951843361793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38064933250052634562241195 57097399875078951843361793)
    ·
      refine ⟨42823049906309213882521345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57097399875078951843361793 42823049906309213882521345)
      ·
        refine ⟨32117287429731910411891009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42823049906309213882521345 32117287429731910411891009)
        ·
          refine ⟨24087965572298932808918257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32117287429731910411891009 24087965572298932808918257)
          ·
            refine ⟨18065974179224199606688693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24087965572298932808918257 18065974179224199606688693)
            ·
              refine ⟨1693685079302268713127065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18065974179224199606688693 1693685079302268713127065)
              ·
                refine ⟨1270263809476701534845299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693685079302268713127065 1270263809476701534845299)
                ·
                  refine ⟨1905395714215052302267949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270263809476701534845299 1905395714215052302267949)
                  ·
                    refine ⟨714523392830644613350481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905395714215052302267949 714523392830644613350481)
                    ·
                      refine ⟨535892544622983460012861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714523392830644613350481 535892544622983460012861)
                      ·
                        rfl

theorem cell23_1043647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_1043647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043647 prefixEnd_1043647 := by exact prefixLift 1043647
  have htrace : WordTrace (prefixWord ++ tailWord_1043647) baseStart_1043647 baseEnd_1043647 := by
    simpa [prefixWord, tailWord_1043647, baseEnd_1043647] using wordTrace_append hprefix tailTrace_1043647
  have hstable : (prefixWord ++ tailWord_1043647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043647).length < 2 ^ (prefixWord ++ tailWord_1043647).sum := by decide
  have hdescent : baseEnd_1043647 < baseStart_1043647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043673 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_1043673 : Nat := 118140960795 + 1043673 * 2 ^ 59
def prefixEnd_1043673 : Nat := 4983230072969 + 3 ^ 40 * 1043673 * 2
def baseEnd_1043673 : Nat := 535905895120000358287741

theorem tailTrace_1043673 : CollatzResearch.WordTrace tailWord_1043673 prefixEnd_1043673 535905895120000358287741 := by
  unfold tailWord_1043673
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065881547958441002687673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25377254365305627335125115 38065881547958441002687673)
  ·
    refine ⟨28549411160968830752015755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38065881547958441002687673 28549411160968830752015755)
    ·
      refine ⟨42824116741453246128023633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28549411160968830752015755 42824116741453246128023633)
      ·
        refine ⟨32118087556089934596017725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42824116741453246128023633 32118087556089934596017725)
        ·
          refine ⟨12044282833533725473506647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32118087556089934596017725 12044282833533725473506647)
          ·
            refine ⟨18066424250300588210259971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044282833533725473506647 18066424250300588210259971)
            ·
              refine ⟨27099636375450882315389957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18066424250300588210259971 27099636375450882315389957)
              ·
                refine ⟨5081181820397040434135617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27099636375450882315389957 5081181820397040434135617)
                ·
                  refine ⟨3810886365297780325601713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081181820397040434135617 3810886365297780325601713)
                  ·
                    refine ⟨2858164773973335244201285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810886365297780325601713 2858164773973335244201285)
                    ·
                      refine ⟨535905895120000358287741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2858164773973335244201285 535905895120000358287741)
                      ·
                        rfl

theorem cell23_1043673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_1043673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043673 prefixEnd_1043673 := by exact prefixLift 1043673
  have htrace : WordTrace (prefixWord ++ tailWord_1043673) baseStart_1043673 baseEnd_1043673 := by
    simpa [prefixWord, tailWord_1043673, baseEnd_1043673] using wordTrace_append hprefix tailTrace_1043673
  have hstable : (prefixWord ++ tailWord_1043673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043673).length < 2 ^ (prefixWord ++ tailWord_1043673).sum := by decide
  have hdescent : baseEnd_1043673 < baseStart_1043673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043690 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1043690 : Nat := 118140960795 + 1043690 * 2 ^ 59
def prefixEnd_1043690 : Nat := 4983230072969 + 3 ^ 40 * 1043690 * 2
def baseEnd_1043690 : Nat := 535914624291126791775163

theorem tailTrace_1043690 : CollatzResearch.WordTrace tailWord_1043690 prefixEnd_1043690 535914624291126791775163 := by
  unfold tailWord_1043690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516625397224213226514131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25377667725931235270704349 9516625397224213226514131)
  ·
    refine ⟨14274938095836319839771197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9516625397224213226514131 14274938095836319839771197)
    ·
      refine ⟨5353101785938619939914199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14274938095836319839771197 5353101785938619939914199)
      ·
        refine ⟨8029652678907929909871299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353101785938619939914199 8029652678907929909871299)
        ·
          refine ⟨12044479018361894864806949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8029652678907929909871299 12044479018361894864806949)
          ·
            refine ⟨2258339815942855287151303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12044479018361894864806949 2258339815942855287151303)
            ·
              refine ⟨3387509723914282930726955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258339815942855287151303 3387509723914282930726955)
              ·
                refine ⟨5081264585871424396090433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3387509723914282930726955 5081264585871424396090433)
                ·
                  refine ⟨3810948439403568297067825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5081264585871424396090433 3810948439403568297067825)
                  ·
                    refine ⟨2858211329552676222800869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810948439403568297067825 2858211329552676222800869)
                    ·
                      refine ⟨535914624291126791775163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2858211329552676222800869 535914624291126791775163)
                      ·
                        rfl

theorem cell23_1043690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1043690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043690 prefixEnd_1043690 := by exact prefixLift 1043690
  have htrace : WordTrace (prefixWord ++ tailWord_1043690) baseStart_1043690 baseEnd_1043690 := by
    simpa [prefixWord, tailWord_1043690, baseEnd_1043690] using wordTrace_append hprefix tailTrace_1043690
  have hstable : (prefixWord ++ tailWord_1043690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043690).length < 2 ^ (prefixWord ++ tailWord_1043690).sum := by decide
  have hdescent : baseEnd_1043690 < baseStart_1043690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043694 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_1043694 : Nat := 118140960795 + 1043694 * 2 ^ 59
def prefixEnd_1043694 : Nat := 4983230072969 + 3 ^ 40 * 1043694 * 2
def baseEnd_1043694 : Nat := 535916678213744776125145

theorem tailTrace_1043694 : CollatzResearch.WordTrace tailWord_1043694 prefixEnd_1043694 535916678213744776125145 := by
  unfold tailWord_1043694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758330935110295198650267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25377764987254907726134757 4758330935110295198650267)
  ·
    refine ⟨7137496402665442797975401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4758330935110295198650267 7137496402665442797975401)
    ·
      refine ⟨5353122301999082098481551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7137496402665442797975401 5353122301999082098481551)
      ·
        refine ⟨8029683452998623147722327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353122301999082098481551 8029683452998623147722327)
        ·
          refine ⟨12044525179497934721583491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8029683452998623147722327 12044525179497934721583491)
          ·
            refine ⟨18066787769246902082375237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12044525179497934721583491 18066787769246902082375237)
            ·
              refine ⟨3387522706733794140445357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18066787769246902082375237 3387522706733794140445357)
              ·
                refine ⟨1270321015025172802667009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3387522706733794140445357 1270321015025172802667009)
                ·
                  refine ⟨952740761268879602000257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270321015025172802667009 952740761268879602000257)
                  ·
                    refine ⟨714555570951659701500193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952740761268879602000257 714555570951659701500193)
                    ·
                      refine ⟨535916678213744776125145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714555570951659701500193 535916678213744776125145)
                      ·
                        rfl

theorem cell23_1043694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_1043694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043694 prefixEnd_1043694 := by exact prefixLift 1043694
  have htrace : WordTrace (prefixWord ++ tailWord_1043694) baseStart_1043694 baseEnd_1043694 := by
    simpa [prefixWord, tailWord_1043694, baseEnd_1043694] using wordTrace_append hprefix tailTrace_1043694
  have hstable : (prefixWord ++ tailWord_1043694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043694).length < 2 ^ (prefixWord ++ tailWord_1043694).sum := by decide
  have hdescent : baseEnd_1043694 < baseStart_1043694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043760 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_1043760 : Nat := 118140960795 + 1043760 * 2 ^ 59
def prefixEnd_1043760 : Nat := 4983230072969 + 3 ^ 40 * 1043760 * 2
def baseEnd_1043760 : Nat := 178650189312313839299947

theorem tailTrace_1043760 : CollatzResearch.WordTrace tailWord_1043760 prefixEnd_1043760 178650189312313839299947 := by
  unfold tailWord_1043760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034527349321627430552367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25379369799095503240736489 19034527349321627430552367)
  ·
    refine ⟨28551791023982441145828551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19034527349321627430552367 28551791023982441145828551)
    ·
      refine ⟨42827686535973661718742827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28551791023982441145828551 42827686535973661718742827)
      ·
        refine ⟨64241529803960492578114241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42827686535973661718742827 64241529803960492578114241)
        ·
          refine ⟨48181147352970369433585681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64241529803960492578114241 48181147352970369433585681)
          ·
            refine ⟨36135860514727777075189261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48181147352970369433585681 36135860514727777075189261)
            ·
              refine ⟨13550947693022916403195973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36135860514727777075189261 13550947693022916403195973)
              ·
                refine ⟨2540802692441796825599245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13550947693022916403195973 2540802692441796825599245)
                ·
                  refine ⟨952801009665673809599717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2540802692441796825599245 952801009665673809599717)
                  ·
                    refine ⟨178650189312313839299947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 952801009665673809599717 178650189312313839299947)
                    ·
                      rfl

theorem cell23_1043760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_1043760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043760 prefixEnd_1043760 := by exact prefixLift 1043760
  have htrace : WordTrace (prefixWord ++ tailWord_1043760) baseStart_1043760 baseEnd_1043760 := by
    simpa [prefixWord, tailWord_1043760, baseEnd_1043760] using wordTrace_append hprefix tailTrace_1043760
  have hstable : (prefixWord ++ tailWord_1043760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043760).length < 2 ^ (prefixWord ++ tailWord_1043760).sum := by decide
  have hdescent : baseEnd_1043760 < baseStart_1043760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043770 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_1043770 : Nat := 118140960795 + 1043770 * 2 ^ 59
def prefixEnd_1043770 : Nat := 4983230072969 + 3 ^ 40 * 1043770 * 2
def baseEnd_1043770 : Nat := 535955702743486478774795

theorem tailTrace_1043770 : CollatzResearch.WordTrace tailWord_1043770 prefixEnd_1043770 535955702743486478774795 := by
  unfold tailWord_1043770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517354857151756642242191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25379612952404684379312509 9517354857151756642242191)
  ·
    refine ⟨14276032285727634963363287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9517354857151756642242191 14276032285727634963363287)
    ·
      refine ⟨21414048428591452445044931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14276032285727634963363287 21414048428591452445044931)
      ·
        refine ⟨32121072642887178667567397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21414048428591452445044931 32121072642887178667567397)
        ·
          refine ⟨6022701120541346000168887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32121072642887178667567397 6022701120541346000168887)
          ·
            refine ⟨9034051680812019000253331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022701120541346000168887 9034051680812019000253331)
            ·
              refine ⟨13551077521218028500379997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034051680812019000253331 13551077521218028500379997)
              ·
                refine ⟨5081654070456760687642499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13551077521218028500379997 5081654070456760687642499)
                ·
                  refine ⟨7622481105685141031463749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5081654070456760687642499 7622481105685141031463749)
                  ·
                    refine ⟨1429215207315963943399453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7622481105685141031463749 1429215207315963943399453)
                    ·
                      refine ⟨535955702743486478774795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1429215207315963943399453 535955702743486478774795)
                      ·
                        rfl

theorem cell23_1043770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_1043770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043770 prefixEnd_1043770 := by exact prefixLift 1043770
  have htrace : WordTrace (prefixWord ++ tailWord_1043770) baseStart_1043770 baseEnd_1043770 := by
    simpa [prefixWord, tailWord_1043770, baseEnd_1043770] using wordTrace_append hprefix tailTrace_1043770
  have hstable : (prefixWord ++ tailWord_1043770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043770).length < 2 ^ (prefixWord ++ tailWord_1043770).sum := by decide
  have hdescent : baseEnd_1043770 < baseStart_1043770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043790 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_1043790 : Nat := 118140960795 + 1043790 * 2 ^ 59
def prefixEnd_1043790 : Nat := 4983230072969 + 3 ^ 40 * 1043790 * 2
def baseEnd_1043790 : Nat := 59551774706286266724967

theorem tailTrace_1043790 : CollatzResearch.WordTrace tailWord_1043790 prefixEnd_1043790 59551774706286266724967 := by
  unfold tailWord_1043790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758768611066821248087103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25380099259023046656464549 4758768611066821248087103)
  ·
    refine ⟨7138152916600231872130655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4758768611066821248087103 7138152916600231872130655)
    ·
      refine ⟨10707229374900347808195983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7138152916600231872130655 10707229374900347808195983)
      ·
        refine ⟨16060844062350521712293975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10707229374900347808195983 16060844062350521712293975)
        ·
          refine ⟨24091266093525782568440963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16060844062350521712293975 24091266093525782568440963)
          ·
            refine ⟨36136899140288673852661445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24091266093525782568440963 36136899140288673852661445)
            ·
              refine ⟨6775668588804126347374021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36136899140288673852661445 6775668588804126347374021)
              ·
                refine ⟨1270437860400773690132629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6775668588804126347374021 1270437860400773690132629)
                ·
                  refine ⟨59551774706286266724967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1270437860400773690132629 59551774706286266724967)
                  ·
                    rfl

theorem cell23_1043790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_1043790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043790 prefixEnd_1043790 := by exact prefixLift 1043790
  have htrace : WordTrace (prefixWord ++ tailWord_1043790) baseStart_1043790 baseEnd_1043790 := by
    simpa [prefixWord, tailWord_1043790, baseEnd_1043790] using wordTrace_append hprefix tailTrace_1043790
  have hstable : (prefixWord ++ tailWord_1043790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043790).length < 2 ^ (prefixWord ++ tailWord_1043790).sum := by decide
  have hdescent : baseEnd_1043790 < baseStart_1043790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043844 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_1043844 : Nat := 118140960795 + 1043844 * 2 ^ 59
def prefixEnd_1043844 : Nat := 4983230072969 + 3 ^ 40 * 1043844 * 2
def baseEnd_1043844 : Nat := 535993700311919189249455

theorem tailTrace_1043844 : CollatzResearch.WordTrace tailWord_1043844 prefixEnd_1043844 535993700311919189249455 := by
  unfold tailWord_1043844
  simp only [CollatzResearch.WordTrace]
  refine ⟨19036059215169468603581293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25381412286892624804775057 19036059215169468603581293)
  ·
    refine ⟨7138522205688550726342985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19036059215169468603581293 7138522205688550726342985)
    ·
      refine ⟨5353891654266413044757239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7138522205688550726342985 5353891654266413044757239)
      ·
        refine ⟨8030837481399619567135859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353891654266413044757239 8030837481399619567135859)
        ·
          refine ⟨12046256222099429350703789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030837481399619567135859 12046256222099429350703789)
          ·
            refine ⟨4517346083287286006513921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12046256222099429350703789 4517346083287286006513921)
            ·
              refine ⟨3388009562465464504885441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517346083287286006513921 3388009562465464504885441)
              ·
                refine ⟨2541007171849098378664081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388009562465464504885441 2541007171849098378664081)
                ·
                  refine ⟨1905755378886823783998061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541007171849098378664081 1905755378886823783998061)
                  ·
                    refine ⟨714658267082558918999273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1905755378886823783998061 714658267082558918999273)
                    ·
                      refine ⟨535993700311919189249455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714658267082558918999273 535993700311919189249455)
                      ·
                        rfl

theorem cell23_1043844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_1043844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043844 prefixEnd_1043844 := by exact prefixLift 1043844
  have htrace : WordTrace (prefixWord ++ tailWord_1043844) baseStart_1043844 baseEnd_1043844 := by
    simpa [prefixWord, tailWord_1043844, baseEnd_1043844] using wordTrace_append hprefix tailTrace_1043844
  have hstable : (prefixWord ++ tailWord_1043844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043844).length < 2 ^ (prefixWord ++ tailWord_1043844).sum := by decide
  have hdescent : baseEnd_1043844 < baseStart_1043844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043908 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1043908 : Nat := 118140960795 + 1043908 * 2 ^ 59
def prefixEnd_1043908 : Nat := 4983230072969 + 3 ^ 40 * 1043908 * 2
def baseEnd_1043908 : Nat := 536026563073806938849161

theorem tailTrace_1043908 : CollatzResearch.WordTrace tailWord_1043908 prefixEnd_1043908 536026563073806938849161 := by
  unfold tailWord_1043908
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037226351053538068746189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25382968468071384091661585 19037226351053538068746189)
  ·
    refine ⟨7138959881645076775779821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19037226351053538068746189 7138959881645076775779821)
    ·
      refine ⟨2677109955616903790917433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7138959881645076775779821 2677109955616903790917433)
      ·
        refine ⟨2007832466712677843188075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2677109955616903790917433 2007832466712677843188075)
        ·
          refine ⟨3011748700069016764782113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007832466712677843188075 3011748700069016764782113)
          ·
            refine ⟨2258811525051762573586585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011748700069016764782113 2258811525051762573586585)
            ·
              refine ⟨1694108643788821930189939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258811525051762573586585 1694108643788821930189939)
              ·
                refine ⟨2541162965683232895284909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694108643788821930189939 2541162965683232895284909)
                ·
                  refine ⟨952936112131212335731841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2541162965683232895284909 952936112131212335731841)
                  ·
                    refine ⟨714702084098409251798881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 952936112131212335731841 714702084098409251798881)
                    ·
                      refine ⟨536026563073806938849161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714702084098409251798881 536026563073806938849161)
                      ·
                        rfl

theorem cell23_1043908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1043908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043908 prefixEnd_1043908 := by exact prefixLift 1043908
  have htrace : WordTrace (prefixWord ++ tailWord_1043908) baseStart_1043908 baseEnd_1043908 := by
    simpa [prefixWord, tailWord_1043908, baseEnd_1043908] using wordTrace_append hprefix tailTrace_1043908
  have hstable : (prefixWord ++ tailWord_1043908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043908).length < 2 ^ (prefixWord ++ tailWord_1043908).sum := by decide
  have hdescent : baseEnd_1043908 < baseStart_1043908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043940 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_1043940 : Nat := 118140960795 + 1043940 * 2 ^ 59
def prefixEnd_1043940 : Nat := 4983230072969 + 3 ^ 40 * 1043940 * 2
def baseEnd_1043940 : Nat := 178680998151583604549671

theorem tailTrace_1043940 : CollatzResearch.WordTrace tailWord_1043940 prefixEnd_1043940 178680998151583604549671 := by
  unfold tailWord_1043940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037809918995572801328637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25383746558660763735104849 19037809918995572801328637)
  ·
    refine ⟨7139178719623339800498239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19037809918995572801328637 7139178719623339800498239)
    ·
      refine ⟨10708768079435009700747359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7139178719623339800498239 10708768079435009700747359)
      ·
        refine ⟨16063152119152514551121039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708768079435009700747359 16063152119152514551121039)
        ·
          refine ⟨24094728178728771826681559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16063152119152514551121039 24094728178728771826681559)
          ·
            refine ⟨36142092268093157740022339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24094728178728771826681559 36142092268093157740022339)
            ·
              refine ⟨54213138402139736610033509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36142092268093157740022339 54213138402139736610033509)
              ·
                refine ⟨10164963450401200614381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54213138402139736610033509 10164963450401200614381283)
                ·
                  refine ⟨15247445175601800921571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164963450401200614381283 15247445175601800921571925)
                  ·
                    refine ⟨178680998151583604549671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15247445175601800921571925 178680998151583604549671)
                    ·
                      rfl

theorem cell23_1043940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_1043940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1043940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1043940 prefixEnd_1043940 := by exact prefixLift 1043940
  have htrace : WordTrace (prefixWord ++ tailWord_1043940) baseStart_1043940 baseEnd_1043940 := by
    simpa [prefixWord, tailWord_1043940, baseEnd_1043940] using wordTrace_append hprefix tailTrace_1043940
  have hstable : (prefixWord ++ tailWord_1043940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043940).length < 2 ^ (prefixWord ++ tailWord_1043940).sum := by decide
  have hdescent : baseEnd_1043940 < baseStart_1043940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044021 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 5]
def baseStart_1044021 : Nat := 118140960795 + 1044021 * 2 ^ 59
def prefixEnd_1044021 : Nat := 4983230072969 + 3 ^ 40 * 1044021 * 2
def baseEnd_1044021 : Nat := 59564954043084999637349

theorem tailTrace_1044021 : CollatzResearch.WordTrace tailWord_1044021 prefixEnd_1044021 59564954043084999637349 := by
  unfold tailWord_1044021
  simp only [CollatzResearch.WordTrace]
  refine ⟨38078574150697696436355917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25385716100465130957570611 38078574150697696436355917)
  ·
    refine ⟨14279465306511636163633469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38078574150697696436355917 14279465306511636163633469)
    ·
      refine ⟨5354799489941863561362551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14279465306511636163633469 5354799489941863561362551)
      ·
        refine ⟨8032199234912795342043827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354799489941863561362551 8032199234912795342043827)
        ·
          refine ⟨12048298852369193013065741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032199234912795342043827 12048298852369193013065741)
          ·
            refine ⟨4518112069638447379899653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12048298852369193013065741 4518112069638447379899653)
            ·
              refine ⟨847146013057208883731185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4518112069638447379899653 847146013057208883731185)
              ·
                refine ⟨635359509792906662798389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847146013057208883731185 635359509792906662798389)
                ·
                  refine ⟨59564954043084999637349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635359509792906662798389 59564954043084999637349)
                  ·
                    rfl

theorem cell23_1044021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_1044021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044021 prefixEnd_1044021 := by exact prefixLift 1044021
  have htrace : WordTrace (prefixWord ++ tailWord_1044021) baseStart_1044021 baseEnd_1044021 := by
    simpa [prefixWord, tailWord_1044021, baseEnd_1044021] using wordTrace_append hprefix tailTrace_1044021
  have hstable : (prefixWord ++ tailWord_1044021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044021).length < 2 ^ (prefixWord ++ tailWord_1044021).sum := by decide
  have hdescent : baseEnd_1044021 < baseStart_1044021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044024 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_1044024 : Nat := 118140960795 + 1044024 * 2 ^ 59
def prefixEnd_1044024 : Nat := 4983230072969 + 3 ^ 40 * 1044024 * 2
def baseEnd_1044024 : Nat := 536086126829728484998627

theorem tailTrace_1044024 : CollatzResearch.WordTrace tailWord_1044024 prefixEnd_1044024 536086126829728484998627 := by
  unfold tailWord_1044024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039341784843413974357563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25385789046457885299143417 19039341784843413974357563)
  ·
    refine ⟨28559012677265120961536345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19039341784843413974357563 28559012677265120961536345)
    ·
      refine ⟨21419259507948840721152259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28559012677265120961536345 21419259507948840721152259)
      ·
        refine ⟨32128889261923261081728389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419259507948840721152259 32128889261923261081728389)
        ·
          refine ⟨6024166736610611452824073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32128889261923261081728389 6024166736610611452824073)
          ·
            refine ⟨4518125052457958589618055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6024166736610611452824073 4518125052457958589618055)
            ·
              refine ⟨6777187578686937884427083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518125052457958589618055 6777187578686937884427083)
              ·
                refine ⟨10165781368030406826640625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777187578686937884427083 10165781368030406826640625)
                ·
                  refine ⟨7624336026022805119980469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10165781368030406826640625 7624336026022805119980469)
                  ·
                    refine ⟨714781502439637979998169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7624336026022805119980469 714781502439637979998169)
                    ·
                      refine ⟨536086126829728484998627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714781502439637979998169 536086126829728484998627)
                      ·
                        rfl

theorem cell23_1044024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_1044024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044024 prefixEnd_1044024 := by exact prefixLift 1044024
  have htrace : WordTrace (prefixWord ++ tailWord_1044024) baseStart_1044024 baseEnd_1044024 := by
    simpa [prefixWord, tailWord_1044024, baseEnd_1044024] using wordTrace_append hprefix tailTrace_1044024
  have hstable : (prefixWord ++ tailWord_1044024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044024).length < 2 ^ (prefixWord ++ tailWord_1044024).sum := by decide
  have hdescent : baseEnd_1044024 < baseStart_1044024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044037 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_1044037 : Nat := 118140960795 + 1044037 * 2 ^ 59
def prefixEnd_1044037 : Nat := 4983230072969 + 3 ^ 40 * 1044037 * 2
def baseEnd_1044037 : Nat := 536092802078236934136067

theorem tailTrace_1044037 : CollatzResearch.WordTrace tailWord_1044037 prefixEnd_1044037 536092802078236934136067 := by
  unfold tailWord_1044037
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079157718639731168938365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25386105145759820779292243 38079157718639731168938365)
  ·
    refine ⟨14279684144489899188351887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38079157718639731168938365 14279684144489899188351887)
    ·
      refine ⟨21419526216734848782527831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279684144489899188351887 21419526216734848782527831)
      ·
        refine ⟨32129289325102273173791747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419526216734848782527831 32129289325102273173791747)
        ·
          refine ⟨48193933987653409760687621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32129289325102273173791747 48193933987653409760687621)
          ·
            refine ⟨9036362622685014330128929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48193933987653409760687621 9036362622685014330128929)
            ·
              refine ⟨6777271967013760747596697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9036362622685014330128929 6777271967013760747596697)
              ·
                refine ⟨5082953975260320560697523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6777271967013760747596697 5082953975260320560697523)
                ·
                  refine ⟨7624430962890480841046285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082953975260320560697523 7624430962890480841046285)
                  ·
                    refine ⟨2859161611083930315392357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7624430962890480841046285 2859161611083930315392357)
                    ·
                      refine ⟨536092802078236934136067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2859161611083930315392357 536092802078236934136067)
                      ·
                        rfl

theorem cell23_1044037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_1044037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044037 prefixEnd_1044037 := by exact prefixLift 1044037
  have htrace : WordTrace (prefixWord ++ tailWord_1044037) baseStart_1044037 baseEnd_1044037 := by
    simpa [prefixWord, tailWord_1044037, baseEnd_1044037] using wordTrace_append hprefix tailTrace_1044037
  have hstable : (prefixWord ++ tailWord_1044037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044037).length < 2 ^ (prefixWord ++ tailWord_1044037).sum := by decide
  have hdescent : baseEnd_1044037 < baseStart_1044037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044067 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1044067 : Nat := 118140960795 + 1044067 * 2 ^ 59
def prefixEnd_1044067 : Nat := 4983230072969 + 3 ^ 40 * 1044067 * 2
def baseEnd_1044067 : Nat := 536108206497871816760929

theorem tailTrace_1044067 : CollatzResearch.WordTrace tailWord_1044067 prefixEnd_1044067 536108206497871816760929 := by
  unfold tailWord_1044067
  simp only [CollatzResearch.WordTrace]
  refine ⟨38080251908531046292530455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25386834605687364195020303 38080251908531046292530455)
  ·
    refine ⟨57120377862796569438795683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38080251908531046292530455 57120377862796569438795683)
    ·
      refine ⟨85680566794194854158193525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57120377862796569438795683 85680566794194854158193525)
      ·
        refine ⟨8032553136955767577330643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85680566794194854158193525 8032553136955767577330643)
        ·
          refine ⟨12048829705433651365995965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032553136955767577330643 12048829705433651365995965)
          ·
            refine ⟨4518311139537619262248487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12048829705433651365995965 4518311139537619262248487)
            ·
              refine ⟨6777466709306428893372731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518311139537619262248487 6777466709306428893372731)
              ·
                refine ⟨10166200063959643340059097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777466709306428893372731 10166200063959643340059097)
                ·
                  refine ⟨7624650047969732505044323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10166200063959643340059097 7624650047969732505044323)
                  ·
                    refine ⟨11436975071954598757566485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7624650047969732505044323 11436975071954598757566485)
                    ·
                      refine ⟨536108206497871816760929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11436975071954598757566485 536108206497871816760929)
                      ·
                        rfl

theorem cell23_1044067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1044067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044067 prefixEnd_1044067 := by exact prefixLift 1044067
  have htrace : WordTrace (prefixWord ++ tailWord_1044067) baseStart_1044067 baseEnd_1044067 := by
    simpa [prefixWord, tailWord_1044067, baseEnd_1044067] using wordTrace_append hprefix tailTrace_1044067
  have hstable : (prefixWord ++ tailWord_1044067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044067).length < 2 ^ (prefixWord ++ tailWord_1044067).sum := by decide
  have hdescent : baseEnd_1044067 < baseStart_1044067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044131 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 2, 3, 2]
def baseStart_1044131 : Nat := 118140960795 + 1044131 * 2 ^ 59
def prefixEnd_1044131 : Nat := 4983230072969 + 3 ^ 40 * 1044131 * 2
def baseEnd_1044131 : Nat := 536141069259759566360635

theorem tailTrace_1044131 : CollatzResearch.WordTrace tailWord_1044131 prefixEnd_1044131 536141069259759566360635 := by
  unfold tailWord_1044131
  simp only [CollatzResearch.WordTrace]
  refine ⟨38082586180299185222860247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25388390786866123481906831 38082586180299185222860247)
  ·
    refine ⟨57123879270448777834290371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38082586180299185222860247 57123879270448777834290371)
    ·
      refine ⟨85685818905673166751435557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57123879270448777834290371 85685818905673166751435557)
      ·
        refine ⟨16066091044813718765894167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85685818905673166751435557 16066091044813718765894167)
        ·
          refine ⟨24099136567220578148841251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066091044813718765894167 24099136567220578148841251)
          ·
            refine ⟨36148704850830867223261877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099136567220578148841251 36148704850830867223261877)
            ·
              refine ⟨3388941079765393802180801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36148704850830867223261877 3388941079765393802180801)
              ·
                refine ⟨2541705809824045351635601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388941079765393802180801 2541705809824045351635601)
                ·
                  refine ⟨1906279357368034013726701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2541705809824045351635601 1906279357368034013726701)
                  ·
                    refine ⟨714854759013012755147513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1906279357368034013726701 714854759013012755147513)
                    ·
                      refine ⟨536141069259759566360635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714854759013012755147513 536141069259759566360635)
                      ·
                        rfl

theorem cell23_1044131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_1044131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044131 prefixEnd_1044131 := by exact prefixLift 1044131
  have htrace : WordTrace (prefixWord ++ tailWord_1044131) baseStart_1044131 baseEnd_1044131 := by
    simpa [prefixWord, tailWord_1044131, baseEnd_1044131] using wordTrace_append hprefix tailTrace_1044131
  have hstable : (prefixWord ++ tailWord_1044131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044131).length < 2 ^ (prefixWord ++ tailWord_1044131).sum := by decide
  have hdescent : baseEnd_1044131 < baseStart_1044131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044158 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1044158 : Nat := 118140960795 + 1044158 * 2 ^ 59
def prefixEnd_1044158 : Nat := 4983230072969 + 3 ^ 40 * 1044158 * 2
def baseEnd_1044158 : Nat := 178718311079143653574337

theorem tailTrace_1044158 : CollatzResearch.WordTrace tailWord_1044158 prefixEnd_1044158 178718311079143653574337 := by
  unfold tailWord_1044158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760446368900171104261641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25389047300800912556062085 4760446368900171104261641)
  ·
    refine ⟨3570334776675128328196231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4760446368900171104261641 3570334776675128328196231)
    ·
      refine ⟨5355502165012692492294347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570334776675128328196231 5355502165012692492294347)
      ·
        refine ⟨8033253247519038738441521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355502165012692492294347 8033253247519038738441521)
        ·
          refine ⟨6024939935639279053831141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8033253247519038738441521 6024939935639279053831141)
          ·
            refine ⟨1129676237932364822593339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6024939935639279053831141 1129676237932364822593339)
            ·
              refine ⟨1694514356898547233890009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129676237932364822593339 1694514356898547233890009)
              ·
                refine ⟨1270885767673910425417507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694514356898547233890009 1270885767673910425417507)
                ·
                  refine ⟨1906328651510865638126261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1270885767673910425417507 1906328651510865638126261)
                  ·
                    refine ⟨178718311079143653574337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1906328651510865638126261 178718311079143653574337)
                    ·
                      rfl

theorem cell23_1044158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1044158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044158 prefixEnd_1044158 := by exact prefixLift 1044158
  have htrace : WordTrace (prefixWord ++ tailWord_1044158) baseStart_1044158 baseEnd_1044158 := by
    simpa [prefixWord, tailWord_1044158, baseEnd_1044158] using wordTrace_append hprefix tailTrace_1044158
  have hstable : (prefixWord ++ tailWord_1044158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044158).length < 2 ^ (prefixWord ++ tailWord_1044158).sum := by decide
  have hdescent : baseEnd_1044158 < baseStart_1044158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044167 : List Nat := [1, 1, 4, 1, 1, 1, 3, 11]
def baseStart_1044167 : Nat := 118140960795 + 1044167 * 2 ^ 59
def prefixEnd_1044167 : Nat := 4983230072969 + 3 ^ 40 * 1044167 * 2
def baseEnd_1044167 : Nat := 19857761280123015759647

theorem tailTrace_1044167 : CollatzResearch.WordTrace tailWord_1044167 prefixEnd_1044167 19857761280123015759647 := by
  unfold tailWord_1044167
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083899208168763371170755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25389266138779175580780503 38083899208168763371170755)
  ·
    refine ⟨57125848812253145056756133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38083899208168763371170755 57125848812253145056756133)
    ·
      refine ⟨10711096652297464698141775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57125848812253145056756133 10711096652297464698141775)
      ·
        refine ⟨16066644978446197047212663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711096652297464698141775 16066644978446197047212663)
        ·
          refine ⟨24099967467669295570818995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066644978446197047212663 24099967467669295570818995)
          ·
            refine ⟨36149951201503943356228493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099967467669295570818995 36149951201503943356228493)
            ·
              refine ⟨13556231700563978758585685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36149951201503943356228493 13556231700563978758585685)
              ·
                refine ⟨19857761280123015759647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13556231700563978758585685 19857761280123015759647)
                ·
                  rfl

theorem cell23_1044167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 11].length) (baseStart_1044167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044167 prefixEnd_1044167 := by exact prefixLift 1044167
  have htrace : WordTrace (prefixWord ++ tailWord_1044167) baseStart_1044167 baseEnd_1044167 := by
    simpa [prefixWord, tailWord_1044167, baseEnd_1044167] using wordTrace_append hprefix tailTrace_1044167
  have hstable : (prefixWord ++ tailWord_1044167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044167).length < 2 ^ (prefixWord ++ tailWord_1044167).sum := by decide
  have hdescent : baseEnd_1044167 < baseStart_1044167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044212 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1044212 : Nat := 118140960795 + 1044212 * 2 ^ 59
def prefixEnd_1044212 : Nat := 4983230072969 + 3 ^ 40 * 1044212 * 2
def baseEnd_1044212 : Nat := 536182661192773749447763

theorem tailTrace_1044212 : CollatzResearch.WordTrace tailWord_1044212 prefixEnd_1044212 536182661192773749447763 := by
  unfold tailWord_1044212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042770246502868028279445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25390360328670490704372593 19042770246502868028279445)
  ·
    refine ⟨892629855304821938825599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19042770246502868028279445 892629855304821938825599)
    ·
      refine ⟨1338944782957232908238399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892629855304821938825599 1338944782957232908238399)
      ·
        refine ⟨2008417174435849362357599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338944782957232908238399 2008417174435849362357599)
        ·
          refine ⟨3012625761653774043536399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008417174435849362357599 3012625761653774043536399)
          ·
            refine ⟨4518938642480661065304599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012625761653774043536399 4518938642480661065304599)
            ·
              refine ⟨6778407963720991597956899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518938642480661065304599 6778407963720991597956899)
              ·
                refine ⟨10167611945581487396935349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778407963720991597956899 10167611945581487396935349)
                ·
                  refine ⟨953213619898264443462689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10167611945581487396935349 953213619898264443462689)
                  ·
                    refine ⟨714910214923698332597017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953213619898264443462689 714910214923698332597017)
                    ·
                      refine ⟨536182661192773749447763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714910214923698332597017 536182661192773749447763)
                      ·
                        rfl

theorem cell23_1044212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1044212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044212 prefixEnd_1044212 := by exact prefixLift 1044212
  have htrace : WordTrace (prefixWord ++ tailWord_1044212) baseStart_1044212 baseEnd_1044212 := by
    simpa [prefixWord, tailWord_1044212, baseEnd_1044212] using wordTrace_append hprefix tailTrace_1044212
  have hstable : (prefixWord ++ tailWord_1044212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044212).length < 2 ^ (prefixWord ++ tailWord_1044212).sum := by decide
  have hdescent : baseEnd_1044212 < baseStart_1044212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044245 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1044245 : Nat := 118140960795 + 1044245 * 2 ^ 59
def prefixEnd_1044245 : Nat := 4983230072969 + 3 ^ 40 * 1044245 * 2
def baseEnd_1044245 : Nat := 536199606054372120335111

theorem tailTrace_1044245 : CollatzResearch.WordTrace tailWord_1044245 prefixEnd_1044245 536199606054372120335111 := by
  unfold tailWord_1044245
  simp only [CollatzResearch.WordTrace]
  refine ⟨38086744101886182692510189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25391162734590788461673459 38086744101886182692510189)
  ·
    refine ⟨14282529038207318509691321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38086744101886182692510189 14282529038207318509691321)
    ·
      refine ⟨10711896778655488882268491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14282529038207318509691321 10711896778655488882268491)
      ·
        refine ⟨16067845167983233323402737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711896778655488882268491 16067845167983233323402737)
        ·
          refine ⟨12050883875987424992552053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16067845167983233323402737 12050883875987424992552053)
          ·
            refine ⟨1129770363373821093051755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12050883875987424992552053 1129770363373821093051755)
            ·
              refine ⟨1694655545060731639577633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129770363373821093051755 1694655545060731639577633)
              ·
                refine ⟨1270991658795548729683225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694655545060731639577633 1270991658795548729683225)
                ·
                  refine ⟨953243744096661547262419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270991658795548729683225 953243744096661547262419)
                  ·
                    refine ⟨1429865616144992320893629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 953243744096661547262419 1429865616144992320893629)
                    ·
                      refine ⟨536199606054372120335111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1429865616144992320893629 536199606054372120335111)
                      ·
                        rfl

theorem cell23_1044245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1044245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044245 prefixEnd_1044245 := by exact prefixLift 1044245
  have htrace : WordTrace (prefixWord ++ tailWord_1044245) baseStart_1044245 baseEnd_1044245 := by
    simpa [prefixWord, tailWord_1044245, baseEnd_1044245] using wordTrace_append hprefix tailTrace_1044245
  have hstable : (prefixWord ++ tailWord_1044245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044245).length < 2 ^ (prefixWord ++ tailWord_1044245).sum := by decide
  have hdescent : baseEnd_1044245 < baseStart_1044245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044268 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_1044268 : Nat := 118140960795 + 1044268 * 2 ^ 59
def prefixEnd_1044268 : Nat := 4983230072969 + 3 ^ 40 * 1044268 * 2
def baseEnd_1044268 : Nat := 536211416109425530347505

theorem tailTrace_1044268 : CollatzResearch.WordTrace tailWord_1044268 prefixEnd_1044268 536211416109425530347505 := by
  unfold tailWord_1044268
  simp only [CollatzResearch.WordTrace]
  refine ⟨19043791490401428810298729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25391721987201905080398305 19043791490401428810298729)
  ·
    refine ⟨14282843617801071607724047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19043791490401428810298729 14282843617801071607724047)
    ·
      refine ⟨21424265426701607411586071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14282843617801071607724047 21424265426701607411586071)
      ·
        refine ⟨32136398140052411117379107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21424265426701607411586071 32136398140052411117379107)
        ·
          refine ⟨48204597210078616676068661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32136398140052411117379107 48204597210078616676068661)
          ·
            refine ⟨4519180988444870313381437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48204597210078616676068661 4519180988444870313381437)
            ·
              refine ⟨1694692870666826367518039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4519180988444870313381437 1694692870666826367518039)
              ·
                refine ⟨2542039306000239551277059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694692870666826367518039 2542039306000239551277059)
                ·
                  refine ⟨3813058959000359326915589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542039306000239551277059 3813058959000359326915589)
                  ·
                    refine ⟨714948554812567373796673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3813058959000359326915589 714948554812567373796673)
                    ·
                      refine ⟨536211416109425530347505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714948554812567373796673 536211416109425530347505)
                      ·
                        rfl

theorem cell23_1044268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_1044268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044268 prefixEnd_1044268 := by exact prefixLift 1044268
  have htrace : WordTrace (prefixWord ++ tailWord_1044268) baseStart_1044268 baseEnd_1044268 := by
    simpa [prefixWord, tailWord_1044268, baseEnd_1044268] using wordTrace_append hprefix tailTrace_1044268
  have hstable : (prefixWord ++ tailWord_1044268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044268).length < 2 ^ (prefixWord ++ tailWord_1044268).sum := by decide
  have hdescent : baseEnd_1044268 < baseStart_1044268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044285 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1044285 : Nat := 118140960795 + 1044285 * 2 ^ 59
def prefixEnd_1044285 : Nat := 4983230072969 + 3 ^ 40 * 1044285 * 2
def baseEnd_1044285 : Nat := 536220145280551963834927

theorem tailTrace_1044285 : CollatzResearch.WordTrace tailWord_1044285 prefixEnd_1044285 536220145280551963834927 := by
  unfold tailWord_1044285
  simp only [CollatzResearch.WordTrace]
  refine ⟨38088203021741269523966309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25392135347827513015977539 38088203021741269523966309)
  ·
    refine ⟨7141538066576488035743683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38088203021741269523966309 7141538066576488035743683)
    ·
      refine ⟨10712307099864732053615525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7141538066576488035743683 10712307099864732053615525)
      ·
        refine ⟨2008557581224637260052911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10712307099864732053615525 2008557581224637260052911)
        ·
          refine ⟨3012836371836955890079367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008557581224637260052911 3012836371836955890079367)
          ·
            refine ⟨4519254557755433835119051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012836371836955890079367 4519254557755433835119051)
            ·
              refine ⟨6778881836633150752678577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519254557755433835119051 6778881836633150752678577)
              ·
                refine ⟨5084161377474863064508933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778881836633150752678577 5084161377474863064508933)
                ·
                  refine ⟨953280258276536824595425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5084161377474863064508933 953280258276536824595425)
                  ·
                    refine ⟨714960193707402618446569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953280258276536824595425 714960193707402618446569)
                    ·
                      refine ⟨536220145280551963834927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 714960193707402618446569 536220145280551963834927)
                      ·
                        rfl

theorem cell23_1044285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1044285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044285 prefixEnd_1044285 := by exact prefixLift 1044285
  have htrace : WordTrace (prefixWord ++ tailWord_1044285) baseStart_1044285 baseEnd_1044285 := by
    simpa [prefixWord, tailWord_1044285, baseEnd_1044285] using wordTrace_append hprefix tailTrace_1044285
  have hstable : (prefixWord ++ tailWord_1044285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044285).length < 2 ^ (prefixWord ++ tailWord_1044285).sum := by decide
  have hdescent : baseEnd_1044285 < baseStart_1044285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044308 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1044308 : Nat := 118140960795 + 1044308 * 2 ^ 59
def prefixEnd_1044308 : Nat := 4983230072969 + 3 ^ 40 * 1044308 * 2
def baseEnd_1044308 : Nat := 59581328370622819316369

theorem tailTrace_1044308 : CollatzResearch.WordTrace tailWord_1044308 prefixEnd_1044308 59581328370622819316369 := by
  unfold tailWord_1044308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044520950328972226026789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25392694600438629634702385 19044520950328972226026789)
  ·
    refine ⟨3570847678186682292380023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19044520950328972226026789 3570847678186682292380023)
    ·
      refine ⟨5356271517280023438570035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570847678186682292380023 5356271517280023438570035)
      ·
        refine ⟨8034407275920035157855053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356271517280023438570035 8034407275920035157855053)
        ·
          refine ⟨3012902728470013184195645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8034407275920035157855053 3012902728470013184195645)
          ·
            refine ⟨1129838523176254944073367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3012902728470013184195645 1129838523176254944073367)
            ·
              refine ⟨1694757784764382416110051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129838523176254944073367 1694757784764382416110051)
              ·
                refine ⟨2542136677146573624165077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694757784764382416110051 2542136677146573624165077)
                ·
                  refine ⟨59581328370622819316369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2542136677146573624165077 59581328370622819316369)
                  ·
                    rfl

theorem cell23_1044308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1044308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044308 prefixEnd_1044308 := by exact prefixLift 1044308
  have htrace : WordTrace (prefixWord ++ tailWord_1044308) baseStart_1044308 baseEnd_1044308 := by
    simpa [prefixWord, tailWord_1044308, baseEnd_1044308] using wordTrace_append hprefix tailTrace_1044308
  have hstable : (prefixWord ++ tailWord_1044308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044308).length < 2 ^ (prefixWord ++ tailWord_1044308).sum := by decide
  have hdescent : baseEnd_1044308 < baseStart_1044308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044385 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1044385 : Nat := 118140960795 + 1044385 * 2 ^ 59
def prefixEnd_1044385 : Nat := 4983230072969 + 3 ^ 40 * 1044385 * 2
def baseEnd_1044385 : Nat := 178757164448667190861489

theorem tailTrace_1044385 : CollatzResearch.WordTrace tailWord_1044385 prefixEnd_1044385 178757164448667190861489 := by
  unfold tailWord_1044385
  simp only [CollatzResearch.WordTrace]
  refine ⟨38091850321378986602606609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25394566880919324401737739 38091850321378986602606609)
  ·
    refine ⟨28568887741034239951954957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38091850321378986602606609 28568887741034239951954957)
    ·
      refine ⟨10713332902887839981983109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28568887741034239951954957 10713332902887839981983109)
      ·
        refine ⟨2008749919291469996621833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10713332902887839981983109 2008749919291469996621833)
        ·
          refine ⟨1506562439468602497466375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008749919291469996621833 1506562439468602497466375)
          ·
            refine ⟨2259843659202903746199563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506562439468602497466375 2259843659202903746199563)
            ·
              refine ⟨3389765488804355619299345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259843659202903746199563 3389765488804355619299345)
              ·
                refine ⟨2542324116603266714474509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3389765488804355619299345 2542324116603266714474509)
                ·
                  refine ⟨953371543726225017927941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2542324116603266714474509 953371543726225017927941)
                  ·
                    refine ⟨178757164448667190861489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953371543726225017927941 178757164448667190861489)
                    ·
                      rfl

theorem cell23_1044385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1044385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044385 prefixEnd_1044385 := by exact prefixLift 1044385
  have htrace : WordTrace (prefixWord ++ tailWord_1044385) baseStart_1044385 baseEnd_1044385 := by
    simpa [prefixWord, tailWord_1044385, baseEnd_1044385] using wordTrace_append hprefix tailTrace_1044385
  have hstable : (prefixWord ++ tailWord_1044385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044385).length < 2 ^ (prefixWord ++ tailWord_1044385).sum := by decide
  have hdescent : baseEnd_1044385 < baseStart_1044385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044408 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_1044408 : Nat := 118140960795 + 1044408 * 2 ^ 59
def prefixEnd_1044408 : Nat := 4983230072969 + 3 ^ 40 * 1044408 * 2
def baseEnd_1044408 : Nat := 536283303401054982596861

theorem tailTrace_1044408 : CollatzResearch.WordTrace tailWord_1044408 prefixEnd_1044408 536283303401054982596861 := by
  unfold tailWord_1044408
  simp only [CollatzResearch.WordTrace]
  refine ⟨19046344600147830765346939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25395126133530441020462585 19046344600147830765346939)
  ·
    refine ⟨28569516900221746148020409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19046344600147830765346939 28569516900221746148020409)
    ·
      refine ⟨21427137675166309611015307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28569516900221746148020409 21427137675166309611015307)
      ·
        refine ⟨32140706512749464416522961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21427137675166309611015307 32140706512749464416522961)
        ·
          refine ⟨24105529884562098312392221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32140706512749464416522961 24105529884562098312392221)
          ·
            refine ⟨9039573706710786867147083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24105529884562098312392221 9039573706710786867147083)
            ·
              refine ⟨13559360560066180300720625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039573706710786867147083 13559360560066180300720625)
              ·
                refine ⟨10169520420049635225540469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13559360560066180300720625 10169520420049635225540469)
                ·
                  refine ⟨953392539379653302394419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10169520420049635225540469 953392539379653302394419)
                  ·
                    refine ⟨1430088809069479953591629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 953392539379653302394419 1430088809069479953591629)
                    ·
                      refine ⟨536283303401054982596861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1430088809069479953591629 536283303401054982596861)
                      ·
                        rfl

theorem cell23_1044408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_1044408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044408 prefixEnd_1044408 := by exact prefixLift 1044408
  have htrace : WordTrace (prefixWord ++ tailWord_1044408) baseStart_1044408 baseEnd_1044408 := by
    simpa [prefixWord, tailWord_1044408, baseEnd_1044408] using wordTrace_append hprefix tailTrace_1044408
  have hstable : (prefixWord ++ tailWord_1044408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044408).length < 2 ^ (prefixWord ++ tailWord_1044408).sum := by decide
  have hdescent : baseEnd_1044408 < baseStart_1044408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044458 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1044458 : Nat := 118140960795 + 1044458 * 2 ^ 59
def prefixEnd_1044458 : Nat := 4983230072969 + 3 ^ 40 * 1044458 * 2
def baseEnd_1044458 : Nat := 178769659144593262323877

theorem tailTrace_1044458 : CollatzResearch.WordTrace tailWord_1044458 prefixEnd_1044458 178769659144593262323877 := by
  unfold tailWord_1044458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523628212528630017503507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25396341900076346713342685 9523628212528630017503507)
  ·
    refine ⟨14285442318792945026255261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523628212528630017503507 14285442318792945026255261)
    ·
      refine ⟨5357040869547354384845723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14285442318792945026255261 5357040869547354384845723)
      ·
        refine ⟨8035561304321031577268585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357040869547354384845723 8035561304321031577268585)
        ·
          refine ⟨6026670978240773682951439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8035561304321031577268585 6026670978240773682951439)
          ·
            refine ⟨9040006467361160524427159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026670978240773682951439 9040006467361160524427159)
            ·
              refine ⟨13560009701041740786640739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040006467361160524427159 13560009701041740786640739)
              ·
                refine ⟨20340014551562611179961109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560009701041740786640739 20340014551562611179961109)
                ·
                  refine ⟨953438182104497399060677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20340014551562611179961109 953438182104497399060677)
                  ·
                    refine ⟨178769659144593262323877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953438182104497399060677 178769659144593262323877)
                    ·
                      rfl

theorem cell23_1044458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1044458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044458 prefixEnd_1044458 := by exact prefixLift 1044458
  have htrace : WordTrace (prefixWord ++ tailWord_1044458) baseStart_1044458 baseEnd_1044458 := by
    simpa [prefixWord, tailWord_1044458, baseEnd_1044458] using wordTrace_append hprefix tailTrace_1044458
  have hstable : (prefixWord ++ tailWord_1044458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044458).length < 2 ^ (prefixWord ++ tailWord_1044458).sum := by decide
  have hdescent : baseEnd_1044458 < baseStart_1044458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044491 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_1044491 : Nat := 118140960795 + 1044491 * 2 ^ 59
def prefixEnd_1044491 : Nat := 4983230072969 + 3 ^ 40 * 1044491 * 2
def baseEnd_1044491 : Nat := 536325922295378157858979

theorem tailTrace_1044491 : CollatzResearch.WordTrace tailWord_1044491 prefixEnd_1044491 536325922295378157858979 := by
  unfold tailWord_1044491
  simp only [CollatzResearch.WordTrace]
  refine ⟨38095716458994966705965327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25397144305996644470643551 38095716458994966705965327)
  ·
    refine ⟨57143574688492450058947991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38095716458994966705965327 57143574688492450058947991)
    ·
      refine ⟨85715362032738675088421987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57143574688492450058947991 85715362032738675088421987)
      ·
        refine ⟨128573043049108012632632981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85715362032738675088421987 128573043049108012632632981)
        ·
          refine ⟨6026861392926938092154671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128573043049108012632632981 6026861392926938092154671)
          ·
            refine ⟨9040292089390407138232007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026861392926938092154671 9040292089390407138232007)
            ·
              refine ⟨13560438134085610707348011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040292089390407138232007 13560438134085610707348011)
              ·
                refine ⟨20340657201128416061022017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560438134085610707348011 20340657201128416061022017)
                ·
                  refine ⟨15255492900846312045766513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20340657201128416061022017 15255492900846312045766513)
                  ·
                    refine ⟨11441619675634734034324885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15255492900846312045766513 11441619675634734034324885)
                    ·
                      refine ⟨536325922295378157858979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11441619675634734034324885 536325922295378157858979)
                      ·
                        rfl

theorem cell23_1044491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_1044491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044491 prefixEnd_1044491 := by exact prefixLift 1044491
  have htrace : WordTrace (prefixWord ++ tailWord_1044491) baseStart_1044491 baseEnd_1044491 := by
    simpa [prefixWord, tailWord_1044491, baseEnd_1044491] using wordTrace_append hprefix tailTrace_1044491
  have hstable : (prefixWord ++ tailWord_1044491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044491).length < 2 ^ (prefixWord ++ tailWord_1044491).sum := by decide
  have hdescent : baseEnd_1044491 < baseStart_1044491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044519 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1044519 : Nat := 118140960795 + 1044519 * 2 ^ 59
def prefixEnd_1044519 : Nat := 4983230072969 + 3 ^ 40 * 1044519 * 2
def baseEnd_1044519 : Nat := 536340299753704048308851

theorem tailTrace_1044519 : CollatzResearch.WordTrace tailWord_1044519 prefixEnd_1044519 536340299753704048308851 := by
  unfold tailWord_1044519
  simp only [CollatzResearch.WordTrace]
  refine ⟨38096737702893527487984611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25397825135262351658656407 38096737702893527487984611)
  ·
    refine ⟨57145106554340291231976917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38096737702893527487984611 57145106554340291231976917)
    ·
      refine ⟨1339338434867350575749459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57145106554340291231976917 1339338434867350575749459)
      ·
        refine ⟨2009007652301025863624189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339338434867350575749459 2009007652301025863624189)
        ·
          refine ⟨753377869612884698859071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2009007652301025863624189 753377869612884698859071)
          ·
            refine ⟨1130066804419327048288607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753377869612884698859071 1130066804419327048288607)
            ·
              refine ⟨1695100206628990572432911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130066804419327048288607 1695100206628990572432911)
              ·
                refine ⟨2542650309943485858649367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695100206628990572432911 2542650309943485858649367)
                ·
                  refine ⟨3813975464915228787974051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542650309943485858649367 3813975464915228787974051)
                  ·
                    refine ⟨5720963197372843181961077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3813975464915228787974051 5720963197372843181961077)
                    ·
                      refine ⟨536340299753704048308851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5720963197372843181961077 536340299753704048308851)
                      ·
                        rfl

theorem cell23_1044519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1044519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044519 prefixEnd_1044519 := by exact prefixLift 1044519
  have htrace : WordTrace (prefixWord ++ tailWord_1044519) baseStart_1044519 baseEnd_1044519 := by
    simpa [prefixWord, tailWord_1044519, baseEnd_1044519] using wordTrace_append hprefix tailTrace_1044519
  have hstable : (prefixWord ++ tailWord_1044519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044519).length < 2 ^ (prefixWord ++ tailWord_1044519).sum := by decide
  have hdescent : baseEnd_1044519 < baseStart_1044519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044572 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_1044572 : Nat := 118140960795 + 1044572 * 2 ^ 59
def prefixEnd_1044572 : Nat := 4983230072969 + 3 ^ 40 * 1044572 * 2
def baseEnd_1044572 : Nat := 536367514228392340946107

theorem tailTrace_1044572 : CollatzResearch.WordTrace tailWord_1044572 prefixEnd_1044572 536367514228392340946107 := by
  unfold tailWord_1044572
  simp only [CollatzResearch.WordTrace]
  refine ⟨19049335385850758769831985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25399113847801011693109313 19049335385850758769831985)
  ·
    refine ⟨14287001539388069077373989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19049335385850758769831985 14287001539388069077373989)
    ·
      refine ⟨2678812788635262952007623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14287001539388069077373989 2678812788635262952007623)
      ·
        refine ⟨4018219182952894428011435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678812788635262952007623 4018219182952894428011435)
        ·
          refine ⟨6027328774429341642017153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018219182952894428011435 6027328774429341642017153)
          ·
            refine ⟨4520496580822006231512865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027328774429341642017153 4520496580822006231512865)
            ·
              refine ⟨3390372435616504673634649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520496580822006231512865 3390372435616504673634649)
              ·
                refine ⟨2542779326712378505225987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390372435616504673634649 2542779326712378505225987)
                ·
                  refine ⟨3814168990068567757838981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2542779326712378505225987 3814168990068567757838981)
                  ·
                    refine ⟨715156685637856454594809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3814168990068567757838981 715156685637856454594809)
                    ·
                      refine ⟨536367514228392340946107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715156685637856454594809 536367514228392340946107)
                      ·
                        rfl

theorem cell23_1044572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_1044572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044572 prefixEnd_1044572 := by exact prefixLift 1044572
  have htrace : WordTrace (prefixWord ++ tailWord_1044572) baseStart_1044572 baseEnd_1044572 := by
    simpa [prefixWord, tailWord_1044572, baseEnd_1044572] using wordTrace_append hprefix tailTrace_1044572
  have hstable : (prefixWord ++ tailWord_1044572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044572).length < 2 ^ (prefixWord ++ tailWord_1044572).sum := by decide
  have hdescent : baseEnd_1044572 < baseStart_1044572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044605 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1044605 : Nat := 118140960795 + 1044605 * 2 ^ 59
def prefixEnd_1044605 : Nat := 4983230072969 + 3 ^ 40 * 1044605 * 2
def baseEnd_1044605 : Nat := 536384459089990711833455

theorem tailTrace_1044605 : CollatzResearch.WordTrace tailWord_1044605 prefixEnd_1044605 536384459089990711833455 := by
  unfold tailWord_1044605
  simp only [CollatzResearch.WordTrace]
  refine ⟨38099874380581964175615269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25399916253721309450410179 38099874380581964175615269)
  ·
    refine ⟨7143726446359118282927863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38099874380581964175615269 7143726446359118282927863)
    ·
      refine ⟨10715589669538677424391795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7143726446359118282927863 10715589669538677424391795)
      ·
        refine ⟨16073384504308016136587693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715589669538677424391795 16073384504308016136587693)
        ·
          refine ⟨6027519189115506051220385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16073384504308016136587693 6027519189115506051220385)
          ·
            refine ⟨4520639391836629538415289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6027519189115506051220385 4520639391836629538415289)
            ·
              refine ⟨3390479543877472153811467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520639391836629538415289 3390479543877472153811467)
              ·
                refine ⟨5085719315816208230717201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390479543877472153811467 5085719315816208230717201)
                ·
                  refine ⟨3814289486862156173037901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5085719315816208230717201 3814289486862156173037901)
                  ·
                    refine ⟨1430358557573308564889213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3814289486862156173037901 1430358557573308564889213)
                    ·
                      refine ⟨536384459089990711833455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1430358557573308564889213 536384459089990711833455)
                      ·
                        rfl

theorem cell23_1044605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1044605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044605 prefixEnd_1044605 := by exact prefixLift 1044605
  have htrace : WordTrace (prefixWord ++ tailWord_1044605) baseStart_1044605 baseEnd_1044605 := by
    simpa [prefixWord, tailWord_1044605, baseEnd_1044605] using wordTrace_append hprefix tailTrace_1044605
  have hstable : (prefixWord ++ tailWord_1044605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044605).length < 2 ^ (prefixWord ++ tailWord_1044605).sum := by decide
  have hdescent : baseEnd_1044605 < baseStart_1044605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044615 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_1044615 : Nat := 118140960795 + 1044615 * 2 ^ 59
def prefixEnd_1044615 : Nat := 4983230072969 + 3 ^ 40 * 1044615 * 2
def baseEnd_1044615 : Nat := 536389593896535672708409

theorem tailTrace_1044615 : CollatzResearch.WordTrace tailWord_1044615 prefixEnd_1044615 536389593896535672708409 := by
  unfold tailWord_1044615
  simp only [CollatzResearch.WordTrace]
  refine ⟨38100239110545735883479299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25400159407030490588986199 38100239110545735883479299)
  ·
    refine ⟨57150358665818603825218949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38100239110545735883479299 57150358665818603825218949)
    ·
      refine ⟨10715692249840988217228553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57150358665818603825218949 10715692249840988217228553)
      ·
        refine ⟨8036769187380741162921415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10715692249840988217228553 8036769187380741162921415)
        ·
          refine ⟨12055153781071111744382123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036769187380741162921415 12055153781071111744382123)
          ·
            refine ⟨18082730671606667616573185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055153781071111744382123 18082730671606667616573185)
            ·
              refine ⟨13562048003705000712429889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18082730671606667616573185 13562048003705000712429889)
              ·
                refine ⟨10171536002778750534322417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13562048003705000712429889 10171536002778750534322417)
                ·
                  refine ⟨7628652002084062900741813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171536002778750534322417 7628652002084062900741813)
                  ·
                    refine ⟨715186125195380896944545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7628652002084062900741813 715186125195380896944545)
                    ·
                      refine ⟨536389593896535672708409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715186125195380896944545 536389593896535672708409)
                      ·
                        rfl

theorem cell23_1044615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_1044615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044615 prefixEnd_1044615 := by exact prefixLift 1044615
  have htrace : WordTrace (prefixWord ++ tailWord_1044615) baseStart_1044615 baseEnd_1044615 := by
    simpa [prefixWord, tailWord_1044615, baseEnd_1044615] using wordTrace_append hprefix tailTrace_1044615
  have hstable : (prefixWord ++ tailWord_1044615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044615).length < 2 ^ (prefixWord ++ tailWord_1044615).sum := by decide
  have hdescent : baseEnd_1044615 < baseStart_1044615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044642 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1044642 : Nat := 118140960795 + 1044642 * 2 ^ 59
def prefixEnd_1044642 : Nat := 4983230072969 + 3 ^ 40 * 1044642 * 2
def baseEnd_1044642 : Nat := 178801152624735689023595

theorem tailTrace_1044642 : CollatzResearch.WordTrace tailWord_1044642 prefixEnd_1044642 178801152624735689023595 := by
  unfold tailWord_1044642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525305970361979873678045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25400815920965279663141453 9525305970361979873678045)
  ·
    refine ⟨3571989738885742452629267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9525305970361979873678045 3571989738885742452629267)
    ·
      refine ⟨5357984608328613678943901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3571989738885742452629267 5357984608328613678943901)
      ·
        refine ⟨2009244228123230129603963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5357984608328613678943901 2009244228123230129603963)
        ·
          refine ⟨3013866342184845194405945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009244228123230129603963 3013866342184845194405945)
          ·
            refine ⟨2260399756638633895804459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013866342184845194405945 2260399756638633895804459)
            ·
              refine ⟨3390599634957950843706689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260399756638633895804459 3390599634957950843706689)
              ·
                refine ⟨2542949726218463132780017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390599634957950843706689 2542949726218463132780017)
                ·
                  refine ⟨1907212294663847349585013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542949726218463132780017 1907212294663847349585013)
                  ·
                    refine ⟨178801152624735689023595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1907212294663847349585013 178801152624735689023595)
                    ·
                      rfl

theorem cell23_1044642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1044642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044642 prefixEnd_1044642 := by exact prefixLift 1044642
  have htrace : WordTrace (prefixWord ++ tailWord_1044642) baseStart_1044642 baseEnd_1044642 := by
    simpa [prefixWord, tailWord_1044642, baseEnd_1044642] using wordTrace_append hprefix tailTrace_1044642
  have hstable : (prefixWord ++ tailWord_1044642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044642).length < 2 ^ (prefixWord ++ tailWord_1044642).sum := by decide
  have hdescent : baseEnd_1044642 < baseStart_1044642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044645 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_1044645 : Nat := 118140960795 + 1044645 * 2 ^ 59
def prefixEnd_1044645 : Nat := 4983230072969 + 3 ^ 40 * 1044645 * 2
def baseEnd_1044645 : Nat := 536404998316170555333271

theorem tailTrace_1044645 : CollatzResearch.WordTrace tailWord_1044645 prefixEnd_1044645 536404998316170555333271 := by
  unfold tailWord_1044645
  simp only [CollatzResearch.WordTrace]
  refine ⟨38101333300437051007071389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25400888866958034004714259 38101333300437051007071389)
  ·
    refine ⟨14287999987663894127651771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38101333300437051007071389 14287999987663894127651771)
    ·
      refine ⟨21431999981495841191477657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14287999987663894127651771 21431999981495841191477657)
      ·
        refine ⟨16073999986121880893608243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21431999981495841191477657 16073999986121880893608243)
        ·
          refine ⟨24110999979182821340412365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16073999986121880893608243 24110999979182821340412365)
          ·
            refine ⟨9041624992193558002654637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24110999979182821340412365 9041624992193558002654637)
            ·
              refine ⟨3390609372072584250995489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9041624992193558002654637 3390609372072584250995489)
              ·
                refine ⟨2542957029054438188246617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390609372072584250995489 2542957029054438188246617)
                ·
                  refine ⟨1907217771790828641184963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2542957029054438188246617 1907217771790828641184963)
                  ·
                    refine ⟨2860826657686242961777445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1907217771790828641184963 2860826657686242961777445)
                    ·
                      refine ⟨536404998316170555333271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2860826657686242961777445 536404998316170555333271)
                      ·
                        rfl

theorem cell23_1044645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_1044645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044645 prefixEnd_1044645 := by exact prefixLift 1044645
  have htrace : WordTrace (prefixWord ++ tailWord_1044645) baseStart_1044645 baseEnd_1044645 := by
    simpa [prefixWord, tailWord_1044645, baseEnd_1044645] using wordTrace_append hprefix tailTrace_1044645
  have hstable : (prefixWord ++ tailWord_1044645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044645).length < 2 ^ (prefixWord ++ tailWord_1044645).sum := by decide
  have hdescent : baseEnd_1044645 < baseStart_1044645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044665 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1044665 : Nat := 118140960795 + 1044665 * 2 ^ 59
def prefixEnd_1044665 : Nat := 4983230072969 + 3 ^ 40 * 1044665 * 2
def baseEnd_1044665 : Nat := 536415267929260477083179

theorem tailTrace_1044665 : CollatzResearch.WordTrace tailWord_1044665 prefixEnd_1044665 536415267929260477083179 := by
  unfold tailWord_1044665
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102062760364594422799449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25401375173576396281866299 38102062760364594422799449)
  ·
    refine ⟨28576547070273445817099587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38102062760364594422799449 28576547070273445817099587)
    ·
      refine ⟨42864820605410168725649381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28576547070273445817099587 42864820605410168725649381)
      ·
        refine ⟨8037153863514406636059259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42864820605410168725649381 8037153863514406636059259)
        ·
          refine ⟨12055730795271609954088889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037153863514406636059259 12055730795271609954088889)
          ·
            refine ⟨9041798096453707465566667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055730795271609954088889 9041798096453707465566667)
            ·
              refine ⟨13562697144680561198350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041798096453707465566667 13562697144680561198350001)
              ·
                refine ⟨10172022858510420898762501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13562697144680561198350001 10172022858510420898762501)
                ·
                  refine ⟨1907254285970703918517969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10172022858510420898762501 1907254285970703918517969)
                  ·
                    refine ⟨1430440714478027938888477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907254285970703918517969 1430440714478027938888477)
                    ·
                      refine ⟨536415267929260477083179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1430440714478027938888477 536415267929260477083179)
                      ·
                        rfl

theorem cell23_1044665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1044665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044665 prefixEnd_1044665 := by exact prefixLift 1044665
  have htrace : WordTrace (prefixWord ++ tailWord_1044665) baseStart_1044665 baseEnd_1044665 := by
    simpa [prefixWord, tailWord_1044665, baseEnd_1044665] using wordTrace_append hprefix tailTrace_1044665
  have hstable : (prefixWord ++ tailWord_1044665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044665).length < 2 ^ (prefixWord ++ tailWord_1044665).sum := by decide
  have hdescent : baseEnd_1044665 < baseStart_1044665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044682 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1044682 : Nat := 118140960795 + 1044682 * 2 ^ 59
def prefixEnd_1044682 : Nat := 4983230072969 + 3 ^ 40 * 1044682 * 2
def baseEnd_1044682 : Nat := 536423997100386910570601

theorem tailTrace_1044682 : CollatzResearch.WordTrace tailWord_1044682 prefixEnd_1044682 536423997100386910570601 := by
  unfold tailWord_1044682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525670700325751581542075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25401788534202004217445533 9525670700325751581542075)
  ·
    refine ⟨14288506050488627372313113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9525670700325751581542075 14288506050488627372313113)
    ·
      refine ⟨10716379537866470529234835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14288506050488627372313113 10716379537866470529234835)
      ·
        refine ⟨16074569306799705793852253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716379537866470529234835 16074569306799705793852253)
        ·
          refine ⟨6027963490049889672694595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16074569306799705793852253 6027963490049889672694595)
          ·
            refine ⟨9041945235074834509041893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027963490049889672694595 9041945235074834509041893)
            ·
              refine ⟨1695364731576531470445355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9041945235074834509041893 1695364731576531470445355)
              ·
                refine ⟨2543047097364797205668033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695364731576531470445355 2543047097364797205668033)
                ·
                  refine ⟨1907285323023597904251025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2543047097364797205668033 1907285323023597904251025)
                  ·
                    refine ⟨1430463992267698428188269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907285323023597904251025 1430463992267698428188269)
                    ·
                      refine ⟨536423997100386910570601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1430463992267698428188269 536423997100386910570601)
                      ·
                        rfl

theorem cell23_1044682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1044682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044682 prefixEnd_1044682 := by exact prefixLift 1044682
  have htrace : WordTrace (prefixWord ++ tailWord_1044682) baseStart_1044682 baseEnd_1044682 := by
    simpa [prefixWord, tailWord_1044682, baseEnd_1044682] using wordTrace_append hprefix tailTrace_1044682
  have hstable : (prefixWord ++ tailWord_1044682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044682).length < 2 ^ (prefixWord ++ tailWord_1044682).sum := by decide
  have hdescent : baseEnd_1044682 < baseStart_1044682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044735 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1044735 : Nat := 118140960795 + 1044735 * 2 ^ 59
def prefixEnd_1044735 : Nat := 4983230072969 + 3 ^ 40 * 1044735 * 2
def baseEnd_1044735 : Nat := 536451211575075203207857

theorem tailTrace_1044735 : CollatzResearch.WordTrace tailWord_1044735 prefixEnd_1044735 536451211575075203207857 := by
  unfold tailWord_1044735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104615870110996377847659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25403077246740664251898439 38104615870110996377847659)
  ·
    refine ⟨57156923805166494566771489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38104615870110996377847659 57156923805166494566771489)
    ·
      refine ⟨42867692853874870925078617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57156923805166494566771489 42867692853874870925078617)
      ·
        refine ⟨32150769640406153193808963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42867692853874870925078617 32150769640406153193808963)
        ·
          refine ⟨48226154460609229790713445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32150769640406153193808963 48226154460609229790713445)
          ·
            refine ⟨9042403961364230585758771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48226154460609229790713445 9042403961364230585758771)
            ·
              refine ⟨13563605942046345878638157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042403961364230585758771 13563605942046345878638157)
              ·
                refine ⟨5086352228267379704489309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13563605942046345878638157 5086352228267379704489309)
                ·
                  refine ⟨1907382085600267389183491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5086352228267379704489309 1907382085600267389183491)
                  ·
                    refine ⟨2861073128400401083775237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1907382085600267389183491 2861073128400401083775237)
                    ·
                      refine ⟨536451211575075203207857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2861073128400401083775237 536451211575075203207857)
                      ·
                        rfl

theorem cell23_1044735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1044735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044735 prefixEnd_1044735 := by exact prefixLift 1044735
  have htrace : WordTrace (prefixWord ++ tailWord_1044735) baseStart_1044735 baseEnd_1044735 := by
    simpa [prefixWord, tailWord_1044735, baseEnd_1044735] using wordTrace_append hprefix tailTrace_1044735
  have hstable : (prefixWord ++ tailWord_1044735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044735).length < 2 ^ (prefixWord ++ tailWord_1044735).sum := by decide
  have hdescent : baseEnd_1044735 < baseStart_1044735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044745 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_1044745 : Nat := 118140960795 + 1044745 * 2 ^ 59
def prefixEnd_1044745 : Nat := 4983230072969 + 3 ^ 40 * 1044745 * 2
def baseEnd_1044745 : Nat := 178818782127206721360937

theorem tailTrace_1044745 : CollatzResearch.WordTrace tailWord_1044745 prefixEnd_1044745 178818782127206721360937 := by
  unfold tailWord_1044745
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104980600074768085711689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25403320400049845390474459 38104980600074768085711689)
  ·
    refine ⟨28578735450056076064283767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38104980600074768085711689 28578735450056076064283767)
    ·
      refine ⟨42868103175084114096425651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28578735450056076064283767 42868103175084114096425651)
      ·
        refine ⟨64302154762626171144638477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42868103175084114096425651 64302154762626171144638477)
        ·
          refine ⟨24113308035984814179239429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64302154762626171144638477 24113308035984814179239429)
          ·
            refine ⟨4521245256747152658607393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24113308035984814179239429 4521245256747152658607393)
            ·
              refine ⟨3390933942560364493955545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521245256747152658607393 3390933942560364493955545)
              ·
                refine ⟨2543200456920273370466659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390933942560364493955545 2543200456920273370466659)
                ·
                  refine ⟨3814800685380410055699989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543200456920273370466659 3814800685380410055699989)
                  ·
                    refine ⟨178818782127206721360937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3814800685380410055699989 178818782127206721360937)
                    ·
                      rfl

theorem cell23_1044745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_1044745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044745 prefixEnd_1044745 := by exact prefixLift 1044745
  have htrace : WordTrace (prefixWord ++ tailWord_1044745) baseStart_1044745 baseEnd_1044745 := by
    simpa [prefixWord, tailWord_1044745, baseEnd_1044745] using wordTrace_append hprefix tailTrace_1044745
  have hstable : (prefixWord ++ tailWord_1044745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044745).length < 2 ^ (prefixWord ++ tailWord_1044745).sum := by decide
  have hdescent : baseEnd_1044745 < baseStart_1044745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044769 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1044769 : Nat := 118140960795 + 1044769 * 2 ^ 59
def prefixEnd_1044769 : Nat := 4983230072969 + 3 ^ 40 * 1044769 * 2
def baseEnd_1044769 : Nat := 536468669917328070182701

theorem tailTrace_1044769 : CollatzResearch.WordTrace tailWord_1044769 prefixEnd_1044769 536468669917328070182701 := by
  unfold tailWord_1044769
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105855951987820184585361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25403903967991880123056907 38105855951987820184585361)
  ·
    refine ⟨28579391963990865138439021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38105855951987820184585361 28579391963990865138439021)
    ·
      refine ⟨10717271986496574426914633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28579391963990865138439021 10717271986496574426914633)
      ·
        refine ⟨8037953989872430820185975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10717271986496574426914633 8037953989872430820185975)
        ·
          refine ⟨12056930984808646230278963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037953989872430820185975 12056930984808646230278963)
          ·
            refine ⟨18085396477212969345418445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12056930984808646230278963 18085396477212969345418445)
            ·
              refine ⟨6782023678954863504531917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18085396477212969345418445 6782023678954863504531917)
              ·
                refine ⟨2543258879608073814199469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6782023678954863504531917 2543258879608073814199469)
                ·
                  refine ⟨953722079853027680324801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2543258879608073814199469 953722079853027680324801)
                  ·
                    refine ⟨715291559889770760243601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953722079853027680324801 715291559889770760243601)
                    ·
                      refine ⟨536468669917328070182701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715291559889770760243601 536468669917328070182701)
                      ·
                        rfl

theorem cell23_1044769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1044769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044769 prefixEnd_1044769 := by exact prefixLift 1044769
  have htrace : WordTrace (prefixWord ++ tailWord_1044769) baseStart_1044769 baseEnd_1044769 := by
    simpa [prefixWord, tailWord_1044769, baseEnd_1044769] using wordTrace_append hprefix tailTrace_1044769
  have hstable : (prefixWord ++ tailWord_1044769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044769).length < 2 ^ (prefixWord ++ tailWord_1044769).sum := by decide
  have hdescent : baseEnd_1044769 < baseStart_1044769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044772 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1044772 : Nat := 118140960795 + 1044772 * 2 ^ 59
def prefixEnd_1044772 : Nat := 4983230072969 + 3 ^ 40 * 1044772 * 2
def baseEnd_1044772 : Nat := 536470210359291558445187

theorem tailTrace_1044772 : CollatzResearch.WordTrace tailWord_1044772 prefixEnd_1044772 536470210359291558445187 := by
  unfold tailWord_1044772
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052982685488475848472285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25403976913984634464629713 19052982685488475848472285)
  ·
    refine ⟨7144868507058178443177107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19052982685488475848472285 7144868507058178443177107)
    ·
      refine ⟨10717302760587267664765661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144868507058178443177107 10717302760587267664765661)
      ·
        refine ⟨4018988535220225374287123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10717302760587267664765661 4018988535220225374287123)
        ·
          refine ⟨6028482802830338061430685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018988535220225374287123 6028482802830338061430685)
          ·
            refine ⟨2260681051061376773036507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6028482802830338061430685 2260681051061376773036507)
            ·
              refine ⟨3391021576592065159554761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260681051061376773036507 3391021576592065159554761)
              ·
                refine ⟨2543266182444048869666071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391021576592065159554761 2543266182444048869666071)
                ·
                  refine ⟨3814899273666073304499107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543266182444048869666071 3814899273666073304499107)
                  ·
                    refine ⟨5722348910499109956748661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3814899273666073304499107 5722348910499109956748661)
                    ·
                      refine ⟨536470210359291558445187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5722348910499109956748661 536470210359291558445187)
                      ·
                        rfl

theorem cell23_1044772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1044772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044772 prefixEnd_1044772 := by exact prefixLift 1044772
  have htrace : WordTrace (prefixWord ++ tailWord_1044772) baseStart_1044772 baseEnd_1044772 := by
    simpa [prefixWord, tailWord_1044772, baseEnd_1044772] using wordTrace_append hprefix tailTrace_1044772
  have hstable : (prefixWord ++ tailWord_1044772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044772).length < 2 ^ (prefixWord ++ tailWord_1044772).sum := by decide
  have hdescent : baseEnd_1044772 < baseStart_1044772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044789 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1044789 : Nat := 118140960795 + 1044789 * 2 ^ 59
def prefixEnd_1044789 : Nat := 4983230072969 + 3 ^ 40 * 1044789 * 2
def baseEnd_1044789 : Nat := 536478939530417991932609

theorem tailTrace_1044789 : CollatzResearch.WordTrace tailWord_1044789 prefixEnd_1044789 536478939530417991932609 := by
  unfold tailWord_1044789
  simp only [CollatzResearch.WordTrace]
  refine ⟨38106585411915363600313421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25404390274610242400208947 38106585411915363600313421)
  ·
    refine ⟨14289969529468261350117533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38106585411915363600313421 14289969529468261350117533)
    ·
      refine ⟨5358738573550598006294075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14289969529468261350117533 5358738573550598006294075)
      ·
        refine ⟨8038107860325897009441113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358738573550598006294075 8038107860325897009441113)
        ·
          refine ⟨6028580895244422757080835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8038107860325897009441113 6028580895244422757080835)
          ·
            refine ⟨9042871342866634135621253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028580895244422757080835 9042871342866634135621253)
            ·
              refine ⟨1695538376787493900428985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9042871342866634135621253 1695538376787493900428985)
              ·
                refine ⟨1271653782590620425321739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695538376787493900428985 1271653782590620425321739)
                ·
                  refine ⟨1907480673885930637982609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1271653782590620425321739 1907480673885930637982609)
                  ·
                    refine ⟨1430610505414447978486957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1907480673885930637982609 1430610505414447978486957)
                    ·
                      refine ⟨536478939530417991932609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1430610505414447978486957 536478939530417991932609)
                      ·
                        rfl

theorem cell23_1044789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1044789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044789 prefixEnd_1044789 := by exact prefixLift 1044789
  have htrace : WordTrace (prefixWord ++ tailWord_1044789) baseStart_1044789 baseEnd_1044789 := by
    simpa [prefixWord, tailWord_1044789, baseEnd_1044789] using wordTrace_append hprefix tailTrace_1044789
  have hstable : (prefixWord ++ tailWord_1044789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044789).length < 2 ^ (prefixWord ++ tailWord_1044789).sum := by decide
  have hdescent : baseEnd_1044789 < baseStart_1044789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044820 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_1044820 : Nat := 118140960795 + 1044820 * 2 ^ 59
def prefixEnd_1044820 : Nat := 4983230072969 + 3 ^ 40 * 1044820 * 2
def baseEnd_1044820 : Nat := 536494857430707370644967

theorem tailTrace_1044820 : CollatzResearch.WordTrace tailWord_1044820 prefixEnd_1044820 536494857430707370644967 := by
  unfold tailWord_1044820
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053858037401527947345957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25405144049868703929794609 19053858037401527947345957)
  ·
    refine ⟨3572598382012786490127367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19053858037401527947345957 3572598382012786490127367)
    ·
      refine ⟨5358897573019179735191051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572598382012786490127367 5358897573019179735191051)
      ·
        refine ⟨8038346359528769602786577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358897573019179735191051 8038346359528769602786577)
        ·
          refine ⟨6028759769646577202089933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8038346359528769602786577 6028759769646577202089933)
          ·
            refine ⟨2260784913617466450783725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6028759769646577202089933 2260784913617466450783725)
            ·
              refine ⟨847794342606549919043897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260784913617466450783725 847794342606549919043897)
              ·
                refine ⟨635845756954912439282923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847794342606549919043897 635845756954912439282923)
                ·
                  refine ⟨953768635432368658924385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635845756954912439282923 953768635432368658924385)
                  ·
                    refine ⟨715326476574276494193289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953768635432368658924385 715326476574276494193289)
                    ·
                      refine ⟨536494857430707370644967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715326476574276494193289 536494857430707370644967)
                      ·
                        rfl

theorem cell23_1044820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_1044820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044820 prefixEnd_1044820 := by exact prefixLift 1044820
  have htrace : WordTrace (prefixWord ++ tailWord_1044820) baseStart_1044820 baseEnd_1044820 := by
    simpa [prefixWord, tailWord_1044820, baseEnd_1044820] using wordTrace_append hprefix tailTrace_1044820
  have hstable : (prefixWord ++ tailWord_1044820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044820).length < 2 ^ (prefixWord ++ tailWord_1044820).sum := by decide
  have hdescent : baseEnd_1044820 < baseStart_1044820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044825 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_1044825 : Nat := 118140960795 + 1044825 * 2 ^ 59
def prefixEnd_1044825 : Nat := 4983230072969 + 3 ^ 40 * 1044825 * 2
def baseEnd_1044825 : Nat := 536497424833979851082443

theorem tailTrace_1044825 : CollatzResearch.WordTrace tailWord_1044825 prefixEnd_1044825 536497424833979851082443 := by
  unfold tailWord_1044825
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107898439784941748623929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25405265626523294499082619 38107898439784941748623929)
  ·
    refine ⟨28580923829838706311467947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38107898439784941748623929 28580923829838706311467947)
    ·
      refine ⟨42871385744758059467201921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28580923829838706311467947 42871385744758059467201921)
      ·
        refine ⟨32153539308568544600401441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42871385744758059467201921 32153539308568544600401441)
        ·
          refine ⟨24115154481426408450301081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32153539308568544600401441 24115154481426408450301081)
          ·
            refine ⟨18086365861069806337725811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24115154481426408450301081 18086365861069806337725811)
            ·
              refine ⟨27129548791604709506588717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18086365861069806337725811 27129548791604709506588717)
              ·
                refine ⟨10173580796851766064970769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27129548791604709506588717 10173580796851766064970769)
                ·
                  refine ⟨7630185597638824548728077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10173580796851766064970769 7630185597638824548728077)
                  ·
                    refine ⟨2861319599114559205773029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7630185597638824548728077 2861319599114559205773029)
                    ·
                      refine ⟨536497424833979851082443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2861319599114559205773029 536497424833979851082443)
                      ·
                        rfl

theorem cell23_1044825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_1044825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044825 prefixEnd_1044825 := by exact prefixLift 1044825
  have htrace : WordTrace (prefixWord ++ tailWord_1044825) baseStart_1044825 baseEnd_1044825 := by
    simpa [prefixWord, tailWord_1044825, baseEnd_1044825] using wordTrace_append hprefix tailTrace_1044825
  have hstable : (prefixWord ++ tailWord_1044825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044825).length < 2 ^ (prefixWord ++ tailWord_1044825).sum := by decide
  have hdescent : baseEnd_1044825 < baseStart_1044825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044835 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 8]
def baseStart_1044835 : Nat := 118140960795 + 1044835 * 2 ^ 59
def prefixEnd_1044835 : Nat := 4983230072969 + 3 ^ 40 * 1044835 * 2
def baseEnd_1044835 : Nat := 178834186546841603985799

theorem tailTrace_1044835 : CollatzResearch.WordTrace tailWord_1044835 prefixEnd_1044835 178834186546841603985799 := by
  unfold tailWord_1044835
  simp only [CollatzResearch.WordTrace]
  refine ⟨38108263169748713456487959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25405508779832475637658639 38108263169748713456487959)
  ·
    refine ⟨57162394754623070184731939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38108263169748713456487959 57162394754623070184731939)
    ·
      refine ⟨85743592131934605277097909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57162394754623070184731939 85743592131934605277097909)
      ·
        refine ⟨8038461762368869244727929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85743592131934605277097909 8038461762368869244727929)
        ·
          refine ⟨6028846321776651933545947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8038461762368869244727929 6028846321776651933545947)
          ·
            refine ⟨9043269482664977900318921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028846321776651933545947 9043269482664977900318921)
            ·
              refine ⟨6782452111998733425239191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043269482664977900318921 6782452111998733425239191)
              ·
                refine ⟨10173678167998100137858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782452111998733425239191 10173678167998100137858787)
                ·
                  refine ⟨15260517251997150206788181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173678167998100137858787 15260517251997150206788181)
                  ·
                    refine ⟨178834186546841603985799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15260517251997150206788181 178834186546841603985799)
                    ·
                      rfl

theorem cell23_1044835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_1044835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044835 prefixEnd_1044835 := by exact prefixLift 1044835
  have htrace : WordTrace (prefixWord ++ tailWord_1044835) baseStart_1044835 baseEnd_1044835 := by
    simpa [prefixWord, tailWord_1044835, baseEnd_1044835] using wordTrace_append hprefix tailTrace_1044835
  have hstable : (prefixWord ++ tailWord_1044835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044835).length < 2 ^ (prefixWord ++ tailWord_1044835).sum := by decide
  have hdescent : baseEnd_1044835 < baseStart_1044835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044855 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1044855 : Nat := 118140960795 + 1044855 * 2 ^ 59
def prefixEnd_1044855 : Nat := 4983230072969 + 3 ^ 40 * 1044855 * 2
def baseEnd_1044855 : Nat := 536512829253614733707305

theorem tailTrace_1044855 : CollatzResearch.WordTrace tailWord_1044855 prefixEnd_1044855 536512829253614733707305 := by
  unfold tailWord_1044855
  simp only [CollatzResearch.WordTrace]
  refine ⟨38108992629676256872216019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25405995086450837914810679 38108992629676256872216019)
  ·
    refine ⟨57163488944514385308324029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38108992629676256872216019 57163488944514385308324029)
    ·
      refine ⟨21436308354192894490621511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57163488944514385308324029 21436308354192894490621511)
      ·
        refine ⟨32154462531289341735932267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21436308354192894490621511 32154462531289341735932267)
        ·
          refine ⟨48231693796934012603898401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32154462531289341735932267 48231693796934012603898401)
          ·
            refine ⟨36173770347700509452923801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48231693796934012603898401 36173770347700509452923801)
            ·
              refine ⟨27130327760775382089692851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36173770347700509452923801 27130327760775382089692851)
              ·
                refine ⟨40695491641163073134539277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27130327760775382089692851 40695491641163073134539277)
                ·
                  refine ⟨15260809365436152425452229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40695491641163073134539277 15260809365436152425452229)
                  ·
                    refine ⟨2861401756019278579772293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15260809365436152425452229 2861401756019278579772293)
                    ·
                      refine ⟨536512829253614733707305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2861401756019278579772293 536512829253614733707305)
                      ·
                        rfl

theorem cell23_1044855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1044855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044855 prefixEnd_1044855 := by exact prefixLift 1044855
  have htrace : WordTrace (prefixWord ++ tailWord_1044855) baseStart_1044855 baseEnd_1044855 := by
    simpa [prefixWord, tailWord_1044855, baseEnd_1044855] using wordTrace_append hprefix tailTrace_1044855
  have hstable : (prefixWord ++ tailWord_1044855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044855).length < 2 ^ (prefixWord ++ tailWord_1044855).sum := by decide
  have hdescent : baseEnd_1044855 < baseStart_1044855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044859 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 1, 4, 2]
def baseStart_1044859 : Nat := 118140960795 + 1044859 * 2 ^ 59
def prefixEnd_1044859 : Nat := 4983230072969 + 3 ^ 40 * 1044859 * 2
def baseEnd_1044859 : Nat := 536514883176232718057287

theorem tailTrace_1044859 : CollatzResearch.WordTrace tailWord_1044859 prefixEnd_1044859 536514883176232718057287 := by
  unfold tailWord_1044859
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109138521661765555361631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25406092347774510370241087 38109138521661765555361631)
  ·
    refine ⟨57163707782492648333042447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38109138521661765555361631 57163707782492648333042447)
    ·
      refine ⟨85745561673738972499563671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57163707782492648333042447 85745561673738972499563671)
      ·
        refine ⟨128618342510608458749345507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85745561673738972499563671 128618342510608458749345507)
        ·
          refine ⟨192927513765912688124018261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128618342510608458749345507 192927513765912688124018261)
          ·
            refine ⟨2260869301944289313953339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 192927513765912688124018261 2260869301944289313953339)
            ·
              refine ⟨3391303952916433970930009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260869301944289313953339 3391303952916433970930009)
              ·
                refine ⟨2543477964687325478197507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391303952916433970930009 2543477964687325478197507)
                ·
                  refine ⟨3815216947030988217296261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2543477964687325478197507 3815216947030988217296261)
                  ·
                    refine ⟨715353177568310290743049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3815216947030988217296261 715353177568310290743049)
                    ·
                      refine ⟨536514883176232718057287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715353177568310290743049 536514883176232718057287)
                      ·
                        rfl

theorem cell23_1044859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4, 2].length) (baseStart_1044859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044859 prefixEnd_1044859 := by exact prefixLift 1044859
  have htrace : WordTrace (prefixWord ++ tailWord_1044859) baseStart_1044859 baseEnd_1044859 := by
    simpa [prefixWord, tailWord_1044859, baseEnd_1044859] using wordTrace_append hprefix tailTrace_1044859
  have hstable : (prefixWord ++ tailWord_1044859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044859).length < 2 ^ (prefixWord ++ tailWord_1044859).sum := by decide
  have hdescent : baseEnd_1044859 < baseStart_1044859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044872 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1044872 : Nat := 118140960795 + 1044872 * 2 ^ 59
def prefixEnd_1044872 : Nat := 4983230072969 + 3 ^ 40 * 1044872 * 2
def baseEnd_1044872 : Nat := 536521558424741167194727

theorem tailTrace_1044872 : CollatzResearch.WordTrace tailWord_1044872 prefixEnd_1044872 536521558424741167194727 := by
  unfold tailWord_1044872
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054806335307334387792435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25406408447076445850389913 19054806335307334387792435)
  ·
    refine ⟨28582209502961001581688653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19054806335307334387792435 28582209502961001581688653)
    ·
      refine ⟨10718328563610375593133245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28582209502961001581688653 10718328563610375593133245)
      ·
        refine ⟨4019373211353890847424967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10718328563610375593133245 4019373211353890847424967)
        ·
          refine ⟨6029059817030836271137451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019373211353890847424967 6029059817030836271137451)
          ·
            refine ⟨9043589725546254406706177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029059817030836271137451 9043589725546254406706177)
            ·
              refine ⟨6782692294159690805029633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043589725546254406706177 6782692294159690805029633)
              ·
                refine ⟨5087019220619768103772225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6782692294159690805029633 5087019220619768103772225)
                ·
                  refine ⟨3815264415464826077829169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5087019220619768103772225 3815264415464826077829169)
                  ·
                    refine ⟨2861448311598619558371877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3815264415464826077829169 2861448311598619558371877)
                    ·
                      refine ⟨536521558424741167194727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2861448311598619558371877 536521558424741167194727)
                      ·
                        rfl

theorem cell23_1044872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1044872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044872 prefixEnd_1044872 := by exact prefixLift 1044872
  have htrace : WordTrace (prefixWord ++ tailWord_1044872) baseStart_1044872 baseEnd_1044872 := by
    simpa [prefixWord, tailWord_1044872, baseEnd_1044872] using wordTrace_append hprefix tailTrace_1044872
  have hstable : (prefixWord ++ tailWord_1044872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044872).length < 2 ^ (prefixWord ++ tailWord_1044872).sum := by decide
  have hdescent : baseEnd_1044872 < baseStart_1044872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044876 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_1044876 : Nat := 118140960795 + 1044876 * 2 ^ 59
def prefixEnd_1044876 : Nat := 4983230072969 + 3 ^ 40 * 1044876 * 2
def baseEnd_1044876 : Nat := 536523612347359151544709

theorem tailTrace_1044876 : CollatzResearch.WordTrace tailWord_1044876 prefixEnd_1044876 536523612347359151544709 := by
  unfold tailWord_1044876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054879281300088729365241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25406505708400118305820321 19054879281300088729365241)
  ·
    refine ⟨14291159460975066547023931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19054879281300088729365241 14291159460975066547023931)
    ·
      refine ⟨21436739191462599820535897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14291159460975066547023931 21436739191462599820535897)
      ·
        refine ⟨16077554393596949865401923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21436739191462599820535897 16077554393596949865401923)
        ·
          refine ⟨24116331590395424798102885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16077554393596949865401923 24116331590395424798102885)
          ·
            refine ⟨4521812173199142149644291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24116331590395424798102885 4521812173199142149644291)
            ·
              refine ⟨6782718259798713224466437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521812173199142149644291 6782718259798713224466437)
              ·
                refine ⟨1271759673712258729587457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6782718259798713224466437 1271759673712258729587457)
                ·
                  refine ⟨953819755284194047190593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1271759673712258729587457 953819755284194047190593)
                  ·
                    refine ⟨715364816463145535392945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953819755284194047190593 715364816463145535392945)
                    ·
                      refine ⟨536523612347359151544709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715364816463145535392945 536523612347359151544709)
                      ·
                        rfl

theorem cell23_1044876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_1044876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044876 prefixEnd_1044876 := by exact prefixLift 1044876
  have htrace : WordTrace (prefixWord ++ tailWord_1044876) baseStart_1044876 baseEnd_1044876 := by
    simpa [prefixWord, tailWord_1044876, baseEnd_1044876] using wordTrace_append hprefix tailTrace_1044876
  have hstable : (prefixWord ++ tailWord_1044876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044876).length < 2 ^ (prefixWord ++ tailWord_1044876).sum := by decide
  have hdescent : baseEnd_1044876 < baseStart_1044876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044885 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1044885 : Nat := 118140960795 + 1044885 * 2 ^ 59
def prefixEnd_1044885 : Nat := 4983230072969 + 3 ^ 40 * 1044885 * 2
def baseEnd_1044885 : Nat := 536528233673249616332167

theorem tailTrace_1044885 : CollatzResearch.WordTrace tailWord_1044885 prefixEnd_1044885 536528233673249616332167 := by
  unfold tailWord_1044885
  simp only [CollatzResearch.WordTrace]
  refine ⟨38110086819567571995808109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25406724546378381330538739 38110086819567571995808109)
  ·
    refine ⟨14291282557337839498428041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38110086819567571995808109 14291282557337839498428041)
    ·
      refine ⟨10718461918003379623821031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14291282557337839498428041 10718461918003379623821031)
      ·
        refine ⟨16077692877005069435731547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10718461918003379623821031 16077692877005069435731547)
        ·
          refine ⟨24116539315507604153597321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16077692877005069435731547 24116539315507604153597321)
          ·
            refine ⟨18087404486630703115197991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24116539315507604153597321 18087404486630703115197991)
            ·
              refine ⟨27131106729946054672796987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18087404486630703115197991 27131106729946054672796987)
              ·
                refine ⟨40696660094919082009195481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27131106729946054672796987 40696660094919082009195481)
                ·
                  refine ⟨30522495071189311506896611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40696660094919082009195481 30522495071189311506896611)
                  ·
                    refine ⟨45783742606783967260344917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30522495071189311506896611 45783742606783967260344917)
                    ·
                      refine ⟨536528233673249616332167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45783742606783967260344917 536528233673249616332167)
                      ·
                        rfl

theorem cell23_1044885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1044885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044885 prefixEnd_1044885 := by exact prefixLift 1044885
  have htrace : WordTrace (prefixWord ++ tailWord_1044885) baseStart_1044885 baseEnd_1044885 := by
    simpa [prefixWord, tailWord_1044885, baseEnd_1044885] using wordTrace_append hprefix tailTrace_1044885
  have hstable : (prefixWord ++ tailWord_1044885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044885).length < 2 ^ (prefixWord ++ tailWord_1044885).sum := by decide
  have hdescent : baseEnd_1044885 < baseStart_1044885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044905 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_1044905 : Nat := 118140960795 + 1044905 * 2 ^ 59
def prefixEnd_1044905 : Nat := 4983230072969 + 3 ^ 40 * 1044905 * 2
def baseEnd_1044905 : Nat := 536538503286339538082075

theorem tailTrace_1044905 : CollatzResearch.WordTrace tailWord_1044905 prefixEnd_1044905 536538503286339538082075 := by
  unfold tailWord_1044905
  simp only [CollatzResearch.WordTrace]
  refine ⟨38110816279495115411536169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25407210852996743607690779 38110816279495115411536169)
  ·
    refine ⟨28583112209621336558652127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38110816279495115411536169 28583112209621336558652127)
    ·
      refine ⟨42874668314432004837978191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28583112209621336558652127 42874668314432004837978191)
      ·
        refine ⟨64312002471648007256967287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42874668314432004837978191 64312002471648007256967287)
        ·
          refine ⟨96468003707472010885450931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64312002471648007256967287 96468003707472010885450931)
          ·
            refine ⟨144702005561208016328176397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96468003707472010885450931 144702005561208016328176397)
            ·
              refine ⟨54263252085453006123066149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144702005561208016328176397 54263252085453006123066149)
              ·
                refine ⟨10174359766022438648074903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54263252085453006123066149 10174359766022438648074903)
                ·
                  refine ⟨15261539649033657972112355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10174359766022438648074903 15261539649033657972112355)
                  ·
                    refine ⟨22892309473550486958168533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15261539649033657972112355 22892309473550486958168533)
                    ·
                      refine ⟨536538503286339538082075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22892309473550486958168533 536538503286339538082075)
                      ·
                        rfl

theorem cell23_1044905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_1044905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044905 prefixEnd_1044905 := by exact prefixLift 1044905
  have htrace : WordTrace (prefixWord ++ tailWord_1044905) baseStart_1044905 baseEnd_1044905 := by
    simpa [prefixWord, tailWord_1044905, baseEnd_1044905] using wordTrace_append hprefix tailTrace_1044905
  have hstable : (prefixWord ++ tailWord_1044905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044905).length < 2 ^ (prefixWord ++ tailWord_1044905).sum := by decide
  have hdescent : baseEnd_1044905 < baseStart_1044905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044959 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 3, 4]
def baseStart_1044959 : Nat := 118140960795 + 1044959 * 2 ^ 59
def prefixEnd_1044959 : Nat := 4983230072969 + 3 ^ 40 * 1044959 * 2
def baseEnd_1044959 : Nat := 178855410413894108935609

theorem tailTrace_1044959 : CollatzResearch.WordTrace tailWord_1044959 prefixEnd_1044959 178855410413894108935609 := by
  unfold tailWord_1044959
  simp only [CollatzResearch.WordTrace]
  refine ⟨38112785821299482634001931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25408523880866321756001287 38112785821299482634001931)
  ·
    refine ⟨57169178731949223951002897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38112785821299482634001931 57169178731949223951002897)
    ·
      refine ⟨42876884048961917963252173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57169178731949223951002897 42876884048961917963252173)
      ·
        refine ⟨16078831518360719236219565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42876884048961917963252173 16078831518360719236219565)
        ·
          refine ⟨6029561819385269713582337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16078831518360719236219565 6029561819385269713582337)
          ·
            refine ⟨4522171364538952285186753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6029561819385269713582337 4522171364538952285186753)
            ·
              refine ⟨3391628523404214213890065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522171364538952285186753 3391628523404214213890065)
              ·
                refine ⟨2543721392553160660417549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391628523404214213890065 2543721392553160660417549)
                ·
                  refine ⟨953895522207435247656581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2543721392553160660417549 953895522207435247656581)
                  ·
                    refine ⟨178855410413894108935609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953895522207435247656581 178855410413894108935609)
                    ·
                      rfl

theorem cell23_1044959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_1044959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1044959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1044959 prefixEnd_1044959 := by exact prefixLift 1044959
  have htrace : WordTrace (prefixWord ++ tailWord_1044959) baseStart_1044959 baseEnd_1044959 := by
    simpa [prefixWord, tailWord_1044959, baseEnd_1044959] using wordTrace_append hprefix tailTrace_1044959
  have hstable : (prefixWord ++ tailWord_1044959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044959).length < 2 ^ (prefixWord ++ tailWord_1044959).sum := by decide
  have hdescent : baseEnd_1044959 < baseStart_1044959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045006 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_1045006 : Nat := 118140960795 + 1045006 * 2 ^ 59
def prefixEnd_1045006 : Nat := 4983230072969 + 3 ^ 40 * 1045006 * 2
def baseEnd_1045006 : Nat := 59621151648049293657679

theorem tailTrace_1045006 : CollatzResearch.WordTrace tailWord_1045006 prefixEnd_1045006 59621151648049293657679 := by
  unfold tailWord_1045006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764312506516151207620359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25409666701419473107308581 4764312506516151207620359)
  ·
    refine ⟨7146468759774226811430539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4764312506516151207620359 7146468759774226811430539)
    ·
      refine ⟨10719703139661340217145809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146468759774226811430539 10719703139661340217145809)
      ·
        refine ⟨8039777354746005162859357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10719703139661340217145809 8039777354746005162859357)
        ·
          refine ⟨3014916508029751936072259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8039777354746005162859357 3014916508029751936072259)
          ·
            refine ⟨4522374762044627904108389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014916508029751936072259 4522374762044627904108389)
            ·
              refine ⟨847945267883367732020323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4522374762044627904108389 847945267883367732020323)
              ·
                refine ⟨1271917901825051598030485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847945267883367732020323 1271917901825051598030485)
                ·
                  refine ⟨59621151648049293657679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1271917901825051598030485 59621151648049293657679)
                  ·
                    rfl

theorem cell23_1045006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_1045006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045006 prefixEnd_1045006 := by exact prefixLift 1045006
  have htrace : WordTrace (prefixWord ++ tailWord_1045006) baseStart_1045006 baseEnd_1045006 := by
    simpa [prefixWord, tailWord_1045006, baseEnd_1045006] using wordTrace_append hprefix tailTrace_1045006
  have hstable : (prefixWord ++ tailWord_1045006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045006).length < 2 ^ (prefixWord ++ tailWord_1045006).sum := by decide
  have hdescent : baseEnd_1045006 < baseStart_1045006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045009 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_1045009 : Nat := 118140960795 + 1045009 * 2 ^ 59
def prefixEnd_1045009 : Nat := 4983230072969 + 3 ^ 40 * 1045009 * 2
def baseEnd_1045009 : Nat := 536591905274407131181597

theorem tailTrace_1045009 : CollatzResearch.WordTrace tailWord_1045009 prefixEnd_1045009 536591905274407131181597 := by
  unfold tailWord_1045009
  simp only [CollatzResearch.WordTrace]
  refine ⟨38114609471118341173322081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25409739647412227448881387 38114609471118341173322081)
  ·
    refine ⟨28585957103338755879991561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38114609471118341173322081 28585957103338755879991561)
    ·
      refine ⟨21439467827504066909993671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28585957103338755879991561 21439467827504066909993671)
      ·
        refine ⟨32159201741256100364990507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21439467827504066909993671 32159201741256100364990507)
        ·
          refine ⟨48238802611884150547485761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32159201741256100364990507 48238802611884150547485761)
          ·
            refine ⟨36179101958913112910614321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48238802611884150547485761 36179101958913112910614321)
            ·
              refine ⟨27134326469184834682960741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36179101958913112910614321 27134326469184834682960741)
              ·
                refine ⟨5087686212972156503055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27134326469184834682960741 5087686212972156503055139)
                ·
                  refine ⟨7631529319458234754582709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5087686212972156503055139 7631529319458234754582709)
                  ·
                    refine ⟨715455873699209508242129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7631529319458234754582709 715455873699209508242129)
                    ·
                      refine ⟨536591905274407131181597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715455873699209508242129 536591905274407131181597)
                      ·
                        rfl

theorem cell23_1045009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_1045009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045009 prefixEnd_1045009 := by exact prefixLift 1045009
  have htrace : WordTrace (prefixWord ++ tailWord_1045009) baseStart_1045009 baseEnd_1045009 := by
    simpa [prefixWord, tailWord_1045009, baseEnd_1045009] using wordTrace_append hprefix tailTrace_1045009
  have hstable : (prefixWord ++ tailWord_1045009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045009).length < 2 ^ (prefixWord ++ tailWord_1045009).sum := by decide
  have hdescent : baseEnd_1045009 < baseStart_1045009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045044 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1045044 : Nat := 118140960795 + 1045044 * 2 ^ 59
def prefixEnd_1045044 : Nat := 4983230072969 + 3 ^ 40 * 1045044 * 2
def baseEnd_1045044 : Nat := 178869959032438164747979

theorem tailTrace_1045044 : CollatzResearch.WordTrace tailWord_1045044 prefixEnd_1045044 178869959032438164747979 := by
  unfold tailWord_1045044
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057943012995771075423093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25410590683994361433897457 19057943012995771075423093)
  ·
    refine ⟨1786682157468353538320915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19057943012995771075423093 1786682157468353538320915)
    ·
      refine ⟨2680023236202530307481373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786682157468353538320915 2680023236202530307481373)
      ·
        refine ⟨1005008713575948865305515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2680023236202530307481373 1005008713575948865305515)
        ·
          refine ⟨1507513070363923297958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005008713575948865305515 1507513070363923297958273)
          ·
            refine ⟨1130634802772942473468705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507513070363923297958273 1130634802772942473468705)
            ·
              refine ⟨847976102079706855101529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130634802772942473468705 847976102079706855101529)
              ·
                refine ⟨635982076559780141326147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847976102079706855101529 635982076559780141326147)
                ·
                  refine ⟨953973114839670211989221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635982076559780141326147 953973114839670211989221)
                  ·
                    refine ⟨178869959032438164747979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953973114839670211989221 178869959032438164747979)
                    ·
                      rfl

theorem cell23_1045044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1045044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045044 prefixEnd_1045044 := by exact prefixLift 1045044
  have htrace : WordTrace (prefixWord ++ tailWord_1045044) baseStart_1045044 baseEnd_1045044 := by
    simpa [prefixWord, tailWord_1045044, baseEnd_1045044] using wordTrace_append hprefix tailTrace_1045044
  have hstable : (prefixWord ++ tailWord_1045044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045044).length < 2 ^ (prefixWord ++ tailWord_1045044).sum := by decide
  have hdescent : baseEnd_1045044 < baseStart_1045044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045050 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3]
def baseStart_1045050 : Nat := 118140960795 + 1045050 * 2 ^ 59
def prefixEnd_1045050 : Nat := 4983230072969 + 3 ^ 40 * 1045050 * 2
def baseEnd_1045050 : Nat := 536612957981241470768909

theorem tailTrace_1045050 : CollatzResearch.WordTrace tailWord_1045050 prefixEnd_1045050 536612957981241470768909 := by
  unfold tailWord_1045050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529026215992451293891151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25410736575979870117043069 9529026215992451293891151)
  ·
    refine ⟨14293539323988676940836727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9529026215992451293891151 14293539323988676940836727)
    ·
      refine ⟨21440308985983015411255091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14293539323988676940836727 21440308985983015411255091)
      ·
        refine ⟨32160463478974523116882637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21440308985983015411255091 32160463478974523116882637)
        ·
          refine ⟨12060173804615446168830989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32160463478974523116882637 12060173804615446168830989)
          ·
            refine ⟨4522565176730792313311621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12060173804615446168830989 4522565176730792313311621)
            ·
              refine ⟨847980970637023558745929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4522565176730792313311621 847980970637023558745929)
              ·
                refine ⟨635985727977767669059447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847980970637023558745929 635985727977767669059447)
                ·
                  refine ⟨953978591966651503589171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635985727977767669059447 953978591966651503589171)
                  ·
                    refine ⟨1430967887949977255383757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 953978591966651503589171 1430967887949977255383757)
                    ·
                      refine ⟨536612957981241470768909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1430967887949977255383757 536612957981241470768909)
                      ·
                        rfl

theorem cell23_1045050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_1045050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045050 prefixEnd_1045050 := by exact prefixLift 1045050
  have htrace : WordTrace (prefixWord ++ tailWord_1045050) baseStart_1045050 baseEnd_1045050 := by
    simpa [prefixWord, tailWord_1045050, baseEnd_1045050] using wordTrace_append hprefix tailTrace_1045050
  have hstable : (prefixWord ++ tailWord_1045050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045050).length < 2 ^ (prefixWord ++ tailWord_1045050).sum := by decide
  have hdescent : baseEnd_1045050 < baseStart_1045050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045066 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_1045066 : Nat := 118140960795 + 1045066 * 2 ^ 59
def prefixEnd_1045066 : Nat := 4983230072969 + 3 ^ 40 * 1045066 * 2
def baseEnd_1045066 : Nat := 178873724557237802722945

theorem tailTrace_1045066 : CollatzResearch.WordTrace tailWord_1045066 prefixEnd_1045066 178873724557237802722945 := by
  unfold tailWord_1045066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529172107977959977036763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25411125621274559938764701 9529172107977959977036763)
  ·
    refine ⟨14293758161966939965555145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9529172107977959977036763 14293758161966939965555145)
    ·
      refine ⟨10720318621475204974166359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14293758161966939965555145 10720318621475204974166359)
      ·
        refine ⟨16080477932212807461249539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720318621475204974166359 16080477932212807461249539)
        ·
          refine ⟨24120716898319211191874309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080477932212807461249539 24120716898319211191874309)
          ·
            refine ⟨4522634418434852098476433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24120716898319211191874309 4522634418434852098476433)
            ·
              refine ⟨3391975813826139073857325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522634418434852098476433 3391975813826139073857325)
              ·
                refine ⟨1271990930184802152696497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3391975813826139073857325 1271990930184802152696497)
                ·
                  refine ⟨953993197638601614522373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1271990930184802152696497 953993197638601614522373)
                  ·
                    refine ⟨178873724557237802722945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 953993197638601614522373 178873724557237802722945)
                    ·
                      rfl

theorem cell23_1045066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_1045066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045066 prefixEnd_1045066 := by exact prefixLift 1045066
  have htrace : WordTrace (prefixWord ++ tailWord_1045066) baseStart_1045066 baseEnd_1045066 := by
    simpa [prefixWord, tailWord_1045066, baseEnd_1045066] using wordTrace_append hprefix tailTrace_1045066
  have hstable : (prefixWord ++ tailWord_1045066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045066).length < 2 ^ (prefixWord ++ tailWord_1045066).sum := by decide
  have hdescent : baseEnd_1045066 < baseStart_1045066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045073 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_1045073 : Nat := 118140960795 + 1045073 * 2 ^ 59
def prefixEnd_1045073 : Nat := 4983230072969 + 3 ^ 40 * 1045073 * 2
def baseEnd_1045073 : Nat := 536624768036294880781303

theorem tailTrace_1045073 : CollatzResearch.WordTrace tailWord_1045073 prefixEnd_1045073 536624768036294880781303 := by
  unfold tailWord_1045073
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116943742886480103651873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411295828590986735767915 38116943742886480103651873)
  ·
    refine ⟨28587707807164860077738905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38116943742886480103651873 28587707807164860077738905)
    ·
      refine ⟨21440780855373645058304179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28587707807164860077738905 21440780855373645058304179)
      ·
        refine ⟨32161171283060467587456269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21440780855373645058304179 32161171283060467587456269)
        ·
          refine ⟨12060439231147675345296101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32161171283060467587456269 12060439231147675345296101)
          ·
            refine ⟨2261332355840189127243019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12060439231147675345296101 2261332355840189127243019)
            ·
              refine ⟨3391998533760283690864529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261332355840189127243019 3391998533760283690864529)
              ·
                refine ⟨2543998900320212768148397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391998533760283690864529 2543998900320212768148397)
                ·
                  refine ⟨953999587620079788055649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2543998900320212768148397 953999587620079788055649)
                  ·
                    refine ⟨715499690715059841041737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 953999587620079788055649 715499690715059841041737)
                    ·
                      refine ⟨536624768036294880781303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715499690715059841041737 536624768036294880781303)
                      ·
                        rfl

theorem cell23_1045073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_1045073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045073 prefixEnd_1045073 := by exact prefixLift 1045073
  have htrace : WordTrace (prefixWord ++ tailWord_1045073) baseStart_1045073 baseEnd_1045073 := by
    simpa [prefixWord, tailWord_1045073, baseEnd_1045073] using wordTrace_append hprefix tailTrace_1045073
  have hstable : (prefixWord ++ tailWord_1045073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045073).length < 2 ^ (prefixWord ++ tailWord_1045073).sum := by decide
  have hdescent : baseEnd_1045073 < baseStart_1045073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045076 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1045076 : Nat := 118140960795 + 1045076 * 2 ^ 59
def prefixEnd_1045076 : Nat := 4983230072969 + 3 ^ 40 * 1045076 * 2
def baseEnd_1045076 : Nat := 536626308478258369043789

theorem tailTrace_1045076 : CollatzResearch.WordTrace tailWord_1045076 prefixEnd_1045076 536626308478258369043789 := by
  unfold tailWord_1045076
  simp only [CollatzResearch.WordTrace]
  refine ⟨19058526580937805808005541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25411368774583741077340721 19058526580937805808005541)
  ·
    refine ⟨3573473733925838589001039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19058526580937805808005541 3573473733925838589001039)
    ·
      refine ⟨5360210600888757883501559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573473733925838589001039 5360210600888757883501559)
      ·
        refine ⟨8040315901333136825252339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360210600888757883501559 8040315901333136825252339)
        ·
          refine ⟨12060473851999705237878509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040315901333136825252339 12060473851999705237878509)
          ·
            refine ⟨4522677694499889464204441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12060473851999705237878509 4522677694499889464204441)
            ·
              refine ⟨3392008270874917098153331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522677694499889464204441 3392008270874917098153331)
              ·
                refine ⟨5088012406312375647229997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392008270874917098153331 5088012406312375647229997)
                ·
                  refine ⟨1908004652367140867711249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5088012406312375647229997 1908004652367140867711249)
                  ·
                    refine ⟨1431003489275355650783437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1908004652367140867711249 1431003489275355650783437)
                    ·
                      refine ⟨536626308478258369043789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431003489275355650783437 536626308478258369043789)
                      ·
                        rfl

theorem cell23_1045076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1045076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045076 prefixEnd_1045076 := by exact prefixLift 1045076
  have htrace : WordTrace (prefixWord ++ tailWord_1045076) baseStart_1045076 baseEnd_1045076 := by
    simpa [prefixWord, tailWord_1045076, baseEnd_1045076] using wordTrace_append hprefix tailTrace_1045076
  have hstable : (prefixWord ++ tailWord_1045076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045076).length < 2 ^ (prefixWord ++ tailWord_1045076).sum := by decide
  have hdescent : baseEnd_1045076 < baseStart_1045076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045079 : List Nat := [1, 1, 3, 2, 2, 2, 5, 7]
def baseStart_1045079 : Nat := 118140960795 + 1045079 * 2 ^ 59
def prefixEnd_1045079 : Nat := 4983230072969 + 3 ^ 40 * 1045079 * 2
def baseEnd_1045079 : Nat := 19875105515563772492825

theorem tailTrace_1045079 : CollatzResearch.WordTrace tailWord_1045079 prefixEnd_1045079 19875105515563772492825 := by
  unfold tailWord_1045079
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117162580864743128370291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411441720576495418913527 38117162580864743128370291)
  ·
    refine ⟨57175743871297114692555437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38117162580864743128370291 57175743871297114692555437)
    ·
      refine ⟨21440903951736418009708289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57175743871297114692555437 21440903951736418009708289)
      ·
        refine ⟨16080677963802313507281217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21440903951736418009708289 16080677963802313507281217)
        ·
          refine ⟨12060508472851735130460913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16080677963802313507281217 12060508472851735130460913)
          ·
            refine ⟨9045381354638801347845685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12060508472851735130460913 9045381354638801347845685)
            ·
              refine ⟨848004501997387626360533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9045381354638801347845685 848004501997387626360533)
              ·
                refine ⟨19875105515563772492825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 848004501997387626360533 19875105515563772492825)
                ·
                  rfl

theorem cell23_1045079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 7].length) (baseStart_1045079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045079 prefixEnd_1045079 := by exact prefixLift 1045079
  have htrace : WordTrace (prefixWord ++ tailWord_1045079) baseStart_1045079 baseEnd_1045079 := by
    simpa [prefixWord, tailWord_1045079, baseEnd_1045079] using wordTrace_append hprefix tailTrace_1045079
  have hstable : (prefixWord ++ tailWord_1045079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045079).length < 2 ^ (prefixWord ++ tailWord_1045079).sum := by decide
  have hdescent : baseEnd_1045079 < baseStart_1045079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045090 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1045090 : Nat := 118140960795 + 1045090 * 2 ^ 59
def prefixEnd_1045090 : Nat := 4983230072969 + 3 ^ 40 * 1045090 * 2
def baseEnd_1045090 : Nat := 536633497207421314268725

theorem tailTrace_1045090 : CollatzResearch.WordTrace tailWord_1045090 prefixEnd_1045090 536633497207421314268725 := by
  unfold tailWord_1045090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529390945956223001755181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25411709189216594671347149 9529390945956223001755181)
  ·
    refine ⟨3573521604733583625658193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9529390945956223001755181 3573521604733583625658193)
    ·
      refine ⟨2680141203550187719243645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3573521604733583625658193 2680141203550187719243645)
      ·
        refine ⟨1005052951331320394716367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2680141203550187719243645 1005052951331320394716367)
        ·
          refine ⟨1507579426996980592074551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005052951331320394716367 1507579426996980592074551)
          ·
            refine ⟨2261369140495470888111827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507579426996980592074551 2261369140495470888111827)
            ·
              refine ⟨3392053710743206332167741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261369140495470888111827 3392053710743206332167741)
              ·
                refine ⟨1272020141528702374562903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3392053710743206332167741 1272020141528702374562903)
                ·
                  refine ⟨1908030212293053561844355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272020141528702374562903 1908030212293053561844355)
                  ·
                    refine ⟨2862045318439580342766533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908030212293053561844355 2862045318439580342766533)
                    ·
                      refine ⟨536633497207421314268725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2862045318439580342766533 536633497207421314268725)
                      ·
                        rfl

theorem cell23_1045090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1045090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045090 prefixEnd_1045090 := by exact prefixLift 1045090
  have htrace : WordTrace (prefixWord ++ tailWord_1045090) baseStart_1045090 baseEnd_1045090 := by
    simpa [prefixWord, tailWord_1045090, baseEnd_1045090] using wordTrace_append hprefix tailTrace_1045090
  have hstable : (prefixWord ++ tailWord_1045090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045090).length < 2 ^ (prefixWord ++ tailWord_1045090).sum := by decide
  have hdescent : baseEnd_1045090 < baseStart_1045090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045093 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1045093 : Nat := 118140960795 + 1045093 * 2 ^ 59
def prefixEnd_1045093 : Nat := 4983230072969 + 3 ^ 40 * 1045093 * 2
def baseEnd_1045093 : Nat := 536635037649384802531211

theorem tailTrace_1045093 : CollatzResearch.WordTrace tailWord_1045093 prefixEnd_1045093 536635037649384802531211 := by
  unfold tailWord_1045093
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117673202814023519379933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411782135209349012919955 38117673202814023519379933)
  ·
    refine ⟨14294127451055258819767475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38117673202814023519379933 14294127451055258819767475)
    ·
      refine ⟨21441191176582888229651213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14294127451055258819767475 21441191176582888229651213)
      ·
        refine ⟨8040446691218583086119205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21441191176582888229651213 8040446691218583086119205)
        ·
          refine ⟨1507583754603484328647351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8040446691218583086119205 1507583754603484328647351)
          ·
            refine ⟨2261375631905226492971027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507583754603484328647351 2261375631905226492971027)
            ·
              refine ⟨3392063447857839739456541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261375631905226492971027 3392063447857839739456541)
              ·
                refine ⟨1272023792946689902296203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3392063447857839739456541 1272023792946689902296203)
                ·
                  refine ⟨1908035689420034853444305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272023792946689902296203 1908035689420034853444305)
                  ·
                    refine ⟨1431026767065026140083229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1908035689420034853444305 1431026767065026140083229)
                    ·
                      refine ⟨536635037649384802531211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431026767065026140083229 536635037649384802531211)
                      ·
                        rfl

theorem cell23_1045093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1045093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045093 prefixEnd_1045093 := by exact prefixLift 1045093
  have htrace : WordTrace (prefixWord ++ tailWord_1045093) baseStart_1045093 baseEnd_1045093 := by
    simpa [prefixWord, tailWord_1045093, baseEnd_1045093] using wordTrace_append hprefix tailTrace_1045093
  have hstable : (prefixWord ++ tailWord_1045093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045093).length < 2 ^ (prefixWord ++ tailWord_1045093).sum := by decide
  have hdescent : baseEnd_1045093 < baseStart_1045093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045116 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_1045116 : Nat := 118140960795 + 1045116 * 2 ^ 59
def prefixEnd_1045116 : Nat := 4983230072969 + 3 ^ 40 * 1045116 * 2
def baseEnd_1045116 : Nat := 536646847704438212543605

theorem tailTrace_1045116 : CollatzResearch.WordTrace tailWord_1045116 prefixEnd_1045116 536646847704438212543605 := by
  unfold tailWord_1045116
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059256040865349223733601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25412341387820465631644801 19059256040865349223733601)
  ·
    refine ⟨14294442030649011917800201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19059256040865349223733601 14294442030649011917800201)
    ·
      refine ⟨10720831522986758938350151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14294442030649011917800201 10720831522986758938350151)
      ·
        refine ⟨16081247284480138407525227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720831522986758938350151 16081247284480138407525227)
        ·
          refine ⟨24121870926720207611287841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081247284480138407525227 24121870926720207611287841)
          ·
            refine ⟨18091403195040155708465881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24121870926720207611287841 18091403195040155708465881)
            ·
              refine ⟨13568552396280116781349411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18091403195040155708465881 13568552396280116781349411)
              ·
                refine ⟨20352828594420175172024117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13568552396280116781349411 20352828594420175172024117)
                ·
                  refine ⟨1908077680726891422377261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20352828594420175172024117 1908077680726891422377261)
                  ·
                    refine ⟨715529130272584283391473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908077680726891422377261 715529130272584283391473)
                    ·
                      refine ⟨536646847704438212543605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715529130272584283391473 536646847704438212543605)
                      ·
                        rfl

theorem cell23_1045116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_1045116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045116 prefixEnd_1045116 := by exact prefixLift 1045116
  have htrace : WordTrace (prefixWord ++ tailWord_1045116) baseStart_1045116 baseEnd_1045116 := by
    simpa [prefixWord, tailWord_1045116, baseEnd_1045116] using wordTrace_append hprefix tailTrace_1045116
  have hstable : (prefixWord ++ tailWord_1045116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045116).length < 2 ^ (prefixWord ++ tailWord_1045116).sum := by decide
  have hdescent : baseEnd_1045116 < baseStart_1045116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045149 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1045149 : Nat := 118140960795 + 1045149 * 2 ^ 59
def prefixEnd_1045149 : Nat := 4983230072969 + 3 ^ 40 * 1045149 * 2
def baseEnd_1045149 : Nat := 536663792566036583430953

theorem tailTrace_1045149 : CollatzResearch.WordTrace tailWord_1045149 prefixEnd_1045149 536663792566036583430953 := by
  unfold tailWord_1045149
  simp only [CollatzResearch.WordTrace]
  refine ⟨38119715690611145083418501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25413143793740763388945667 38119715690611145083418501)
  ·
    refine ⟨7147446691989589703140969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38119715690611145083418501 7147446691989589703140969)
    ·
      refine ⟨5360585018992192277355727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7147446691989589703140969 5360585018992192277355727)
      ·
        refine ⟨8040877528488288416033591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360585018992192277355727 8040877528488288416033591)
        ·
          refine ⟨12061316292732432624050387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040877528488288416033591 12061316292732432624050387)
          ·
            refine ⟨18091974439098648936075581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061316292732432624050387 18091974439098648936075581)
            ·
              refine ⟨6784490414661993351028343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18091974439098648936075581 6784490414661993351028343)
              ·
                refine ⟨10176735621992990026542515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784490414661993351028343 10176735621992990026542515)
                ·
                  refine ⟨15265103432989485039813773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10176735621992990026542515 15265103432989485039813773)
                  ·
                    refine ⟨5724413787371056889930165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15265103432989485039813773 5724413787371056889930165)
                    ·
                      refine ⟨536663792566036583430953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5724413787371056889930165 536663792566036583430953)
                      ·
                        rfl

theorem cell23_1045149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1045149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045149 prefixEnd_1045149 := by exact prefixLift 1045149
  have htrace : WordTrace (prefixWord ++ tailWord_1045149) baseStart_1045149 baseEnd_1045149 := by
    simpa [prefixWord, tailWord_1045149, baseEnd_1045149] using wordTrace_append hprefix tailTrace_1045149
  have hstable : (prefixWord ++ tailWord_1045149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045149).length < 2 ^ (prefixWord ++ tailWord_1045149).sum := by decide
  have hdescent : baseEnd_1045149 < baseStart_1045149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045150 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_1045150 : Nat := 118140960795 + 1045150 * 2 ^ 59
def prefixEnd_1045150 : Nat := 4983230072969 + 3 ^ 40 * 1045150 * 2
def baseEnd_1045150 : Nat := 536664306046691079518449

theorem tailTrace_1045150 : CollatzResearch.WordTrace tailWord_1045150 prefixEnd_1045150 536664306046691079518449 := by
  unfold tailWord_1045150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764969020450940281775613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25413168109071681502803269 4764969020450940281775613)
  ·
    refine ⟨1786863382669102605665855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4764969020450940281775613 1786863382669102605665855)
    ·
      refine ⟨2680295074003653908498783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786863382669102605665855 2680295074003653908498783)
      ·
        refine ⟨4020442611005480862748175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680295074003653908498783 4020442611005480862748175)
        ·
          refine ⟨6030663916508221294122263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020442611005480862748175 6030663916508221294122263)
          ·
            refine ⟨9045995874762331941183395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030663916508221294122263 9045995874762331941183395)
            ·
              refine ⟨13568993812143497911775093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045995874762331941183395 13568993812143497911775093)
              ·
                refine ⟨1272093169888452929228915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13568993812143497911775093 1272093169888452929228915)
                ·
                  refine ⟨1908139754832679393843373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272093169888452929228915 1908139754832679393843373)
                  ·
                    refine ⟨715552408062254772691265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908139754832679393843373 715552408062254772691265)
                    ·
                      refine ⟨536664306046691079518449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715552408062254772691265 536664306046691079518449)
                      ·
                        rfl

theorem cell23_1045150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_1045150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045150 prefixEnd_1045150 := by exact prefixLift 1045150
  have htrace : WordTrace (prefixWord ++ tailWord_1045150) baseStart_1045150 baseEnd_1045150 := by
    simpa [prefixWord, tailWord_1045150, baseEnd_1045150] using wordTrace_append hprefix tailTrace_1045150
  have hstable : (prefixWord ++ tailWord_1045150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045150).length < 2 ^ (prefixWord ++ tailWord_1045150).sum := by decide
  have hdescent : baseEnd_1045150 < baseStart_1045150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045180 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_1045180 : Nat := 118140960795 + 1045180 * 2 ^ 59
def prefixEnd_1045180 : Nat := 4983230072969 + 3 ^ 40 * 1045180 * 2
def baseEnd_1045180 : Nat := 536679710466325962143311

theorem tailTrace_1045180 : CollatzResearch.WordTrace tailWord_1045180 prefixEnd_1045180 536679710466325962143311 := by
  unfold tailWord_1045180
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060423176749418688898497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25413897568999224918531329 19060423176749418688898497)
  ·
    refine ⟨14295317382562064016673873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19060423176749418688898497 14295317382562064016673873)
    ·
      refine ⟨10721488036921548012505405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14295317382562064016673873 10721488036921548012505405)
      ·
        refine ⟨4020558013845580504689527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10721488036921548012505405 4020558013845580504689527)
        ·
          refine ⟨6030837020768370757034291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020558013845580504689527 6030837020768370757034291)
          ·
            refine ⟨9046255531152556135551437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030837020768370757034291 9046255531152556135551437)
            ·
              refine ⟨3392345824182208550831789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9046255531152556135551437 3392345824182208550831789)
              ·
                refine ⟨1272129684068328206561921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3392345824182208550831789 1272129684068328206561921)
                ·
                  refine ⟨954097263051246154921441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1272129684068328206561921 954097263051246154921441)
                  ·
                    refine ⟨715572947288434616191081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954097263051246154921441 715572947288434616191081)
                    ·
                      refine ⟨536679710466325962143311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715572947288434616191081 536679710466325962143311)
                      ·
                        rfl

theorem cell23_1045180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_1045180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045180 prefixEnd_1045180 := by exact prefixLift 1045180
  have htrace : WordTrace (prefixWord ++ tailWord_1045180) baseStart_1045180 baseEnd_1045180 := by
    simpa [prefixWord, tailWord_1045180, baseEnd_1045180] using wordTrace_append hprefix tailTrace_1045180
  have hstable : (prefixWord ++ tailWord_1045180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045180).length < 2 ^ (prefixWord ++ tailWord_1045180).sum := by decide
  have hdescent : baseEnd_1045180 < baseStart_1045180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045197 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1045197 : Nat := 118140960795 + 1045197 * 2 ^ 59
def prefixEnd_1045197 : Nat := 4983230072969 + 3 ^ 40 * 1045197 * 2
def baseEnd_1045197 : Nat := 536688439637452395630733

theorem tailTrace_1045197 : CollatzResearch.WordTrace tailWord_1045197 prefixEnd_1045197 536688439637452395630733 := by
  unfold tailWord_1045197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38121466394437249281165845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25414310929624832854110563 38121466394437249281165845)
  ·
    refine ⟨1786943737239246060054649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38121466394437249281165845 1786943737239246060054649)
    ·
      refine ⟨1340207802929434545040987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1786943737239246060054649 1340207802929434545040987)
      ·
        refine ⟨2010311704394151817561481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340207802929434545040987 2010311704394151817561481)
        ·
          refine ⟨1507733778295613863171111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2010311704394151817561481 1507733778295613863171111)
          ·
            refine ⟨2261600667443420794756667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507733778295613863171111 2261600667443420794756667)
            ·
              refine ⟨3392401001165131192135001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261600667443420794756667 3392401001165131192135001)
              ·
                refine ⟨2544300750873848394101251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392401001165131192135001 2544300750873848394101251)
                ·
                  refine ⟨3816451126310772591151877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544300750873848394101251 3816451126310772591151877)
                  ·
                    refine ⟨715584586183269860840977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3816451126310772591151877 715584586183269860840977)
                    ·
                      refine ⟨536688439637452395630733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715584586183269860840977 536688439637452395630733)
                      ·
                        rfl

theorem cell23_1045197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1045197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045197 prefixEnd_1045197 := by exact prefixLift 1045197
  have htrace : WordTrace (prefixWord ++ tailWord_1045197) baseStart_1045197 baseEnd_1045197 := by
    simpa [prefixWord, tailWord_1045197, baseEnd_1045197] using wordTrace_append hprefix tailTrace_1045197
  have hstable : (prefixWord ++ tailWord_1045197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045197).length < 2 ^ (prefixWord ++ tailWord_1045197).sum := by decide
  have hdescent : baseEnd_1045197 < baseStart_1045197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045209 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_1045209 : Nat := 118140960795 + 1045209 * 2 ^ 59
def prefixEnd_1045209 : Nat := 4983230072969 + 3 ^ 40 * 1045209 * 2
def baseEnd_1045209 : Nat := 536694601405306348680677

theorem tailTrace_1045209 : CollatzResearch.WordTrace tailWord_1045209 prefixEnd_1045209 536694601405306348680677 := by
  unfold tailWord_1045209
  simp only [CollatzResearch.WordTrace]
  refine ⟨38121904070393775330602681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25414602713595850220401787 38121904070393775330602681)
  ·
    refine ⟨28591428052795331497952011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38121904070393775330602681 28591428052795331497952011)
    ·
      refine ⟨42887142079192997246928017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28591428052795331497952011 42887142079192997246928017)
      ·
        refine ⟨32165356559394747935196013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42887142079192997246928017 32165356559394747935196013)
        ·
          refine ⟨12062008709773030475698505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32165356559394747935196013 12062008709773030475698505)
          ·
            refine ⟨9046506532329772856773879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062008709773030475698505 9046506532329772856773879)
            ·
              refine ⟨13569759798494659285160819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046506532329772856773879 13569759798494659285160819)
              ·
                refine ⟨20354639697741988927741229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569759798494659285160819 20354639697741988927741229)
                ·
                  refine ⟨7632989886653245847902961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20354639697741988927741229 7632989886653245847902961)
                  ·
                    refine ⟨5724742414989934385927221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7632989886653245847902961 5724742414989934385927221)
                    ·
                      refine ⟨536694601405306348680677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5724742414989934385927221 536694601405306348680677)
                      ·
                        rfl

theorem cell23_1045209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_1045209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045209 prefixEnd_1045209 := by exact prefixLift 1045209
  have htrace : WordTrace (prefixWord ++ tailWord_1045209) baseStart_1045209 baseEnd_1045209 := by
    simpa [prefixWord, tailWord_1045209, baseEnd_1045209] using wordTrace_append hprefix tailTrace_1045209
  have hstable : (prefixWord ++ tailWord_1045209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045209).length < 2 ^ (prefixWord ++ tailWord_1045209).sum := by decide
  have hdescent : baseEnd_1045209 < baseStart_1045209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045220 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1045220 : Nat := 118140960795 + 1045220 * 2 ^ 59
def prefixEnd_1045220 : Nat := 4983230072969 + 3 ^ 40 * 1045220 * 2
def baseEnd_1045220 : Nat := 59633361076945089515903

theorem tailTrace_1045220 : CollatzResearch.WordTrace tailWord_1045220 prefixEnd_1045220 59633361076945089515903 := by
  unfold tailWord_1045220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061152636676962104626557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25414870182235949472835409 19061152636676962104626557)
  ·
    refine ⟨7147932238753860789234959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19061152636676962104626557 7147932238753860789234959)
    ·
      refine ⟨10721898358130791183852439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7147932238753860789234959 10721898358130791183852439)
      ·
        refine ⟨16082847537196186775778659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10721898358130791183852439 16082847537196186775778659)
        ·
          refine ⟨24124271305794280163667989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16082847537196186775778659 24124271305794280163667989)
          ·
            refine ⟨1130825217459106882671937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24124271305794280163667989 1130825217459106882671937)
            ·
              refine ⟨848118913094330162003953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130825217459106882671937 848118913094330162003953)
              ·
                refine ⟨636089184820747621502965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848118913094330162003953 636089184820747621502965)
                ·
                  refine ⟨59633361076945089515903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 636089184820747621502965 59633361076945089515903)
                  ·
                    rfl

theorem cell23_1045220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1045220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045220 prefixEnd_1045220 := by exact prefixLift 1045220
  have htrace : WordTrace (prefixWord ++ tailWord_1045220) baseStart_1045220 baseEnd_1045220 := by
    simpa [prefixWord, tailWord_1045220, baseEnd_1045220] using wordTrace_append hprefix tailTrace_1045220
  have hstable : (prefixWord ++ tailWord_1045220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045220).length < 2 ^ (prefixWord ++ tailWord_1045220).sum := by decide
  have hdescent : baseEnd_1045220 < baseStart_1045220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045250 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1045250 : Nat := 118140960795 + 1045250 * 2 ^ 59
def prefixEnd_1045250 : Nat := 4983230072969 + 3 ^ 40 * 1045250 * 2
def baseEnd_1045250 : Nat := 178905218037380229422663

theorem tailTrace_1045250 : CollatzResearch.WordTrace tailWord_1045250 prefixEnd_1045250 178905218037380229422663 := by
  unfold tailWord_1045250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530849865811309833211301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25415599642163492888563469 9530849865811309833211301)
  ·
    refine ⟨1787034349839620593727119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9530849865811309833211301 1787034349839620593727119)
    ·
      refine ⟨2680551524759430890590679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787034349839620593727119 2680551524759430890590679)
      ·
        refine ⟨4020827287139146335886019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680551524759430890590679 4020827287139146335886019)
        ·
          refine ⟨6031240930708719503829029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020827287139146335886019 6031240930708719503829029)
          ·
            refine ⟨1130857674507884906967943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6031240930708719503829029 1130857674507884906967943)
            ·
              refine ⟨1696286511761827360451915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130857674507884906967943 1696286511761827360451915)
              ·
                refine ⟨2544429767642741040677873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696286511761827360451915 2544429767642741040677873)
                ·
                  refine ⟨1908322325732055780508405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544429767642741040677873 1908322325732055780508405)
                  ·
                    refine ⟨178905218037380229422663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1908322325732055780508405 178905218037380229422663)
                    ·
                      rfl

theorem cell23_1045250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1045250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045250 prefixEnd_1045250 := by exact prefixLift 1045250
  have htrace : WordTrace (prefixWord ++ tailWord_1045250) baseStart_1045250 baseEnd_1045250 := by
    simpa [prefixWord, tailWord_1045250, baseEnd_1045250] using wordTrace_append hprefix tailTrace_1045250
  have hstable : (prefixWord ++ tailWord_1045250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045250).length < 2 ^ (prefixWord ++ tailWord_1045250).sum := by decide
  have hdescent : baseEnd_1045250 < baseStart_1045250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045259 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 8]
def baseStart_1045259 : Nat := 118140960795 + 1045259 * 2 ^ 59
def prefixEnd_1045259 : Nat := 4983230072969 + 3 ^ 40 * 1045259 * 2
def baseEnd_1045259 : Nat := 59635586159781239228383

theorem tailTrace_1045259 : CollatzResearch.WordTrace tailWord_1045259 prefixEnd_1045259 59635586159781239228383 := by
  unfold tailWord_1045259
  simp only [CollatzResearch.WordTrace]
  refine ⟨38123727720212633869922831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25415818480141755913281887 38123727720212633869922831)
  ·
    refine ⟨57185591580318950804884247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38123727720212633869922831 57185591580318950804884247)
    ·
      refine ⟨85778387370478426207326371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57185591580318950804884247 85778387370478426207326371)
      ·
        refine ⟨128667581055717639310989557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85778387370478426207326371 128667581055717639310989557)
        ·
          refine ⟨12062585723973528685405271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128667581055717639310989557 12062585723973528685405271)
          ·
            refine ⟨18093878585960293028107907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062585723973528685405271 18093878585960293028107907)
            ·
              refine ⟨27140817878940439542161861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18093878585960293028107907 27140817878940439542161861)
              ·
                refine ⟨5088903352301332414155349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27140817878940439542161861 5088903352301332414155349)
                ·
                  refine ⟨59635586159781239228383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5088903352301332414155349 59635586159781239228383)
                  ·
                    rfl

theorem cell23_1045259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 8].length) (baseStart_1045259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045259 prefixEnd_1045259 := by exact prefixLift 1045259
  have htrace : WordTrace (prefixWord ++ tailWord_1045259) baseStart_1045259 baseEnd_1045259 := by
    simpa [prefixWord, tailWord_1045259, baseEnd_1045259] using wordTrace_append hprefix tailTrace_1045259
  have hstable : (prefixWord ++ tailWord_1045259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045259).length < 2 ^ (prefixWord ++ tailWord_1045259).sum := by decide
  have hdescent : baseEnd_1045259 < baseStart_1045259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045276 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 8]
def baseStart_1045276 : Nat := 118140960795 + 1045276 * 2 ^ 59
def prefixEnd_1045276 : Nat := 4983230072969 + 3 ^ 40 * 1045276 * 2
def baseEnd_1045276 : Nat := 59636556067684176282541

theorem tailTrace_1045276 : CollatzResearch.WordTrace tailWord_1045276 prefixEnd_1045276 59636556067684176282541 := by
  unfold tailWord_1045276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062173880575522886645841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25416231840767363848861121 19062173880575522886645841)
  ·
    refine ⟨14296630410431642164984381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19062173880575522886645841 14296630410431642164984381)
    ·
      refine ⟨5361236403911865811869143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14296630410431642164984381 5361236403911865811869143)
      ·
        refine ⟨8041854605867798717803715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361236403911865811869143 8041854605867798717803715)
        ·
          refine ⟨12062781908801698076705573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041854605867798717803715 12062781908801698076705573)
          ·
            refine ⟨2261771607900318389382295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12062781908801698076705573 2261771607900318389382295)
            ·
              refine ⟨3392657411850477584073443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261771607900318389382295 3392657411850477584073443)
              ·
                refine ⟨5088986117775716376110165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392657411850477584073443 5088986117775716376110165)
                ·
                  refine ⟨59636556067684176282541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5088986117775716376110165 59636556067684176282541)
                  ·
                    rfl

theorem cell23_1045276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_1045276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045276 prefixEnd_1045276 := by exact prefixLift 1045276
  have htrace : WordTrace (prefixWord ++ tailWord_1045276) baseStart_1045276 baseEnd_1045276 := by
    simpa [prefixWord, tailWord_1045276, baseEnd_1045276] using wordTrace_append hprefix tailTrace_1045276
  have hstable : (prefixWord ++ tailWord_1045276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045276).length < 2 ^ (prefixWord ++ tailWord_1045276).sum := by decide
  have hdescent : baseEnd_1045276 < baseStart_1045276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045280 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 1, 4]
def baseStart_1045280 : Nat := 118140960795 + 1045280 * 2 ^ 59
def prefixEnd_1045280 : Nat := 4983230072969 + 3 ^ 40 * 1045280 * 2
def baseEnd_1045280 : Nat := 178910352843925190297617

theorem tailTrace_1045280 : CollatzResearch.WordTrace tailWord_1045280 prefixEnd_1045280 178910352843925190297617 := by
  unfold tailWord_1045280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062246826568277228218647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25416329102091036304291529 19062246826568277228218647)
  ·
    refine ⟨28593370239852415842327971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19062246826568277228218647 28593370239852415842327971)
    ·
      refine ⟨42890055359778623763491957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28593370239852415842327971 42890055359778623763491957)
      ·
        refine ⟨4020942689979245977827371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42890055359778623763491957 4020942689979245977827371)
        ·
          refine ⟨6031414034968868966741057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020942689979245977827371 6031414034968868966741057)
          ·
            refine ⟨4523560526226651725055793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031414034968868966741057 4523560526226651725055793)
            ·
              refine ⟨3392670394669988793791845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523560526226651725055793 3392670394669988793791845)
              ·
                refine ⟨636125699000622898835971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3392670394669988793791845 636125699000622898835971)
                ·
                  refine ⟨954188548500934348253957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636125699000622898835971 954188548500934348253957)
                  ·
                    refine ⟨178910352843925190297617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954188548500934348253957 178910352843925190297617)
                    ·
                      rfl

theorem cell23_1045280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 4].length) (baseStart_1045280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045280 prefixEnd_1045280 := by exact prefixLift 1045280
  have htrace : WordTrace (prefixWord ++ tailWord_1045280) baseStart_1045280 baseEnd_1045280 := by
    simpa [prefixWord, tailWord_1045280, baseEnd_1045280] using wordTrace_append hprefix tailTrace_1045280
  have hstable : (prefixWord ++ tailWord_1045280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045280).length < 2 ^ (prefixWord ++ tailWord_1045280).sum := by decide
  have hdescent : baseEnd_1045280 < baseStart_1045280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045303 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_1045303 : Nat := 118140960795 + 1045303 * 2 ^ 59
def prefixEnd_1045303 : Nat := 4983230072969 + 3 ^ 40 * 1045303 * 2
def baseEnd_1045303 : Nat := 536742868586828980905245

theorem tailTrace_1045303 : CollatzResearch.WordTrace tailWord_1045303 prefixEnd_1045303 536742868586828980905245 := by
  unfold tailWord_1045303
  simp only [CollatzResearch.WordTrace]
  refine ⟨38125332532053229384524563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25416888354702152923016375 38125332532053229384524563)
  ·
    refine ⟨57187998798079844076786845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38125332532053229384524563 57187998798079844076786845)
    ·
      refine ⟨21445499549279941528795067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57187998798079844076786845 21445499549279941528795067)
      ·
        refine ⟨32168249323919912293192601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21445499549279941528795067 32168249323919912293192601)
        ·
          refine ⟨24126186992939934219894451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32168249323919912293192601 24126186992939934219894451)
          ·
            refine ⟨36189280489409901329841677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24126186992939934219894451 36189280489409901329841677)
            ·
              refine ⟨13570980183528712998690629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36189280489409901329841677 13570980183528712998690629)
              ·
                refine ⟨2544558784411633687254493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13570980183528712998690629 2544558784411633687254493)
                ·
                  refine ⟨954209544154362632720435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2544558784411633687254493 954209544154362632720435)
                  ·
                    refine ⟨1431314316231543949080653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954209544154362632720435 1431314316231543949080653)
                    ·
                      refine ⟨536742868586828980905245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431314316231543949080653 536742868586828980905245)
                      ·
                        rfl

theorem cell23_1045303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_1045303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045303 prefixEnd_1045303 := by exact prefixLift 1045303
  have htrace : WordTrace (prefixWord ++ tailWord_1045303) baseStart_1045303 baseEnd_1045303 := by
    simpa [prefixWord, tailWord_1045303, baseEnd_1045303] using wordTrace_append hprefix tailTrace_1045303
  have hstable : (prefixWord ++ tailWord_1045303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045303).length < 2 ^ (prefixWord ++ tailWord_1045303).sum := by decide
  have hdescent : baseEnd_1045303 < baseStart_1045303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045330 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_1045330 : Nat := 118140960795 + 1045330 * 2 ^ 59
def prefixEnd_1045330 : Nat := 4983230072969 + 3 ^ 40 * 1045330 * 2
def baseEnd_1045330 : Nat := 536756732564500375267621

theorem tailTrace_1045330 : CollatzResearch.WordTrace tailWord_1045330 prefixEnd_1045330 536756732564500375267621 := by
  unfold tailWord_1045330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531579325738853248939361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25417544868636941997171629 9531579325738853248939361)
  ·
    refine ⟨7148684494304139936704521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9531579325738853248939361 7148684494304139936704521)
    ·
      refine ⟨5361513370728104952528391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7148684494304139936704521 5361513370728104952528391)
      ·
        refine ⟨8042270056092157428792587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361513370728104952528391 8042270056092157428792587)
        ·
          refine ⟨12063405084138236143188881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042270056092157428792587 12063405084138236143188881)
          ·
            refine ⟨9047553813103677107391661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12063405084138236143188881 9047553813103677107391661)
            ·
              refine ⟨3392832679913878915271873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9047553813103677107391661 3392832679913878915271873)
              ·
                refine ⟨2544624509935409186453905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392832679913878915271873 2544624509935409186453905)
                ·
                  refine ⟨1908468382451556889840429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2544624509935409186453905 1908468382451556889840429)
                  ·
                    refine ⟨715675643419333833690161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1908468382451556889840429 715675643419333833690161)
                    ·
                      refine ⟨536756732564500375267621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715675643419333833690161 536756732564500375267621)
                      ·
                        rfl

theorem cell23_1045330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_1045330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045330 prefixEnd_1045330 := by exact prefixLift 1045330
  have htrace : WordTrace (prefixWord ++ tailWord_1045330) baseStart_1045330 baseEnd_1045330 := by
    simpa [prefixWord, tailWord_1045330, baseEnd_1045330] using wordTrace_append hprefix tailTrace_1045330
  have hstable : (prefixWord ++ tailWord_1045330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045330).length < 2 ^ (prefixWord ++ tailWord_1045330).sum := by decide
  have hdescent : baseEnd_1045330 < baseStart_1045330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045356 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_1045356 : Nat := 118140960795 + 1045356 * 2 ^ 59
def prefixEnd_1045356 : Nat := 4983230072969 + 3 ^ 40 * 1045356 * 2
def baseEnd_1045356 : Nat := 536770083061517273542501

theorem tailTrace_1045356 : CollatzResearch.WordTrace tailWord_1045356 prefixEnd_1045356 536770083061517273542501 := by
  unfold tailWord_1045356
  simp only [CollatzResearch.WordTrace]
  refine ⟨19063632800430609718101961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25418177067240812957469281 19063632800430609718101961)
  ·
    refine ⟨14297724600322957288576471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19063632800430609718101961 14297724600322957288576471)
    ·
      refine ⟨21446586900484435932864707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14297724600322957288576471 21446586900484435932864707)
      ·
        refine ⟨32169880350726653899297061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21446586900484435932864707 32169880350726653899297061)
        ·
          refine ⟨6031852565761247606118199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32169880350726653899297061 6031852565761247606118199)
          ·
            refine ⟨9047778848641871409177299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031852565761247606118199 9047778848641871409177299)
            ·
              refine ⟨13571668272962807113765949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047778848641871409177299 13571668272962807113765949)
              ·
                refine ⟨5089375602361052667662231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13571668272962807113765949 5089375602361052667662231)
                ·
                  refine ⟨7634063403541579001493347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089375602361052667662231 7634063403541579001493347)
                  ·
                    refine ⟨11451095105312368502240021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7634063403541579001493347 11451095105312368502240021)
                    ·
                      refine ⟨536770083061517273542501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11451095105312368502240021 536770083061517273542501)
                      ·
                        rfl

theorem cell23_1045356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_1045356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045356 prefixEnd_1045356 := by exact prefixLift 1045356
  have htrace : WordTrace (prefixWord ++ tailWord_1045356) baseStart_1045356 baseEnd_1045356 := by
    simpa [prefixWord, tailWord_1045356, baseEnd_1045356] using wordTrace_append hprefix tailTrace_1045356
  have hstable : (prefixWord ++ tailWord_1045356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045356).length < 2 ^ (prefixWord ++ tailWord_1045356).sum := by decide
  have hdescent : baseEnd_1045356 < baseStart_1045356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045360 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2]
def baseStart_1045360 : Nat := 118140960795 + 1045360 * 2 ^ 59
def prefixEnd_1045360 : Nat := 4983230072969 + 3 ^ 40 * 1045360 * 2
def baseEnd_1045360 : Nat := 536772136984135257892483

theorem tailTrace_1045360 : CollatzResearch.WordTrace tailWord_1045360 prefixEnd_1045360 536772136984135257892483 := by
  unfold tailWord_1045360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19063705746423364059674767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25418274328564485412899689 19063705746423364059674767)
  ·
    refine ⟨28595558619635046089512151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19063705746423364059674767 28595558619635046089512151)
    ·
      refine ⟨42893337929452569134268227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28595558619635046089512151 42893337929452569134268227)
      ·
        refine ⟨64340006894178853701402341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42893337929452569134268227 64340006894178853701402341)
        ·
          refine ⟨12063751292658535069012939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64340006894178853701402341 12063751292658535069012939)
          ·
            refine ⟨18095626938987802603519409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063751292658535069012939 18095626938987802603519409)
            ·
              refine ⟨13571720204240851952639557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18095626938987802603519409 13571720204240851952639557)
              ·
                refine ⟨2544697538295159741119917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13571720204240851952639557 2544697538295159741119917)
                ·
                  refine ⟨954261576860684902919969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2544697538295159741119917 954261576860684902919969)
                  ·
                    refine ⟨715696182645513677189977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954261576860684902919969 715696182645513677189977)
                    ·
                      refine ⟨536772136984135257892483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715696182645513677189977 536772136984135257892483)
                      ·
                        rfl

theorem cell23_1045360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2].length) (baseStart_1045360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045360 prefixEnd_1045360 := by exact prefixLift 1045360
  have htrace : WordTrace (prefixWord ++ tailWord_1045360) baseStart_1045360 baseEnd_1045360 := by
    simpa [prefixWord, tailWord_1045360, baseEnd_1045360] using wordTrace_append hprefix tailTrace_1045360
  have hstable : (prefixWord ++ tailWord_1045360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045360).length < 2 ^ (prefixWord ++ tailWord_1045360).sum := by decide
  have hdescent : baseEnd_1045360 < baseStart_1045360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045374 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1045374 : Nat := 118140960795 + 1045374 * 2 ^ 59
def prefixEnd_1045374 : Nat := 4983230072969 + 3 ^ 40 * 1045374 * 2
def baseEnd_1045374 : Nat := 178926441904432734372473

theorem tailTrace_1045374 : CollatzResearch.WordTrace tailWord_1045374 prefixEnd_1045374 178926441904432734372473 := by
  unfold tailWord_1045374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4765990264349501063794897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25418614743197339006906117 4765990264349501063794897)
  ·
    refine ⟨3574492698262125797846173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4765990264349501063794897 3574492698262125797846173)
    ·
      refine ⟨1340434761848297174192315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3574492698262125797846173 1340434761848297174192315)
      ·
        refine ⟨2010652142772445761288473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340434761848297174192315 2010652142772445761288473)
        ·
          refine ⟨1507989107079334320966355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2010652142772445761288473 1507989107079334320966355)
          ·
            refine ⟨2261983660619001481449533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507989107079334320966355 2261983660619001481449533)
            ·
              refine ⟨848243872732125555543575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2261983660619001481449533 848243872732125555543575)
              ·
                refine ⟨1272365809098188333315363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848243872732125555543575 1272365809098188333315363)
                ·
                  refine ⟨1908548713647282499973045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272365809098188333315363 1908548713647282499973045)
                  ·
                    refine ⟨178926441904432734372473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1908548713647282499973045 178926441904432734372473)
                    ·
                      rfl

theorem cell23_1045374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1045374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045374 prefixEnd_1045374 := by exact prefixLift 1045374
  have htrace : WordTrace (prefixWord ++ tailWord_1045374) baseStart_1045374 baseEnd_1045374 := by
    simpa [prefixWord, tailWord_1045374, baseEnd_1045374] using wordTrace_append hprefix tailTrace_1045374
  have hstable : (prefixWord ++ tailWord_1045374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045374).length < 2 ^ (prefixWord ++ tailWord_1045374).sum := by decide
  have hdescent : baseEnd_1045374 < baseStart_1045374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045410 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1045410 : Nat := 118140960795 + 1045410 * 2 ^ 59
def prefixEnd_1045410 : Nat := 4983230072969 + 3 ^ 40 * 1045410 * 2
def baseEnd_1045410 : Nat := 536797811016860062267253

theorem tailTrace_1045410 : CollatzResearch.WordTrace tailWord_1045410 prefixEnd_1045410 536797811016860062267253 := by
  unfold tailWord_1045410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532308785666396664667421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25419490095110391105779789 9532308785666396664667421)
  ·
    refine ⟨3574615794624898749250283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9532308785666396664667421 3574615794624898749250283)
    ·
      refine ⟨5361923691937348123875425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574615794624898749250283 5361923691937348123875425)
      ·
        refine ⟨4021442768953011092906569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5361923691937348123875425 4021442768953011092906569)
        ·
          refine ⟨3016082076714758319679927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4021442768953011092906569 3016082076714758319679927)
          ·
            refine ⟨4524123115072137479519891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016082076714758319679927 4524123115072137479519891)
            ·
              refine ⟨6786184672608206219279837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524123115072137479519891 6786184672608206219279837)
              ·
                refine ⟨2544819252228077332229939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786184672608206219279837 2544819252228077332229939)
                ·
                  refine ⟨3817228878342115998344909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544819252228077332229939 3817228878342115998344909)
                  ·
                    refine ⟨1431460829378293499379341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817228878342115998344909 1431460829378293499379341)
                    ·
                      refine ⟨536797811016860062267253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431460829378293499379341 536797811016860062267253)
                      ·
                        rfl

theorem cell23_1045410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1045410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045410 prefixEnd_1045410 := by exact prefixLift 1045410
  have htrace : WordTrace (prefixWord ++ tailWord_1045410) baseStart_1045410 baseEnd_1045410 := by
    simpa [prefixWord, tailWord_1045410, baseEnd_1045410] using wordTrace_append hprefix tailTrace_1045410
  have hstable : (prefixWord ++ tailWord_1045410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045410).length < 2 ^ (prefixWord ++ tailWord_1045410).sum := by decide
  have hdescent : baseEnd_1045410 < baseStart_1045410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045428 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1045428 : Nat := 118140960795 + 1045428 * 2 ^ 59
def prefixEnd_1045428 : Nat := 4983230072969 + 3 ^ 40 * 1045428 * 2
def baseEnd_1045428 : Nat := 536807053668640991842171

theorem tailTrace_1045428 : CollatzResearch.WordTrace tailWord_1045428 prefixEnd_1045428 536807053668640991842171 := by
  unfold tailWord_1045428
  simp only [CollatzResearch.WordTrace]
  refine ⟨19064945828300187866412469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25419927771066917155216625 19064945828300187866412469)
  ·
    refine ⟨1787338671403142612476169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19064945828300187866412469 1787338671403142612476169)
    ·
      refine ⟨1340504003552356959357127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1787338671403142612476169 1340504003552356959357127)
      ·
        refine ⟨2010756005328535439035691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340504003552356959357127 2010756005328535439035691)
        ·
          refine ⟨3016134007992803158553537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010756005328535439035691 3016134007992803158553537)
          ·
            refine ⟨2262100505994602368915153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3016134007992803158553537 2262100505994602368915153)
            ·
              refine ⟨1696575379495951776686365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262100505994602368915153 1696575379495951776686365)
              ·
                refine ⟨636215767310981916257387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696575379495951776686365 636215767310981916257387)
                ·
                  refine ⟨954323650966472874386081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636215767310981916257387 954323650966472874386081)
                  ·
                    refine ⟨715742738224854655789561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954323650966472874386081 715742738224854655789561)
                    ·
                      refine ⟨536807053668640991842171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715742738224854655789561 536807053668640991842171)
                      ·
                        rfl

theorem cell23_1045428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1045428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045428 prefixEnd_1045428 := by exact prefixLift 1045428
  have htrace : WordTrace (prefixWord ++ tailWord_1045428) baseStart_1045428 baseEnd_1045428 := by
    simpa [prefixWord, tailWord_1045428, baseEnd_1045428] using wordTrace_append hprefix tailTrace_1045428
  have hstable : (prefixWord ++ tailWord_1045428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045428).length < 2 ^ (prefixWord ++ tailWord_1045428).sum := by decide
  have hdescent : baseEnd_1045428 < baseStart_1045428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045444 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1045444 : Nat := 118140960795 + 1045444 * 2 ^ 59
def prefixEnd_1045444 : Nat := 4983230072969 + 3 ^ 40 * 1045444 * 2
def baseEnd_1045444 : Nat := 536815269359112929242097

theorem tailTrace_1045444 : CollatzResearch.WordTrace tailWord_1045444 prefixEnd_1045444 536815269359112929242097 := by
  unfold tailWord_1045444
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065237612271205232703693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25420316816361606976938257 19065237612271205232703693)
  ·
    refine ⟨7149464104601701962263885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19065237612271205232703693 7149464104601701962263885)
    ·
      refine ⟨2681049039225638235848957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7149464104601701962263885 2681049039225638235848957)
      ·
        refine ⟨1005393389709614338443359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681049039225638235848957 1005393389709614338443359)
        ·
          refine ⟨1508090084564421507665039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005393389709614338443359 1508090084564421507665039)
          ·
            refine ⟨2262135126846632261497559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508090084564421507665039 2262135126846632261497559)
            ·
              refine ⟨3393202690269948392246339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262135126846632261497559 3393202690269948392246339)
              ·
                refine ⟨5089804035404922588369509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393202690269948392246339 5089804035404922588369509)
                ·
                  refine ⟨954338256638422985319283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5089804035404922588369509 954338256638422985319283)
                  ·
                    refine ⟨1431507384957634477978925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954338256638422985319283 1431507384957634477978925)
                    ·
                      refine ⟨536815269359112929242097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431507384957634477978925 536815269359112929242097)
                      ·
                        rfl

theorem cell23_1045444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1045444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045444 prefixEnd_1045444 := by exact prefixLift 1045444
  have htrace : WordTrace (prefixWord ++ tailWord_1045444) baseStart_1045444 baseEnd_1045444 := by
    simpa [prefixWord, tailWord_1045444, baseEnd_1045444] using wordTrace_append hprefix tailTrace_1045444
  have hstable : (prefixWord ++ tailWord_1045444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045444).length < 2 ^ (prefixWord ++ tailWord_1045444).sum := by decide
  have hdescent : baseEnd_1045444 < baseStart_1045444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045523 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4]
def baseStart_1045523 : Nat := 118140960795 + 1045523 * 2 ^ 59
def prefixEnd_1045523 : Nat := 4983230072969 + 3 ^ 40 * 1045523 * 2
def baseEnd_1045523 : Nat := 536855834330818120154233

theorem tailTrace_1045523 : CollatzResearch.WordTrace tailWord_1045523 prefixEnd_1045523 536855834330818120154233 := by
  unfold tailWord_1045523
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133356591256206957533223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25422237727504137971688815 38133356591256206957533223)
  ·
    refine ⟨57200034886884310436299835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38133356591256206957533223 57200034886884310436299835)
    ·
      refine ⟨85800052330326465654449753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57200034886884310436299835 85800052330326465654449753)
      ·
        refine ⟨64350039247744849240837315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85800052330326465654449753 64350039247744849240837315)
        ·
          refine ⟨96525058871617273861255973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64350039247744849240837315 96525058871617273861255973)
          ·
            refine ⟨18098448538428238848985495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96525058871617273861255973 18098448538428238848985495)
            ·
              refine ⟨27147672807642358273478243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18098448538428238848985495 27147672807642358273478243)
              ·
                refine ⟨40721509211463537410217365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27147672807642358273478243 40721509211463537410217365)
                ·
                  refine ⟨1908820744287353316103939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40721509211463537410217365 1908820744287353316103939)
                  ·
                    refine ⟨2863231116431029974155909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1908820744287353316103939 2863231116431029974155909)
                    ·
                      refine ⟨536855834330818120154233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2863231116431029974155909 536855834330818120154233)
                      ·
                        rfl

theorem cell23_1045523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_1045523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045523 prefixEnd_1045523 := by exact prefixLift 1045523
  have htrace : WordTrace (prefixWord ++ tailWord_1045523) baseStart_1045523 baseEnd_1045523 := by
    simpa [prefixWord, tailWord_1045523, baseEnd_1045523] using wordTrace_append hprefix tailTrace_1045523
  have hstable : (prefixWord ++ tailWord_1045523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045523).length < 2 ^ (prefixWord ++ tailWord_1045523).sum := by decide
  have hdescent : baseEnd_1045523 < baseStart_1045523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045553 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1045553 : Nat := 118140960795 + 1045553 * 2 ^ 59
def prefixEnd_1045553 : Nat := 4983230072969 + 3 ^ 40 * 1045553 * 2
def baseEnd_1045553 : Nat := 536871238750453002779095

theorem tailTrace_1045553 : CollatzResearch.WordTrace tailWord_1045553 prefixEnd_1045553 536871238750453002779095 := by
  unfold tailWord_1045553
  simp only [CollatzResearch.WordTrace]
  refine ⟨38134450781147522081125313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25422967187431681387416875 38134450781147522081125313)
  ·
    refine ⟨28600838085860641560843985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38134450781147522081125313 28600838085860641560843985)
    ·
      refine ⟨21450628564395481170632989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28600838085860641560843985 21450628564395481170632989)
      ·
        refine ⟨8043985711648305438987371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21450628564395481170632989 8043985711648305438987371)
        ·
          refine ⟨12065978567472458158481057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043985711648305438987371 12065978567472458158481057)
          ·
            refine ⟨9049483925604343618860793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065978567472458158481057 9049483925604343618860793)
            ·
              refine ⟨6787112944203257714145595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9049483925604343618860793 6787112944203257714145595)
              ·
                refine ⟨10180669416304886571218393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787112944203257714145595 10180669416304886571218393)
                ·
                  refine ⟨7635502062228664928413795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10180669416304886571218393 7635502062228664928413795)
                  ·
                    refine ⟨11453253093342997392620693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7635502062228664928413795 11453253093342997392620693)
                    ·
                      refine ⟨536871238750453002779095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11453253093342997392620693 536871238750453002779095)
                      ·
                        rfl

theorem cell23_1045553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1045553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045553 prefixEnd_1045553 := by exact prefixLift 1045553
  have htrace : WordTrace (prefixWord ++ tailWord_1045553) baseStart_1045553 baseEnd_1045553 := by
    simpa [prefixWord, tailWord_1045553, baseEnd_1045553] using wordTrace_append hprefix tailTrace_1045553
  have hstable : (prefixWord ++ tailWord_1045553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045553).length < 2 ^ (prefixWord ++ tailWord_1045553).sum := by decide
  have hdescent : baseEnd_1045553 < baseStart_1045553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045574 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1045574 : Nat := 118140960795 + 1045574 * 2 ^ 59
def prefixEnd_1045574 : Nat := 4983230072969 + 3 ^ 40 * 1045574 * 2
def baseEnd_1045574 : Nat := 536882021844197420616499

theorem tailTrace_1045574 : CollatzResearch.WordTrace tailWord_1045574 prefixEnd_1045574 536882021844197420616499 := by
  unfold tailWord_1045574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191725522314732583363743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25423477809380961778426517 1191725522314732583363743)
  ·
    refine ⟨1787588283472098875045615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191725522314732583363743 1787588283472098875045615)
    ·
      refine ⟨2681382425208148312568423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787588283472098875045615 2681382425208148312568423)
      ·
        refine ⟨4022073637812222468852635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681382425208148312568423 4022073637812222468852635)
        ·
          refine ⟨6033110456718333703278953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022073637812222468852635 6033110456718333703278953)
          ·
            refine ⟨4524832842538750277459215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033110456718333703278953 4524832842538750277459215)
            ·
              refine ⟨6787249263808125416188823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524832842538750277459215 6787249263808125416188823)
              ·
                refine ⟨10180873895712188124283235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787249263808125416188823 10180873895712188124283235)
                ·
                  refine ⟨15271310843568282186424853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180873895712188124283235 15271310843568282186424853)
                  ·
                    refine ⟨715842695792263227488665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15271310843568282186424853 715842695792263227488665)
                    ·
                      refine ⟨536882021844197420616499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715842695792263227488665 536882021844197420616499)
                      ·
                        rfl

theorem cell23_1045574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1045574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045574 prefixEnd_1045574 := by exact prefixLift 1045574
  have htrace : WordTrace (prefixWord ++ tailWord_1045574) baseStart_1045574 baseEnd_1045574 := by
    simpa [prefixWord, tailWord_1045574, baseEnd_1045574] using wordTrace_append hprefix tailTrace_1045574
  have hstable : (prefixWord ++ tailWord_1045574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045574).length < 2 ^ (prefixWord ++ tailWord_1045574).sum := by decide
  have hdescent : baseEnd_1045574 < baseStart_1045574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045603 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1045603 : Nat := 118140960795 + 1045603 * 2 ^ 59
def prefixEnd_1045603 : Nat := 4983230072969 + 3 ^ 40 * 1045603 * 2
def baseEnd_1045603 : Nat := 536896912783177807153865

theorem tailTrace_1045603 : CollatzResearch.WordTrace tailWord_1045603 prefixEnd_1045603 536896912783177807153865 := by
  unfold tailWord_1045603
  simp only [CollatzResearch.WordTrace]
  refine ⟨38136274430966380620445463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25424182953977587080296975 38136274430966380620445463)
  ·
    refine ⟨57204411646449570930668195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38136274430966380620445463 57204411646449570930668195)
    ·
      refine ⟨85806617469674356396002293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57204411646449570930668195 85806617469674356396002293)
      ·
        refine ⟨8044370387781970912125215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85806617469674356396002293 8044370387781970912125215)
        ·
          refine ⟨12066555581672956368187823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044370387781970912125215 12066555581672956368187823)
          ·
            refine ⟨18099833372509434552281735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12066555581672956368187823 18099833372509434552281735)
            ·
              refine ⟨27149750058764151828422603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18099833372509434552281735 27149750058764151828422603)
              ·
                refine ⟨40724625088146227742633905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27149750058764151828422603 40724625088146227742633905)
                ·
                  refine ⟨30543468816109670806975429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40724625088146227742633905 30543468816109670806975429)
                  ·
                    refine ⟨5726900403020563276307893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30543468816109670806975429 5726900403020563276307893)
                    ·
                      refine ⟨536896912783177807153865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5726900403020563276307893 536896912783177807153865)
                      ·
                        rfl

theorem cell23_1045603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1045603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045603 prefixEnd_1045603 := by exact prefixLift 1045603
  have htrace : WordTrace (prefixWord ++ tailWord_1045603) baseStart_1045603 baseEnd_1045603 := by
    simpa [prefixWord, tailWord_1045603, baseEnd_1045603] using wordTrace_append hprefix tailTrace_1045603
  have hstable : (prefixWord ++ tailWord_1045603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045603).length < 2 ^ (prefixWord ++ tailWord_1045603).sum := by decide
  have hdescent : baseEnd_1045603 < baseStart_1045603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045624 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 1, 1, 3]
def baseStart_1045624 : Nat := 118140960795 + 1045624 * 2 ^ 59
def prefixEnd_1045624 : Nat := 4983230072969 + 3 ^ 40 * 1045624 * 2
def baseEnd_1045624 : Nat := 536907695876922224991269

theorem tailTrace_1045624 : CollatzResearch.WordTrace tailWord_1045624 prefixEnd_1045624 536907695876922224991269 := by
  unfold tailWord_1045624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19068520181945150603479963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25424693575926867471306617 19068520181945150603479963)
  ·
    refine ⟨28602780272917725905219945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19068520181945150603479963 28602780272917725905219945)
    ·
      refine ⟨21452085204688294428914959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28602780272917725905219945 21452085204688294428914959)
      ·
        refine ⟨32178127807032441643372439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452085204688294428914959 32178127807032441643372439)
        ·
          refine ⟨48267191710548662465058659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32178127807032441643372439 48267191710548662465058659)
          ·
            refine ⟨72400787565822993697587989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48267191710548662465058659 72400787565822993697587989)
            ·
              refine ⟨3393786917147952829574437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72400787565822993697587989 3393786917147952829574437)
              ·
                refine ⟨636335046965241155545207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3393786917147952829574437 636335046965241155545207)
                ·
                  refine ⟨954502570447861733317811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636335046965241155545207 954502570447861733317811)
                  ·
                    refine ⟨1431753855671792599976717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954502570447861733317811 1431753855671792599976717)
                    ·
                      refine ⟨536907695876922224991269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431753855671792599976717 536907695876922224991269)
                      ·
                        rfl

theorem cell23_1045624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_1045624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045624 prefixEnd_1045624 := by exact prefixLift 1045624
  have htrace : WordTrace (prefixWord ++ tailWord_1045624) baseStart_1045624 baseEnd_1045624 := by
    simpa [prefixWord, tailWord_1045624, baseEnd_1045624] using wordTrace_append hprefix tailTrace_1045624
  have hstable : (prefixWord ++ tailWord_1045624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045624).length < 2 ^ (prefixWord ++ tailWord_1045624).sum := by decide
  have hdescent : baseEnd_1045624 < baseStart_1045624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045647 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 9, 2, 2]
def baseStart_1045647 : Nat := 118140960795 + 1045647 * 2 ^ 59
def prefixEnd_1045647 : Nat := 4983230072969 + 3 ^ 40 * 1045647 * 2
def baseEnd_1045647 : Nat := 536919505931975635003663

theorem tailTrace_1045647 : CollatzResearch.WordTrace tailWord_1045647 prefixEnd_1045647 536919505931975635003663 := by
  unfold tailWord_1045647
  simp only [CollatzResearch.WordTrace]
  refine ⟨38137879242806976135047195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25425252828537984090031463 38137879242806976135047195)
  ·
    refine ⟨57206818864210464202570793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38137879242806976135047195 57206818864210464202570793)
    ·
      refine ⟨42905114148157848151928095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57206818864210464202570793 42905114148157848151928095)
      ·
        refine ⟨64357671222236772227892143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42905114148157848151928095 64357671222236772227892143)
        ·
          refine ⟨96536506833355158341838215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64357671222236772227892143 96536506833355158341838215)
          ·
            refine ⟨144804760250032737512757323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96536506833355158341838215 144804760250032737512757323)
            ·
              refine ⟨217207140375049106269135985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144804760250032737512757323 217207140375049106269135985)
              ·
                refine ⟨162905355281286829701851989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217207140375049106269135985 162905355281286829701851989)
                ·
                  refine ⟨954523566101290017784289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 162905355281286829701851989 954523566101290017784289)
                  ·
                    refine ⟨715892674575967513338217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954523566101290017784289 715892674575967513338217)
                    ·
                      refine ⟨536919505931975635003663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715892674575967513338217 536919505931975635003663)
                      ·
                        rfl

theorem cell23_1045647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2, 2].length) (baseStart_1045647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045647 prefixEnd_1045647 := by exact prefixLift 1045647
  have htrace : WordTrace (prefixWord ++ tailWord_1045647) baseStart_1045647 baseEnd_1045647 := by
    simpa [prefixWord, tailWord_1045647, baseEnd_1045647] using wordTrace_append hprefix tailTrace_1045647
  have hstable : (prefixWord ++ tailWord_1045647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045647).length < 2 ^ (prefixWord ++ tailWord_1045647).sum := by decide
  have hdescent : baseEnd_1045647 < baseStart_1045647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045658 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1045658 : Nat := 118140960795 + 1045658 * 2 ^ 59
def prefixEnd_1045658 : Nat := 4983230072969 + 3 ^ 40 * 1045658 * 2
def baseEnd_1045658 : Nat := 536925154219175091966113

theorem tailTrace_1045658 : CollatzResearch.WordTrace tailWord_1045658 prefixEnd_1045658 536925154219175091966113 := by
  unfold tailWord_1045658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534570111441781253424407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25425520297178083342465085 9534570111441781253424407)
  ·
    refine ⟨14301855167162671880136611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9534570111441781253424407 14301855167162671880136611)
    ·
      refine ⟨21452782750744007820204917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14301855167162671880136611 21452782750744007820204917)
      ·
        refine ⟨2011198382882250733144211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21452782750744007820204917 2011198382882250733144211)
        ·
          refine ⟨3016797574323376099716317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011198382882250733144211 3016797574323376099716317)
          ·
            refine ⟨1131299090371266037393619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3016797574323376099716317 1131299090371266037393619)
            ·
              refine ⟨1696948635556899056090429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131299090371266037393619 1696948635556899056090429)
              ·
                refine ⟨636355738333837146033911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696948635556899056090429 636355738333837146033911)
                ·
                  refine ⟨954533607500755719050867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636355738333837146033911 954533607500755719050867)
                  ·
                    refine ⟨1431800411251133578576301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954533607500755719050867 1431800411251133578576301)
                    ·
                      refine ⟨536925154219175091966113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431800411251133578576301 536925154219175091966113)
                      ·
                        rfl

theorem cell23_1045658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1045658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045658 prefixEnd_1045658 := by exact prefixLift 1045658
  have htrace : WordTrace (prefixWord ++ tailWord_1045658) baseStart_1045658 baseEnd_1045658 := by
    simpa [prefixWord, tailWord_1045658, baseEnd_1045658] using wordTrace_append hprefix tailTrace_1045658
  have hstable : (prefixWord ++ tailWord_1045658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045658).length < 2 ^ (prefixWord ++ tailWord_1045658).sum := by decide
  have hdescent : baseEnd_1045658 < baseStart_1045658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045673 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_1045673 : Nat := 118140960795 + 1045673 * 2 ^ 59
def prefixEnd_1045673 : Nat := 4983230072969 + 3 ^ 40 * 1045673 * 2
def baseEnd_1045673 : Nat := 536932856428992533278543

theorem tailTrace_1045673 : CollatzResearch.WordTrace tailWord_1045673 prefixEnd_1045673 536932856428992533278543 := by
  unfold tailWord_1045673
  simp only [CollatzResearch.WordTrace]
  refine ⟨38138827540712782575493673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25425885027141855050329115 38138827540712782575493673)
  ·
    refine ⟨28604120655534586931620255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38138827540712782575493673 28604120655534586931620255)
    ·
      refine ⟨42906180983301880397430383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604120655534586931620255 42906180983301880397430383)
      ·
        refine ⟨64359271474952820596145575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42906180983301880397430383 64359271474952820596145575)
        ·
          refine ⟨96538907212429230894218363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64359271474952820596145575 96538907212429230894218363)
          ·
            refine ⟨144808360818643846341327545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96538907212429230894218363 144808360818643846341327545)
            ·
              refine ⟨108606270613982884755995659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144808360818643846341327545 108606270613982884755995659)
              ·
                refine ⟨162909405920974327133993489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108606270613982884755995659 162909405920974327133993489)
                ·
                  refine ⟨122182054440730745350495117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162909405920974327133993489 122182054440730745350495117)
                  ·
                    refine ⟨45818270415274029506435669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122182054440730745350495117 45818270415274029506435669)
                    ·
                      refine ⟨536932856428992533278543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45818270415274029506435669 536932856428992533278543)
                      ·
                        rfl

theorem cell23_1045673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_1045673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045673 prefixEnd_1045673 := by exact prefixLift 1045673
  have htrace : WordTrace (prefixWord ++ tailWord_1045673) baseStart_1045673 baseEnd_1045673 := by
    simpa [prefixWord, tailWord_1045673, baseEnd_1045673] using wordTrace_append hprefix tailTrace_1045673
  have hstable : (prefixWord ++ tailWord_1045673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045673).length < 2 ^ (prefixWord ++ tailWord_1045673).sum := by decide
  have hdescent : baseEnd_1045673 < baseStart_1045673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045674 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1045674 : Nat := 118140960795 + 1045674 * 2 ^ 59
def prefixEnd_1045674 : Nat := 4983230072969 + 3 ^ 40 * 1045674 * 2
def baseEnd_1045674 : Nat := 178977789969882343122013

theorem tailTrace_1045674 : CollatzResearch.WordTrace tailWord_1045674 prefixEnd_1045674 178977789969882343122013 := by
  unfold tailWord_1045674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534716003427289936570019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25425909342472773164186717 9534716003427289936570019)
  ·
    refine ⟨14302074005140934904855029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9534716003427289936570019 14302074005140934904855029)
    ·
      refine ⟨1340819437981962647330159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14302074005140934904855029 1340819437981962647330159)
      ·
        refine ⟨2011229156972943970995239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340819437981962647330159 2011229156972943970995239)
        ·
          refine ⟨3016843735459415956492859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011229156972943970995239 3016843735459415956492859)
          ·
            refine ⟨4525265603189123934739289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016843735459415956492859 4525265603189123934739289)
            ·
              refine ⟨3393949202391842951054467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525265603189123934739289 3393949202391842951054467)
              ·
                refine ⟨5090923803587764426581701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393949202391842951054467 5090923803587764426581701)
                ·
                  refine ⟨954548213172705829984069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5090923803587764426581701 954548213172705829984069)
                  ·
                    refine ⟨178977789969882343122013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954548213172705829984069 178977789969882343122013)
                    ·
                      rfl

theorem cell23_1045674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1045674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045674 prefixEnd_1045674 := by exact prefixLift 1045674
  have htrace : WordTrace (prefixWord ++ tailWord_1045674) baseStart_1045674 baseEnd_1045674 := by
    simpa [prefixWord, tailWord_1045674, baseEnd_1045674] using wordTrace_append hprefix tailTrace_1045674
  have hstable : (prefixWord ++ tailWord_1045674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045674).length < 2 ^ (prefixWord ++ tailWord_1045674).sum := by decide
  have hdescent : baseEnd_1045674 < baseStart_1045674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045680 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_1045680 : Nat := 118140960795 + 1045680 * 2 ^ 59
def prefixEnd_1045680 : Nat := 4983230072969 + 3 ^ 40 * 1045680 * 2
def baseEnd_1045680 : Nat := 536936450793574005891011

theorem tailTrace_1045680 : CollatzResearch.WordTrace tailWord_1045680 prefixEnd_1045680 536936450793574005891011 := by
  unfold tailWord_1045680
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069541425843711385499247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25426055234458281847332329 19069541425843711385499247)
  ·
    refine ⟨28604312138765567078248871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19069541425843711385499247 28604312138765567078248871)
    ·
      refine ⟨42906468208148350617373307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604312138765567078248871 42906468208148350617373307)
      ·
        refine ⟨64359702312222525926059961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42906468208148350617373307 64359702312222525926059961)
        ·
          refine ⟨48269776734166894444544971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64359702312222525926059961 48269776734166894444544971)
          ·
            refine ⟨72404665101250341666817457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48269776734166894444544971 72404665101250341666817457)
            ·
              refine ⟨54303498825937756250113093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72404665101250341666817457 54303498825937756250113093)
              ·
                refine ⟨10181906029863329296896205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54303498825937756250113093 10181906029863329296896205)
                ·
                  refine ⟨3818214761198748486336077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10181906029863329296896205 3818214761198748486336077)
                  ·
                    refine ⟨1431830535449530682376029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818214761198748486336077 1431830535449530682376029)
                    ·
                      refine ⟨536936450793574005891011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1431830535449530682376029 536936450793574005891011)
                      ·
                        rfl

theorem cell23_1045680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_1045680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045680 prefixEnd_1045680 := by exact prefixLift 1045680
  have htrace : WordTrace (prefixWord ++ tailWord_1045680) baseStart_1045680 baseEnd_1045680 := by
    simpa [prefixWord, tailWord_1045680, baseEnd_1045680] using wordTrace_append hprefix tailTrace_1045680
  have hstable : (prefixWord ++ tailWord_1045680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045680).length < 2 ^ (prefixWord ++ tailWord_1045680).sum := by decide
  have hdescent : baseEnd_1045680 < baseStart_1045680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045681 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1045681 : Nat := 118140960795 + 1045681 * 2 ^ 59
def prefixEnd_1045681 : Nat := 4983230072969 + 3 ^ 40 * 1045681 * 2
def baseEnd_1045681 : Nat := 536936964274228501978507

theorem tailTrace_1045681 : CollatzResearch.WordTrace tailWord_1045681 prefixEnd_1045681 536936964274228501978507 := by
  unfold tailWord_1045681
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139119324683799941784897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25426079549789199961189931 38139119324683799941784897)
  ·
    refine ⟨28604339493512849956338673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38139119324683799941784897 28604339493512849956338673)
    ·
      refine ⟨21453254620134637467254005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28604339493512849956338673 21453254620134637467254005)
      ·
        refine ⟨2011242620637622262555063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21453254620134637467254005 2011242620637622262555063)
        ·
          refine ⟨3016863930956433393832595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011242620637622262555063 3016863930956433393832595)
          ·
            refine ⟨4525295896434650090748893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016863930956433393832595 4525295896434650090748893)
            ·
              refine ⟨1696985961162993784030835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4525295896434650090748893 1696985961162993784030835)
              ·
                refine ⟨2545478941744490676046253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696985961162993784030835 2545478941744490676046253)
                ·
                  refine ⟨954554603154184003517345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2545478941744490676046253 954554603154184003517345)
                  ·
                    refine ⟨715915952365638002638009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954554603154184003517345 715915952365638002638009)
                    ·
                      refine ⟨536936964274228501978507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715915952365638002638009 536936964274228501978507)
                      ·
                        rfl

theorem cell23_1045681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1045681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045681 prefixEnd_1045681 := by exact prefixLift 1045681
  have htrace : WordTrace (prefixWord ++ tailWord_1045681) baseStart_1045681 baseEnd_1045681 := by
    simpa [prefixWord, tailWord_1045681, baseEnd_1045681] using wordTrace_append hprefix tailTrace_1045681
  have hstable : (prefixWord ++ tailWord_1045681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045681).length < 2 ^ (prefixWord ++ tailWord_1045681).sum := by decide
  have hdescent : baseEnd_1045681 < baseStart_1045681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045718 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1045718 : Nat := 118140960795 + 1045718 * 2 ^ 59
def prefixEnd_1045718 : Nat := 4983230072969 + 3 ^ 40 * 1045718 * 2
def baseEnd_1045718 : Nat := 536955963058444857215837

theorem tailTrace_1045718 : CollatzResearch.WordTrace tailWord_1045718 prefixEnd_1045718 536955963058444857215837 := by
  unfold tailWord_1045718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383779301596859703805113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25426979217033170173921205 2383779301596859703805113)
  ·
    refine ⟨1787834476197644777853835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2383779301596859703805113 1787834476197644777853835)
    ·
      refine ⟨2681751714296467166780753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787834476197644777853835 2681751714296467166780753)
      ·
        refine ⟨2011313785722350375085565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2681751714296467166780753 2011313785722350375085565)
        ·
          refine ⟨754242669645881390657087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2011313785722350375085565 754242669645881390657087)
          ·
            refine ⟨1131364004468822085985631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754242669645881390657087 1131364004468822085985631)
            ·
              refine ⟨1697046006703233128978447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131364004468822085985631 1697046006703233128978447)
              ·
                refine ⟨2545569010054849693467671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697046006703233128978447 2545569010054849693467671)
                ·
                  refine ⟨3818353515082274540201507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545569010054849693467671 3818353515082274540201507)
                  ·
                    refine ⟨5727530272623411810302261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3818353515082274540201507 5727530272623411810302261)
                    ·
                      refine ⟨536955963058444857215837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5727530272623411810302261 536955963058444857215837)
                      ·
                        rfl

theorem cell23_1045718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1045718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045718 prefixEnd_1045718 := by exact prefixLift 1045718
  have htrace : WordTrace (prefixWord ++ tailWord_1045718) baseStart_1045718 baseEnd_1045718 := by
    simpa [prefixWord, tailWord_1045718, baseEnd_1045718] using wordTrace_append hprefix tailTrace_1045718
  have hstable : (prefixWord ++ tailWord_1045718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045718).length < 2 ^ (prefixWord ++ tailWord_1045718).sum := by decide
  have hdescent : baseEnd_1045718 < baseStart_1045718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045754 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_1045754 : Nat := 118140960795 + 1045754 * 2 ^ 59
def prefixEnd_1045754 : Nat := 4983230072969 + 3 ^ 40 * 1045754 * 2
def baseEnd_1045754 : Nat := 536974448362006716365671

theorem tailTrace_1045754 : CollatzResearch.WordTrace tailWord_1045754 prefixEnd_1045754 536974448362006716365671 := by
  unfold tailWord_1045754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535445463354833352298079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25427854568946222272794877 9535445463354833352298079)
  ·
    refine ⟨14303168195032250028447119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535445463354833352298079 14303168195032250028447119)
    ·
      refine ⟨21454752292548375042670679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303168195032250028447119 21454752292548375042670679)
      ·
        refine ⟨32182128438822562564006019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454752292548375042670679 32182128438822562564006019)
        ·
          refine ⟨48273192658233843846009029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32182128438822562564006019 48273192658233843846009029)
          ·
            refine ⟨9051223623418845721126693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48273192658233843846009029 9051223623418845721126693)
            ·
              refine ⟨1697104429391033572711255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9051223623418845721126693 1697104429391033572711255)
              ·
                refine ⟨2545656644086550359066883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697104429391033572711255 2545656644086550359066883)
                ·
                  refine ⟨3818484966129825538600325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545656644086550359066883 3818484966129825538600325)
                  ·
                    refine ⟨715965931149342288487561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3818484966129825538600325 715965931149342288487561)
                    ·
                      refine ⟨536974448362006716365671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 715965931149342288487561 536974448362006716365671)
                      ·
                        rfl

theorem cell23_1045754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_1045754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045754 prefixEnd_1045754 := by exact prefixLift 1045754
  have htrace : WordTrace (prefixWord ++ tailWord_1045754) baseStart_1045754 baseEnd_1045754 := by
    simpa [prefixWord, tailWord_1045754, baseEnd_1045754] using wordTrace_append hprefix tailTrace_1045754
  have hstable : (prefixWord ++ tailWord_1045754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045754).length < 2 ^ (prefixWord ++ tailWord_1045754).sum := by decide
  have hdescent : baseEnd_1045754 < baseStart_1045754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045770 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1045770 : Nat := 118140960795 + 1045770 * 2 ^ 59
def prefixEnd_1045770 : Nat := 4983230072969 + 3 ^ 40 * 1045770 * 2
def baseEnd_1045770 : Nat := 536982664052478653765597

theorem tailTrace_1045770 : CollatzResearch.WordTrace tailWord_1045770 prefixEnd_1045770 536982664052478653765597 := by
  unfold tailWord_1045770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535591355340342035443691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25428243614240912094516509 9535591355340342035443691)
  ·
    refine ⟨14303387033010513053165537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535591355340342035443691 14303387033010513053165537)
    ·
      refine ⟨10727540274757884789874153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14303387033010513053165537 10727540274757884789874153)
      ·
        refine ⟨8045655206068413592405615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10727540274757884789874153 8045655206068413592405615)
        ·
          refine ⟨12068482809102620388608423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8045655206068413592405615 12068482809102620388608423)
          ·
            refine ⟨18102724213653930582912635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12068482809102620388608423 18102724213653930582912635)
            ·
              refine ⟨27154086320480895874368953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18102724213653930582912635 27154086320480895874368953)
              ·
                refine ⟨20365564740360671905776715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27154086320480895874368953 20365564740360671905776715)
                ·
                  refine ⟨30548347110541007858665073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20365564740360671905776715 30548347110541007858665073)
                  ·
                    refine ⟨22911260332905755893998805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30548347110541007858665073 22911260332905755893998805)
                    ·
                      refine ⟨536982664052478653765597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22911260332905755893998805 536982664052478653765597)
                      ·
                        rfl

theorem cell23_1045770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1045770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045770 prefixEnd_1045770 := by exact prefixLift 1045770
  have htrace : WordTrace (prefixWord ++ tailWord_1045770) baseStart_1045770 baseEnd_1045770 := by
    simpa [prefixWord, tailWord_1045770, baseEnd_1045770] using wordTrace_append hprefix tailTrace_1045770
  have hstable : (prefixWord ++ tailWord_1045770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045770).length < 2 ^ (prefixWord ++ tailWord_1045770).sum := by decide
  have hdescent : baseEnd_1045770 < baseStart_1045770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045794 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1045794 : Nat := 118140960795 + 1045794 * 2 ^ 59
def prefixEnd_1045794 : Nat := 4983230072969 + 3 ^ 40 * 1045794 * 2
def baseEnd_1045794 : Nat := 59666109732020728873943

theorem tailTrace_1045794 : CollatzResearch.WordTrace tailWord_1045794 prefixEnd_1045794 59666109732020728873943 := by
  unfold tailWord_1045794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535810193318605060162109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25428827182182946827098957 9535810193318605060162109)
  ·
    refine ⟨3575928822494476897560791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9535810193318605060162109 3575928822494476897560791)
    ·
      refine ⟨5363893233741715346341187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575928822494476897560791 5363893233741715346341187)
      ·
        refine ⟨8045839850612573019511781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363893233741715346341187 8045839850612573019511781)
        ·
          refine ⟨1508594971989857441158459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8045839850612573019511781 1508594971989857441158459)
          ·
            refine ⟨2262892457984786161737689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508594971989857441158459 2262892457984786161737689)
            ·
              refine ⟨1697169343488589621303267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262892457984786161737689 1697169343488589621303267)
              ·
                refine ⟨2545754015232884431954901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697169343488589621303267 2545754015232884431954901)
                ·
                  refine ⟨59666109732020728873943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2545754015232884431954901 59666109732020728873943)
                  ·
                    rfl

theorem cell23_1045794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1045794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045794 prefixEnd_1045794 := by exact prefixLift 1045794
  have htrace : WordTrace (prefixWord ++ tailWord_1045794) baseStart_1045794 baseEnd_1045794 := by
    simpa [prefixWord, tailWord_1045794, baseEnd_1045794] using wordTrace_append hprefix tailTrace_1045794
  have hstable : (prefixWord ++ tailWord_1045794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045794).length < 2 ^ (prefixWord ++ tailWord_1045794).sum := by decide
  have hdescent : baseEnd_1045794 < baseStart_1045794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045827 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1045827 : Nat := 118140960795 + 1045827 * 2 ^ 59
def prefixEnd_1045827 : Nat := 4983230072969 + 3 ^ 40 * 1045827 * 2
def baseEnd_1045827 : Nat := 537011932449784930752835

theorem tailTrace_1045827 : CollatzResearch.WordTrace tailWord_1045827 prefixEnd_1045827 537011932449784930752835 := by
  unfold tailWord_1045827
  simp only [CollatzResearch.WordTrace]
  refine ⟨38144444382154866876599735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25429629588103244584399823 38144444382154866876599735)
  ·
    refine ⟨57216666573232300314899603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38144444382154866876599735 57216666573232300314899603)
    ·
      refine ⟨85824999859848450472349405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57216666573232300314899603 85824999859848450472349405)
      ·
        refine ⟨32184374947443168927131027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85824999859848450472349405 32184374947443168927131027)
        ·
          refine ⟨48276562421164753390696541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32184374947443168927131027 48276562421164753390696541)
          ·
            refine ⟨18103710907936782521511203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48276562421164753390696541 18103710907936782521511203)
            ·
              refine ⟨27155566361905173782266805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18103710907936782521511203 27155566361905173782266805)
              ·
                refine ⟨2545834346428610042087513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27155566361905173782266805 2545834346428610042087513)
                ·
                  refine ⟨1909375759821457531565635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2545834346428610042087513 1909375759821457531565635)
                  ·
                    refine ⟨2864063639732186297348453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909375759821457531565635 2864063639732186297348453)
                    ·
                      refine ⟨537011932449784930752835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2864063639732186297348453 537011932449784930752835)
                      ·
                        rfl

theorem cell23_1045827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1045827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045827 prefixEnd_1045827 := by exact prefixLift 1045827
  have htrace : WordTrace (prefixWord ++ tailWord_1045827) baseStart_1045827 baseEnd_1045827 := by
    simpa [prefixWord, tailWord_1045827, baseEnd_1045827] using wordTrace_append hprefix tailTrace_1045827
  have hstable : (prefixWord ++ tailWord_1045827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045827).length < 2 ^ (prefixWord ++ tailWord_1045827).sum := by decide
  have hdescent : baseEnd_1045827 < baseStart_1045827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045828 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1045828 : Nat := 118140960795 + 1045828 * 2 ^ 59
def prefixEnd_1045828 : Nat := 4983230072969 + 3 ^ 40 * 1045828 * 2
def baseEnd_1045828 : Nat := 59668049547826602982259

theorem tailTrace_1045828 : CollatzResearch.WordTrace tailWord_1045828 prefixEnd_1045828 59668049547826602982259 := by
  unfold tailWord_1045828
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072240427575622023693069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25429653903434162698257425 19072240427575622023693069)
  ·
    refine ⟨7152090160340858258884901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19072240427575622023693069 7152090160340858258884901)
    ·
      refine ⟨1341016905063910923540919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7152090160340858258884901 1341016905063910923540919)
      ·
        refine ⟨2011525357595866385311379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341016905063910923540919 2011525357595866385311379)
        ·
          refine ⟨3017288036393799577967069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011525357595866385311379 3017288036393799577967069)
          ·
            refine ⟨1131483013647674841737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3017288036393799577967069 1131483013647674841737651)
            ·
              refine ⟨1697224520471512262606477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131483013647674841737651 1697224520471512262606477)
              ·
                refine ⟨636459195176817098477429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697224520471512262606477 636459195176817098477429)
                ·
                  refine ⟨59668049547826602982259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 636459195176817098477429 59668049547826602982259)
                  ·
                    rfl

theorem cell23_1045828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1045828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045828 prefixEnd_1045828 := by exact prefixLift 1045828
  have htrace : WordTrace (prefixWord ++ tailWord_1045828) baseStart_1045828 baseEnd_1045828 := by
    simpa [prefixWord, tailWord_1045828, baseEnd_1045828] using wordTrace_append hprefix tailTrace_1045828
  have hstable : (prefixWord ++ tailWord_1045828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045828).length < 2 ^ (prefixWord ++ tailWord_1045828).sum := by decide
  have hdescent : baseEnd_1045828 < baseStart_1045828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045844 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1045844 : Nat := 118140960795 + 1045844 * 2 ^ 59
def prefixEnd_1045844 : Nat := 4983230072969 + 3 ^ 40 * 1045844 * 2
def baseEnd_1045844 : Nat := 537020661620911364240257

theorem tailTrace_1045844 : CollatzResearch.WordTrace tailWord_1045844 prefixEnd_1045844 537020661620911364240257 := by
  unfold tailWord_1045844
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072532211546639389984293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25430042948728852519979057 19072532211546639389984293)
  ·
    refine ⟨3576099789664994885622055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19072532211546639389984293 3576099789664994885622055)
    ·
      refine ⟨5364149684497492328433083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576099789664994885622055 5364149684497492328433083)
      ·
        refine ⟨8046224526746238492649625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364149684497492328433083 8046224526746238492649625)
        ·
          refine ⟨6034668395059678869487219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8046224526746238492649625 6034668395059678869487219)
          ·
            refine ⟨9052002592589518304230829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034668395059678869487219 9052002592589518304230829)
            ·
              refine ⟨3394500972221069364086561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9052002592589518304230829 3394500972221069364086561)
              ·
                refine ⟨2545875729165802023064921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394500972221069364086561 2545875729165802023064921)
                ·
                  refine ⟨1909406796874351517298691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2545875729165802023064921 1909406796874351517298691)
                  ·
                    refine ⟨2864110195311527275948037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909406796874351517298691 2864110195311527275948037)
                    ·
                      refine ⟨537020661620911364240257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2864110195311527275948037 537020661620911364240257)
                      ·
                        rfl

theorem cell23_1045844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1045844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045844 prefixEnd_1045844 := by exact prefixLift 1045844
  have htrace : WordTrace (prefixWord ++ tailWord_1045844) baseStart_1045844 baseEnd_1045844 := by
    simpa [prefixWord, tailWord_1045844, baseEnd_1045844] using wordTrace_append hprefix tailTrace_1045844
  have hstable : (prefixWord ++ tailWord_1045844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045844).length < 2 ^ (prefixWord ++ tailWord_1045844).sum := by decide
  have hdescent : baseEnd_1045844 < baseStart_1045844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045945 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1045945 : Nat := 118140960795 + 1045945 * 2 ^ 59
def prefixEnd_1045945 : Nat := 4983230072969 + 3 ^ 40 * 1045945 * 2
def baseEnd_1045945 : Nat := 537072523167015469077293

theorem tailTrace_1045945 : CollatzResearch.WordTrace tailWord_1045945 prefixEnd_1045945 537072523167015469077293 := by
  unfold tailWord_1045945
  simp only [CollatzResearch.WordTrace]
  refine ⟨38148748195727373029395289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25432498797151582019596859 38148748195727373029395289)
  ·
    refine ⟨28611561146795529772046467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38148748195727373029395289 28611561146795529772046467)
    ·
      refine ⟨42917341720193294658069701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28611561146795529772046467 42917341720193294658069701)
      ·
        refine ⟨8047001572536242748388069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42917341720193294658069701 8047001572536242748388069)
        ·
          refine ⟨1508812794850545515322763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8047001572536242748388069 1508812794850545515322763)
          ·
            refine ⟨2263219192275818272984145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508812794850545515322763 2263219192275818272984145)
            ·
              refine ⟨1697414394206863704738109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263219192275818272984145 1697414394206863704738109)
              ·
                refine ⟨636530397827573889276791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697414394206863704738109 636530397827573889276791)
                ·
                  refine ⟨954795596741360833915187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636530397827573889276791 954795596741360833915187)
                  ·
                    refine ⟨1432193395112041250872781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954795596741360833915187 1432193395112041250872781)
                    ·
                      refine ⟨537072523167015469077293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432193395112041250872781 537072523167015469077293)
                      ·
                        rfl

theorem cell23_1045945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1045945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045945 prefixEnd_1045945 := by exact prefixLift 1045945
  have htrace : WordTrace (prefixWord ++ tailWord_1045945) baseStart_1045945 baseEnd_1045945 := by
    simpa [prefixWord, tailWord_1045945, baseEnd_1045945] using wordTrace_append hprefix tailTrace_1045945
  have hstable : (prefixWord ++ tailWord_1045945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045945).length < 2 ^ (prefixWord ++ tailWord_1045945).sum := by decide
  have hdescent : baseEnd_1045945 < baseStart_1045945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045978 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_1045978 : Nat := 118140960795 + 1045978 * 2 ^ 59
def prefixEnd_1045978 : Nat := 4983230072969 + 3 ^ 40 * 1045978 * 2
def baseEnd_1045978 : Nat := 179029822676204613321547

theorem tailTrace_1045978 : CollatzResearch.WordTrace tailWord_1045978 prefixEnd_1045978 179029822676204613321547 := by
  unfold tailWord_1045978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537487951151954916336647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25433301203071879776897725 9537487951151954916336647)
  ·
    refine ⟨14306231926727932374504971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9537487951151954916336647 14306231926727932374504971)
    ·
      refine ⟨21459347890091898561757457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14306231926727932374504971 21459347890091898561757457)
      ·
        refine ⟨16094510917568923921318093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21459347890091898561757457 16094510917568923921318093)
        ·
          refine ⟨6035441594088346470494285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16094510917568923921318093 6035441594088346470494285)
          ·
            refine ⟨2263290597783129926435357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6035441594088346470494285 2263290597783129926435357)
            ·
              refine ⟨848733974168673722413259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2263290597783129926435357 848733974168673722413259)
              ·
                refine ⟨1273100961253010583619889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848733974168673722413259 1273100961253010583619889)
                ·
                  refine ⟨954825720939757937714917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273100961253010583619889 954825720939757937714917)
                  ·
                    refine ⟨179029822676204613321547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954825720939757937714917 179029822676204613321547)
                    ·
                      rfl

theorem cell23_1045978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_1045978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045978 prefixEnd_1045978 := by exact prefixLift 1045978
  have htrace : WordTrace (prefixWord ++ tailWord_1045978) baseStart_1045978 baseEnd_1045978 := by
    simpa [prefixWord, tailWord_1045978, baseEnd_1045978] using wordTrace_append hprefix tailTrace_1045978
  have hstable : (prefixWord ++ tailWord_1045978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045978).length < 2 ^ (prefixWord ++ tailWord_1045978).sum := by decide
  have hdescent : baseEnd_1045978 < baseStart_1045978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045981 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1045981 : Nat := 118140960795 + 1045981 * 2 ^ 59
def prefixEnd_1045981 : Nat := 4983230072969 + 3 ^ 40 * 1045981 * 2
def baseEnd_1045981 : Nat := 537091008470577328227127

theorem tailTrace_1045981 : CollatzResearch.WordTrace tailWord_1045981 prefixEnd_1045981 537091008470577328227127 := by
  unfold tailWord_1045981
  simp only [CollatzResearch.WordTrace]
  refine ⟨38150061223596951177705797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25433374149064634118470531 38150061223596951177705797)
  ·
    refine ⟨7153136479424428345819837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38150061223596951177705797 7153136479424428345819837)
    ·
      refine ⟨2682426179784160629682439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7153136479424428345819837 2682426179784160629682439)
      ·
        refine ⟨4023639269676240944523659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682426179784160629682439 4023639269676240944523659)
        ·
          refine ⟨6035458904514361416785489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023639269676240944523659 6035458904514361416785489)
          ·
            refine ⟨4526594178385771062589117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035458904514361416785489 4526594178385771062589117)
            ·
              refine ⟨1697472816894664148470919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526594178385771062589117 1697472816894664148470919)
              ·
                refine ⟨2546209225341996222706379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697472816894664148470919 2546209225341996222706379)
                ·
                  refine ⟨3819313838012994334059569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546209225341996222706379 3819313838012994334059569)
                  ·
                    refine ⟨2864485378509745750544677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3819313838012994334059569 2864485378509745750544677)
                    ·
                      refine ⟨537091008470577328227127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2864485378509745750544677 537091008470577328227127)
                      ·
                        rfl

theorem cell23_1045981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1045981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045981 prefixEnd_1045981 := by exact prefixLift 1045981
  have htrace : WordTrace (prefixWord ++ tailWord_1045981) baseStart_1045981 baseEnd_1045981 := by
    simpa [prefixWord, tailWord_1045981, baseEnd_1045981] using wordTrace_append hprefix tailTrace_1045981
  have hstable : (prefixWord ++ tailWord_1045981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045981).length < 2 ^ (prefixWord ++ tailWord_1045981).sum := by decide
  have hdescent : baseEnd_1045981 < baseStart_1045981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045984 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1045984 : Nat := 118140960795 + 1045984 * 2 ^ 59
def prefixEnd_1045984 : Nat := 4983230072969 + 3 ^ 40 * 1045984 * 2
def baseEnd_1045984 : Nat := 537092548912540816489613

theorem tailTrace_1045984 : CollatzResearch.WordTrace tailWord_1045984 prefixEnd_1045984 537092548912540816489613 := by
  unfold tailWord_1045984
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075085321293041345032503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25433447095057388460043337 19075085321293041345032503)
  ·
    refine ⟨28612627981939562017548755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19075085321293041345032503 28612627981939562017548755)
    ·
      refine ⟨42918941972909343026323133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28612627981939562017548755 42918941972909343026323133)
      ·
        refine ⟨16094603239841003634871175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42918941972909343026323133 16094603239841003634871175)
        ·
          refine ⟨24141904859761505452306763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094603239841003634871175 24141904859761505452306763)
          ·
            refine ⟨36212857289642258178460145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24141904859761505452306763 36212857289642258178460145)
            ·
              refine ⟨27159642967231693633845109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36212857289642258178460145 27159642967231693633845109)
              ·
                refine ⟨2546216528177971278172979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27159642967231693633845109 2546216528177971278172979)
                ·
                  refine ⟨3819324792266956917259469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546216528177971278172979 3819324792266956917259469)
                  ·
                    refine ⟨1432246797100108843972301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819324792266956917259469 1432246797100108843972301)
                    ·
                      refine ⟨537092548912540816489613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432246797100108843972301 537092548912540816489613)
                      ·
                        rfl

theorem cell23_1045984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1045984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045984 prefixEnd_1045984 := by exact prefixLift 1045984
  have htrace : WordTrace (prefixWord ++ tailWord_1045984) baseStart_1045984 baseEnd_1045984 := by
    simpa [prefixWord, tailWord_1045984, baseEnd_1045984] using wordTrace_append hprefix tailTrace_1045984
  have hstable : (prefixWord ++ tailWord_1045984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045984).length < 2 ^ (prefixWord ++ tailWord_1045984).sum := by decide
  have hdescent : baseEnd_1045984 < baseStart_1045984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045991 : List Nat := [1, 1, 5, 2, 1, 4, 2, 7]
def baseStart_1045991 : Nat := 118140960795 + 1045991 * 2 ^ 59
def prefixEnd_1045991 : Nat := 4983230072969 + 3 ^ 40 * 1045991 * 2
def baseEnd_1045991 : Nat := 19892449751004529226003

theorem tailTrace_1045991 : CollatzResearch.WordTrace tailWord_1045991 prefixEnd_1045991 19892449751004529226003 := by
  unfold tailWord_1045991
  simp only [CollatzResearch.WordTrace]
  refine ⟨38150425953560722885569827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25433617302373815257046551 38150425953560722885569827)
  ·
    refine ⟨57225638930341084328354741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38150425953560722885569827 57225638930341084328354741)
    ·
      refine ⟨5364903649719476655783257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57225638930341084328354741 5364903649719476655783257)
      ·
        refine ⟨4023677737289607491837443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364903649719476655783257 4023677737289607491837443)
        ·
          refine ⟨6035516605934411237756165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023677737289607491837443 6035516605934411237756165)
          ·
            refine ⟨1131659363612702107079281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6035516605934411237756165 1131659363612702107079281)
            ·
              refine ⟨848744522709526580309461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131659363612702107079281 848744522709526580309461)
              ·
                refine ⟨19892449751004529226003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 848744522709526580309461 19892449751004529226003)
                ·
                  rfl

theorem cell23_1045991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 7].length) (baseStart_1045991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1045991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1045991 prefixEnd_1045991 := by exact prefixLift 1045991
  have htrace : WordTrace (prefixWord ++ tailWord_1045991) baseStart_1045991 baseEnd_1045991 := by
    simpa [prefixWord, tailWord_1045991, baseEnd_1045991] using wordTrace_append hprefix tailTrace_1045991
  have hstable : (prefixWord ++ tailWord_1045991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045991).length < 2 ^ (prefixWord ++ tailWord_1045991).sum := by decide
  have hdescent : baseEnd_1045991 < baseStart_1045991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046001 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_1046001 : Nat := 118140960795 + 1046001 * 2 ^ 59
def prefixEnd_1046001 : Nat := 4983230072969 + 3 ^ 40 * 1046001 * 2
def baseEnd_1046001 : Nat := 537101278083667249977035

theorem tailTrace_1046001 : CollatzResearch.WordTrace tailWord_1046001 prefixEnd_1046001 537101278083667249977035 := by
  unfold tailWord_1046001
  simp only [CollatzResearch.WordTrace]
  refine ⟨38150790683524494593433857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25433860455682996395622571 38150790683524494593433857)
  ·
    refine ⟨28613093012643370945075393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38150790683524494593433857 28613093012643370945075393)
    ·
      refine ⟨21459819759482528208806545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28613093012643370945075393 21459819759482528208806545)
      ·
        refine ⟨16094864819611896156604909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21459819759482528208806545 16094864819611896156604909)
        ·
          refine ⟨6035574307354461058726841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16094864819611896156604909 6035574307354461058726841)
          ·
            refine ⟨4526680730515845794045131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035574307354461058726841 4526680730515845794045131)
            ·
              refine ⟨6790021095773768691067697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526680730515845794045131 6790021095773768691067697)
              ·
                refine ⟨5092515821830326518300773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790021095773768691067697 5092515821830326518300773)
                ·
                  refine ⟨954846716593186222181395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5092515821830326518300773 954846716593186222181395)
                  ·
                    refine ⟨1432270074889779333272093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954846716593186222181395 1432270074889779333272093)
                    ·
                      refine ⟨537101278083667249977035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432270074889779333272093 537101278083667249977035)
                      ·
                        rfl

theorem cell23_1046001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_1046001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046001 prefixEnd_1046001 := by exact prefixLift 1046001
  have htrace : WordTrace (prefixWord ++ tailWord_1046001) baseStart_1046001 baseEnd_1046001 := by
    simpa [prefixWord, tailWord_1046001, baseEnd_1046001] using wordTrace_append hprefix tailTrace_1046001
  have hstable : (prefixWord ++ tailWord_1046001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046001).length < 2 ^ (prefixWord ++ tailWord_1046001).sum := by decide
  have hdescent : baseEnd_1046001 < baseStart_1046001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046002 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1046002 : Nat := 118140960795 + 1046002 * 2 ^ 59
def prefixEnd_1046002 : Nat := 4983230072969 + 3 ^ 40 * 1046002 * 2
def baseEnd_1046002 : Nat := 537101791564321746064531

theorem tailTrace_1046002 : CollatzResearch.WordTrace tailWord_1046002 prefixEnd_1046002 537101791564321746064531 := by
  unfold tailWord_1046002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537706789130217941055065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25433884771013914509480173 9537706789130217941055065)
  ·
    refine ⟨7153280091847663455791299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9537706789130217941055065 7153280091847663455791299)
    ·
      refine ⟨10729920137771495183686949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153280091847663455791299 10729920137771495183686949)
      ·
        refine ⟨2011860025832155346941303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10729920137771495183686949 2011860025832155346941303)
        ·
          refine ⟨3017790038748233020411955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011860025832155346941303 3017790038748233020411955)
          ·
            refine ⟨4526685058122349530617933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017790038748233020411955 4526685058122349530617933)
            ·
              refine ⟨1697506896795881073981725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526685058122349530617933 1697506896795881073981725)
              ·
                refine ⟨636565086298455402743147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697506896795881073981725 636565086298455402743147)
                ·
                  refine ⟨954847629447683104114721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636565086298455402743147 954847629447683104114721)
                  ·
                    refine ⟨716135722085762328086041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954847629447683104114721 716135722085762328086041)
                    ·
                      refine ⟨537101791564321746064531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716135722085762328086041 537101791564321746064531)
                      ·
                        rfl

theorem cell23_1046002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1046002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046002 prefixEnd_1046002 := by exact prefixLift 1046002
  have htrace : WordTrace (prefixWord ++ tailWord_1046002) baseStart_1046002 baseEnd_1046002 := by
    simpa [prefixWord, tailWord_1046002, baseEnd_1046002] using wordTrace_append hprefix tailTrace_1046002
  have hstable : (prefixWord ++ tailWord_1046002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046002).length < 2 ^ (prefixWord ++ tailWord_1046002).sum := by decide
  have hdescent : baseEnd_1046002 < baseStart_1046002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046029 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1046029 : Nat := 118140960795 + 1046029 * 2 ^ 59
def prefixEnd_1046029 : Nat := 4983230072969 + 3 ^ 40 * 1046029 * 2
def baseEnd_1046029 : Nat := 179038551847331046808969

theorem tailTrace_1046029 : CollatzResearch.WordTrace tailWord_1046029 prefixEnd_1046029 179038551847331046808969 := by
  unfold tailWord_1046029
  simp only [CollatzResearch.WordTrace]
  refine ⟨38151811927423055375453141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25434541284948703583635427 38151811927423055375453141)
  ·
    refine ⟨894183092048977860362183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38151811927423055375453141 894183092048977860362183)
    ·
      refine ⟨1341274638073466790543275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894183092048977860362183 1341274638073466790543275)
      ·
        refine ⟨2011911957110200185814913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341274638073466790543275 2011911957110200185814913)
        ·
          refine ⟨1508933967832650139361185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2011911957110200185814913 1508933967832650139361185)
          ·
            refine ⟨1131700475874487604520889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508933967832650139361185 1131700475874487604520889)
            ·
              refine ⟨848775356905865703390667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131700475874487604520889 848775356905865703390667)
              ·
                refine ⟨1273163035358798555086001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848775356905865703390667 1273163035358798555086001)
                ·
                  refine ⟨954872276519098916314501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273163035358798555086001 954872276519098916314501)
                  ·
                    refine ⟨179038551847331046808969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954872276519098916314501 179038551847331046808969)
                    ·
                      rfl

theorem cell23_1046029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1046029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046029 prefixEnd_1046029 := by exact prefixLift 1046029
  have htrace : WordTrace (prefixWord ++ tailWord_1046029) baseStart_1046029 baseEnd_1046029 := by
    simpa [prefixWord, tailWord_1046029, baseEnd_1046029] using wordTrace_append hprefix tailTrace_1046029
  have hstable : (prefixWord ++ tailWord_1046029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046029).length < 2 ^ (prefixWord ++ tailWord_1046029).sum := by decide
  have hdescent : baseEnd_1046029 < baseStart_1046029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046035 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 2, 1, 3]
def baseStart_1046035 : Nat := 118140960795 + 1046035 * 2 ^ 59
def prefixEnd_1046035 : Nat := 4983230072969 + 3 ^ 40 * 1046035 * 2
def baseEnd_1046035 : Nat := 537118736425920116951879

theorem tailTrace_1046035 : CollatzResearch.WordTrace tailWord_1046035 prefixEnd_1046035 537118736425920116951879 := by
  unfold tailWord_1046035
  simp only [CollatzResearch.WordTrace]
  refine ⟨38152030765401318400171559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25434687176934212266781039 38152030765401318400171559)
  ·
    refine ⟨57228046148101977600257339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38152030765401318400171559 57228046148101977600257339)
    ·
      refine ⟨85842069222152966400386009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57228046148101977600257339 85842069222152966400386009)
      ·
        refine ⟨64381551916614724800289507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85842069222152966400386009 64381551916614724800289507)
        ·
          refine ⟨96572327874922087200434261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64381551916614724800289507 96572327874922087200434261)
          ·
            refine ⟨1131706967284243209380089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 96572327874922087200434261 1131706967284243209380089)
            ·
              refine ⟨848780225463182407035067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131706967284243209380089 848780225463182407035067)
              ·
                refine ⟨1273170338194773610552601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848780225463182407035067 1273170338194773610552601)
                ·
                  refine ⟨954877753646080207914451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273170338194773610552601 954877753646080207914451)
                  ·
                    refine ⟨1432316630469120311871677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954877753646080207914451 1432316630469120311871677)
                    ·
                      refine ⟨537118736425920116951879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432316630469120311871677 537118736425920116951879)
                      ·
                        rfl

theorem cell23_1046035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 1, 3].length) (baseStart_1046035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046035 prefixEnd_1046035 := by exact prefixLift 1046035
  have htrace : WordTrace (prefixWord ++ tailWord_1046035) baseStart_1046035 baseEnd_1046035 := by
    simpa [prefixWord, tailWord_1046035, baseEnd_1046035] using wordTrace_append hprefix tailTrace_1046035
  have hstable : (prefixWord ++ tailWord_1046035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046035).length < 2 ^ (prefixWord ++ tailWord_1046035).sum := by decide
  have hdescent : baseEnd_1046035 < baseStart_1046035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046044 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1046044 : Nat := 118140960795 + 1046044 * 2 ^ 59
def prefixEnd_1046044 : Nat := 4983230072969 + 3 ^ 40 * 1046044 * 2
def baseEnd_1046044 : Nat := 537123357751810581739337

theorem tailTrace_1046044 : CollatzResearch.WordTrace tailWord_1046044 prefixEnd_1046044 537123357751810581739337 := by
  unfold tailWord_1046044
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076179511184356468624593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25434906014912475291499457 19076179511184356468624593)
  ·
    refine ⟨14307134633388267351468445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19076179511184356468624593 14307134633388267351468445)
    ·
      refine ⟨5365175487520600256800667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14307134633388267351468445 5365175487520600256800667)
      ·
        refine ⟨8047763231280900385201001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365175487520600256800667 8047763231280900385201001)
        ·
          refine ⟨6035822423460675288900751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8047763231280900385201001 6035822423460675288900751)
          ·
            refine ⟨9053733635191012933351127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035822423460675288900751 9053733635191012933351127)
            ·
              refine ⟨13580600452786519400026691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053733635191012933351127 13580600452786519400026691)
              ·
                refine ⟨20370900679179779100040037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580600452786519400026691 20370900679179779100040037)
                ·
                  refine ⟨3819543877346208581257507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20370900679179779100040037 3819543877346208581257507)
                  ·
                    refine ⟨5729315816019312871886261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3819543877346208581257507 5729315816019312871886261)
                    ·
                      refine ⟨537123357751810581739337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5729315816019312871886261 537123357751810581739337)
                      ·
                        rfl

theorem cell23_1046044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1046044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046044 prefixEnd_1046044 := by exact prefixLift 1046044
  have htrace : WordTrace (prefixWord ++ tailWord_1046044) baseStart_1046044 baseEnd_1046044 := by
    simpa [prefixWord, tailWord_1046044, baseEnd_1046044] using wordTrace_append hprefix tailTrace_1046044
  have hstable : (prefixWord ++ tailWord_1046044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046044).length < 2 ^ (prefixWord ++ tailWord_1046044).sum := by decide
  have hdescent : baseEnd_1046044 < baseStart_1046044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046058 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_1046058 : Nat := 118140960795 + 1046058 * 2 ^ 59
def prefixEnd_1046058 : Nat := 4983230072969 + 3 ^ 40 * 1046058 * 2
def baseEnd_1046058 : Nat := 537130546480973526964273

theorem tailTrace_1046058 : CollatzResearch.WordTrace tailWord_1046058 prefixEnd_1046058 537130546480973526964273 := by
  unfold tailWord_1046058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538217411079498332064707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25435246429545328885505885 9538217411079498332064707)
  ·
    refine ⟨14307326116619247498097061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9538217411079498332064707 14307326116619247498097061)
    ·
      refine ⟨2682623646866108905893199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14307326116619247498097061 2682623646866108905893199)
      ·
        refine ⟨4023935470299163358839799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682623646866108905893199 4023935470299163358839799)
        ·
          refine ⟨6035903205448745038259699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023935470299163358839799 6035903205448745038259699)
          ·
            refine ⟨9053854808173117557389549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035903205448745038259699 9053854808173117557389549)
            ·
              refine ⟨3395195553064919084021081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9053854808173117557389549 3395195553064919084021081)
              ·
                refine ⟨2546396664798689313015811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395195553064919084021081 2546396664798689313015811)
                ·
                  refine ⟨3819594997198033969523717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546396664798689313015811 3819594997198033969523717)
                  ·
                    refine ⟨716174061974631369285697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3819594997198033969523717 716174061974631369285697)
                    ·
                      refine ⟨537130546480973526964273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716174061974631369285697 537130546480973526964273)
                      ·
                        rfl

theorem cell23_1046058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_1046058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046058 prefixEnd_1046058 := by exact prefixLift 1046058
  have htrace : WordTrace (prefixWord ++ tailWord_1046058) baseStart_1046058 baseEnd_1046058 := by
    simpa [prefixWord, tailWord_1046058, baseEnd_1046058] using wordTrace_append hprefix tailTrace_1046058
  have hstable : (prefixWord ++ tailWord_1046058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046058).length < 2 ^ (prefixWord ++ tailWord_1046058).sum := by decide
  have hdescent : baseEnd_1046058 < baseStart_1046058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046062 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1046062 : Nat := 118140960795 + 1046062 * 2 ^ 59
def prefixEnd_1046062 : Nat := 4983230072969 + 3 ^ 40 * 1046062 * 2
def baseEnd_1046062 : Nat := 537132600403591511314255

theorem tailTrace_1046062 : CollatzResearch.WordTrace tailWord_1046062 prefixEnd_1046062 537132600403591511314255 := by
  unfold tailWord_1046062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769126942037937751425555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25435343690869001340936293 4769126942037937751425555)
  ·
    refine ⟨7153690413056906627138333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4769126942037937751425555 7153690413056906627138333)
    ·
      refine ⟨2682633904896339985176875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7153690413056906627138333 2682633904896339985176875)
      ·
        refine ⟨4023950857344509977765313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682633904896339985176875 4023950857344509977765313)
        ·
          refine ⟨3017963143008382483323985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4023950857344509977765313 3017963143008382483323985)
          ·
            refine ⟨2263472357256286862492989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017963143008382483323985 2263472357256286862492989)
            ·
              refine ⟨848802133971107573434871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2263472357256286862492989 848802133971107573434871)
              ·
                refine ⟨1273203200956661360152307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848802133971107573434871 1273203200956661360152307)
                ·
                  refine ⟨1909804801434992040228461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273203200956661360152307 1909804801434992040228461)
                  ·
                    refine ⟨716176800538122015085673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1909804801434992040228461 716176800538122015085673)
                    ·
                      refine ⟨537132600403591511314255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716176800538122015085673 537132600403591511314255)
                      ·
                        rfl

theorem cell23_1046062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1046062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046062 prefixEnd_1046062 := by exact prefixLift 1046062
  have htrace : WordTrace (prefixWord ++ tailWord_1046062) baseStart_1046062 baseEnd_1046062 := by
    simpa [prefixWord, tailWord_1046062, baseEnd_1046062] using wordTrace_append hprefix tailTrace_1046062
  have hstable : (prefixWord ++ tailWord_1046062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046062).length < 2 ^ (prefixWord ++ tailWord_1046062).sum := by decide
  have hdescent : baseEnd_1046062 < baseStart_1046062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046094 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1046094 : Nat := 118140960795 + 1046094 * 2 ^ 59
def prefixEnd_1046094 : Nat := 4983230072969 + 3 ^ 40 * 1046094 * 2
def baseEnd_1046094 : Nat := 179049677261511795371369

theorem tailTrace_1046094 : CollatzResearch.WordTrace tailWord_1046094 prefixEnd_1046094 179049677261511795371369 := by
  unfold tailWord_1046094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769272834023446434571167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25436121781458380984379557 4769272834023446434571167)
  ·
    refine ⟨7153909251035169651856751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4769272834023446434571167 7153909251035169651856751)
    ·
      refine ⟨10730863876552754477785127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153909251035169651856751 10730863876552754477785127)
      ·
        refine ⟨16096295814829131716677691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730863876552754477785127 16096295814829131716677691)
        ·
          refine ⟨24144443722243697575016537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16096295814829131716677691 24144443722243697575016537)
          ·
            refine ⟨18108332791682773181262403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24144443722243697575016537 18108332791682773181262403)
            ·
              refine ⟨27162499187524159771893605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108332791682773181262403 27162499187524159771893605)
              ·
                refine ⟨5092968597660779957230051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27162499187524159771893605 5092968597660779957230051)
                ·
                  refine ⟨7639452896491169935845077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092968597660779957230051 7639452896491169935845077)
                  ·
                    refine ⟨179049677261511795371369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7639452896491169935845077 179049677261511795371369)
                    ·
                      rfl

theorem cell23_1046094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1046094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046094 prefixEnd_1046094 := by exact prefixLift 1046094
  have htrace : WordTrace (prefixWord ++ tailWord_1046094) baseStart_1046094 baseEnd_1046094 := by
    simpa [prefixWord, tailWord_1046094, baseEnd_1046094] using wordTrace_append hprefix tailTrace_1046094
  have hstable : (prefixWord ++ tailWord_1046094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046094).length < 2 ^ (prefixWord ++ tailWord_1046094).sum := by decide
  have hdescent : baseEnd_1046094 < baseStart_1046094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046101 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_1046101 : Nat := 118140960795 + 1046101 * 2 ^ 59
def prefixEnd_1046101 : Nat := 4983230072969 + 3 ^ 40 * 1046101 * 2
def baseEnd_1046101 : Nat := 537152626149116858726575

theorem tailTrace_1046101 : CollatzResearch.WordTrace tailWord_1046101 prefixEnd_1046101 537152626149116858726575 := by
  unfold tailWord_1046101
  simp only [CollatzResearch.WordTrace]
  refine ⟨38154437983162211672074157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25436291988774807781382771 38154437983162211672074157)
  ·
    refine ⟨14307914243685829377027809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38154437983162211672074157 14307914243685829377027809)
    ·
      refine ⟨10730935682764372032770857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307914243685829377027809 10730935682764372032770857)
      ·
        refine ⟨8048201762073279024578143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10730935682764372032770857 8048201762073279024578143)
        ·
          refine ⟨12072302643109918536867215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048201762073279024578143 12072302643109918536867215)
          ·
            refine ⟨18108453964664877805300823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072302643109918536867215 18108453964664877805300823)
            ·
              refine ⟨27162680946997316707951235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108453964664877805300823 27162680946997316707951235)
              ·
                refine ⟨40744021420495975061926853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27162680946997316707951235 40744021420495975061926853)
                ·
                  refine ⟨7639504016342995324111285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40744021420495975061926853 7639504016342995324111285)
                  ·
                    refine ⟨716203501532155811635433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7639504016342995324111285 716203501532155811635433)
                    ·
                      refine ⟨537152626149116858726575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716203501532155811635433 537152626149116858726575)
                      ·
                        rfl

theorem cell23_1046101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_1046101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046101 prefixEnd_1046101 := by exact prefixLift 1046101
  have htrace : WordTrace (prefixWord ++ tailWord_1046101) baseStart_1046101 baseEnd_1046101 := by
    simpa [prefixWord, tailWord_1046101, baseEnd_1046101] using wordTrace_append hprefix tailTrace_1046101
  have hstable : (prefixWord ++ tailWord_1046101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046101).length < 2 ^ (prefixWord ++ tailWord_1046101).sum := by decide
  have hdescent : baseEnd_1046101 < baseStart_1046101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046144 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1046144 : Nat := 118140960795 + 1046144 * 2 ^ 59
def prefixEnd_1046144 : Nat := 4983230072969 + 3 ^ 40 * 1046144 * 2
def baseEnd_1046144 : Nat := 537174705817260190488877

theorem tailTrace_1046144 : CollatzResearch.WordTrace tailWord_1046144 prefixEnd_1046144 537174705817260190488877 := by
  unfold tailWord_1046144
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078003161003215007944743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25437337548004286677259657 19078003161003215007944743)
  ·
    refine ⟨28617004741504822511917115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19078003161003215007944743 28617004741504822511917115)
    ·
      refine ⟨42925507112257233767875673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28617004741504822511917115 42925507112257233767875673)
      ·
        refine ⟨32194130334192925325906755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42925507112257233767875673 32194130334192925325906755)
        ·
          refine ⟨48291195501289387988860133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32194130334192925325906755 48291195501289387988860133)
          ·
            refine ⟨9054599156491760247911275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48291195501289387988860133 9054599156491760247911275)
            ·
              refine ⟨13581898734737640371866913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9054599156491760247911275 13581898734737640371866913)
              ·
                refine ⟨10186424051053230278900185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13581898734737640371866913 10186424051053230278900185)
                ·
                  refine ⟨7639818038289922709175139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10186424051053230278900185 7639818038289922709175139)
                  ·
                    refine ⟨11459727057434884063762709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7639818038289922709175139 11459727057434884063762709)
                    ·
                      refine ⟨537174705817260190488877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11459727057434884063762709 537174705817260190488877)
                      ·
                        rfl

theorem cell23_1046144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1046144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046144 prefixEnd_1046144 := by exact prefixLift 1046144
  have htrace : WordTrace (prefixWord ++ tailWord_1046144) baseStart_1046144 baseEnd_1046144 := by
    simpa [prefixWord, tailWord_1046144, baseEnd_1046144] using wordTrace_append hprefix tailTrace_1046144
  have hstable : (prefixWord ++ tailWord_1046144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046144).length < 2 ^ (prefixWord ++ tailWord_1046144).sum := by decide
  have hdescent : baseEnd_1046144 < baseStart_1046144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046151 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1046151 : Nat := 118140960795 + 1046151 * 2 ^ 59
def prefixEnd_1046151 : Nat := 4983230072969 + 3 ^ 40 * 1046151 * 2
def baseEnd_1046151 : Nat := 537178300181841663101345

theorem tailTrace_1046151 : CollatzResearch.WordTrace tailWord_1046151 prefixEnd_1046151 537178300181841663101345 := by
  unfold tailWord_1046151
  simp only [CollatzResearch.WordTrace]
  refine ⟨38156261632981070211394307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25437507755320713474262871 38156261632981070211394307)
  ·
    refine ⟨57234392449471605317091461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38156261632981070211394307 57234392449471605317091461)
    ·
      refine ⟨10731448584275925996954649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57234392449471605317091461 10731448584275925996954649)
      ·
        refine ⟨8048586438206944497715987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10731448584275925996954649 8048586438206944497715987)
        ·
          refine ⟨12072879657310416746573981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048586438206944497715987 12072879657310416746573981)
          ·
            refine ⟨4527329871491406279965243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12072879657310416746573981 4527329871491406279965243)
            ·
              refine ⟨6790994807237109419947865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527329871491406279965243 6790994807237109419947865)
              ·
                refine ⟨5093246105427832064960899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790994807237109419947865 5093246105427832064960899)
                ·
                  refine ⟨7639869158141748097441349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093246105427832064960899 7639869158141748097441349)
                  ·
                    refine ⟨1432475467151577768270253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639869158141748097441349 1432475467151577768270253)
                    ·
                      refine ⟨537178300181841663101345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432475467151577768270253 537178300181841663101345)
                      ·
                        rfl

theorem cell23_1046151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1046151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046151 prefixEnd_1046151 := by exact prefixLift 1046151
  have htrace : WordTrace (prefixWord ++ tailWord_1046151) baseStart_1046151 baseEnd_1046151 := by
    simpa [prefixWord, tailWord_1046151, baseEnd_1046151] using wordTrace_append hprefix tailTrace_1046151
  have hstable : (prefixWord ++ tailWord_1046151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046151).length < 2 ^ (prefixWord ++ tailWord_1046151).sum := by decide
  have hdescent : baseEnd_1046151 < baseStart_1046151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046158 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1046158 : Nat := 118140960795 + 1046158 * 2 ^ 59
def prefixEnd_1046158 : Nat := 4983230072969 + 3 ^ 40 * 1046158 * 2
def baseEnd_1046158 : Nat := 179060631515474378571271

theorem tailTrace_1046158 : CollatzResearch.WordTrace tailWord_1046158 prefixEnd_1046158 179060631515474378571271 := by
  unfold tailWord_1046158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769564617994463800862391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25437677962637140271266085 4769564617994463800862391)
  ·
    refine ⟨7154346926991695701293587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4769564617994463800862391 7154346926991695701293587)
    ·
      refine ⟨10731520390487543551940381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154346926991695701293587 10731520390487543551940381)
      ·
        refine ⟨4024320146432828831977643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10731520390487543551940381 4024320146432828831977643)
        ·
          refine ⟨6036480219649243247966465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024320146432828831977643 6036480219649243247966465)
          ·
            refine ⟨4527360164736932435974849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036480219649243247966465 4527360164736932435974849)
            ·
              refine ⟨3395520123552699326981137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527360164736932435974849 3395520123552699326981137)
              ·
                refine ⟨2546640092664524495235853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395520123552699326981137 2546640092664524495235853)
                ·
                  refine ⟨954990034749196685713445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2546640092664524495235853 954990034749196685713445)
                  ·
                    refine ⟨179060631515474378571271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 954990034749196685713445 179060631515474378571271)
                    ·
                      rfl

theorem cell23_1046158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1046158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046158 prefixEnd_1046158 := by exact prefixLift 1046158
  have htrace : WordTrace (prefixWord ++ tailWord_1046158) baseStart_1046158 baseEnd_1046158 := by
    simpa [prefixWord, tailWord_1046158, baseEnd_1046158] using wordTrace_append hprefix tailTrace_1046158
  have hstable : (prefixWord ++ tailWord_1046158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046158).length < 2 ^ (prefixWord ++ tailWord_1046158).sum := by decide
  have hdescent : baseEnd_1046158 < baseStart_1046158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046208 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2]
def baseStart_1046208 : Nat := 118140960795 + 1046208 * 2 ^ 59
def prefixEnd_1046208 : Nat := 4983230072969 + 3 ^ 40 * 1046208 * 2
def baseEnd_1046208 : Nat := 537207568579147940088583

theorem tailTrace_1046208 : CollatzResearch.WordTrace tailWord_1046208 prefixEnd_1046208 537207568579147940088583 := by
  unfold tailWord_1046208
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079170296887284473109639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25438893729183045964146185 19079170296887284473109639)
  ·
    refine ⟨28618755445330926709664459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19079170296887284473109639 28618755445330926709664459)
    ·
      refine ⟨42928133167996390064496689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28618755445330926709664459 42928133167996390064496689)
      ·
        refine ⟨32196099875997292548372517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42928133167996390064496689 32196099875997292548372517)
        ·
          refine ⟨6036768726749492352819847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32196099875997292548372517 6036768726749492352819847)
          ·
            refine ⟨9055153090124238529229771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036768726749492352819847 9055153090124238529229771)
            ·
              refine ⟨13582729635186357793844657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055153090124238529229771 13582729635186357793844657)
              ·
                refine ⟨10187047226389768345383493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13582729635186357793844657 10187047226389768345383493)
                ·
                  refine ⟨1910071354948081564759405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10187047226389768345383493 1910071354948081564759405)
                  ·
                    refine ⟨716276758105530586784777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910071354948081564759405 716276758105530586784777)
                    ·
                      refine ⟨537207568579147940088583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716276758105530586784777 537207568579147940088583)
                      ·
                        rfl

theorem cell23_1046208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_1046208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046208 prefixEnd_1046208 := by exact prefixLift 1046208
  have htrace : WordTrace (prefixWord ++ tailWord_1046208) baseStart_1046208 baseEnd_1046208 := by
    simpa [prefixWord, tailWord_1046208, baseEnd_1046208] using wordTrace_append hprefix tailTrace_1046208
  have hstable : (prefixWord ++ tailWord_1046208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046208).length < 2 ^ (prefixWord ++ tailWord_1046208).sum := by decide
  have hdescent : baseEnd_1046208 < baseStart_1046208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046218 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_1046218 : Nat := 118140960795 + 1046218 * 2 ^ 59
def prefixEnd_1046218 : Nat := 4983230072969 + 3 ^ 40 * 1046218 * 2
def baseEnd_1046218 : Nat := 179070901128564300321179

theorem tailTrace_1046218 : CollatzResearch.WordTrace tailWord_1046218 prefixEnd_1046218 179070901128564300321179 := by
  unfold tailWord_1046218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539676330934585163520827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25439136882492227102722205 9539676330934585163520827)
  ·
    refine ⟨14309514496401877745281241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9539676330934585163520827 14309514496401877745281241)
    ·
      refine ⟨10732135872301408308960931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14309514496401877745281241 10732135872301408308960931)
      ·
        refine ⟨16098203808452112463441397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732135872301408308960931 16098203808452112463441397)
        ·
          refine ⟨1509206607042385543447631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16098203808452112463441397 1509206607042385543447631)
          ·
            refine ⟨2263809910563578315171447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509206607042385543447631 2263809910563578315171447)
            ·
              refine ⟨3395714865845367472757171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263809910563578315171447 3395714865845367472757171)
              ·
                refine ⟨5093572298768051209135757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395714865845367472757171 5093572298768051209135757)
                ·
                  refine ⟨1910089612038019203425909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5093572298768051209135757 1910089612038019203425909)
                  ·
                    refine ⟨179070901128564300321179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1910089612038019203425909 179070901128564300321179)
                    ·
                      rfl

theorem cell23_1046218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_1046218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046218 prefixEnd_1046218 := by exact prefixLift 1046218
  have htrace : WordTrace (prefixWord ++ tailWord_1046218) baseStart_1046218 baseEnd_1046218 := by
    simpa [prefixWord, tailWord_1046218, baseEnd_1046218] using wordTrace_append hprefix tailTrace_1046218
  have hstable : (prefixWord ++ tailWord_1046218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046218).length < 2 ^ (prefixWord ++ tailWord_1046218).sum := by decide
  have hdescent : baseEnd_1046218 < baseStart_1046218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046225 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_1046225 : Nat := 118140960795 + 1046225 * 2 ^ 59
def prefixEnd_1046225 : Nat := 4983230072969 + 3 ^ 40 * 1046225 * 2
def baseEnd_1046225 : Nat := 537216297750274373576005

theorem tailTrace_1046225 : CollatzResearch.WordTrace tailWord_1046225 prefixEnd_1046225 537216297750274373576005 := by
  unfold tailWord_1046225
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158960634712980849588129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25439307089808653899725419 38158960634712980849588129)
  ·
    refine ⟨28619220476034735637191097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38158960634712980849588129 28619220476034735637191097)
    ·
      refine ⟨21464415357026051727893323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28619220476034735637191097 21464415357026051727893323)
      ·
        refine ⟨32196623035539077591839985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21464415357026051727893323 32196623035539077591839985)
        ·
          refine ⟨24147467276654308193879989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32196623035539077591839985 24147467276654308193879989)
          ·
            refine ⟨2263825057186341393176249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24147467276654308193879989 2263825057186341393176249)
            ·
              refine ⟨1697868792889756044882187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263825057186341393176249 1697868792889756044882187)
              ·
                refine ⟨2546803189334634067323281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697868792889756044882187 2546803189334634067323281)
                ·
                  refine ⟨1910102392000975550492461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2546803189334634067323281 1910102392000975550492461)
                  ·
                    refine ⟨716288397000365831434673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910102392000975550492461 716288397000365831434673)
                    ·
                      refine ⟨537216297750274373576005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716288397000365831434673 537216297750274373576005)
                      ·
                        rfl

theorem cell23_1046225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_1046225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046225 prefixEnd_1046225 := by exact prefixLift 1046225
  have htrace : WordTrace (prefixWord ++ tailWord_1046225) baseStart_1046225 baseEnd_1046225 := by
    simpa [prefixWord, tailWord_1046225, baseEnd_1046225] using wordTrace_append hprefix tailTrace_1046225
  have hstable : (prefixWord ++ tailWord_1046225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046225).length < 2 ^ (prefixWord ++ tailWord_1046225).sum := by decide
  have hdescent : baseEnd_1046225 < baseStart_1046225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046231 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 1, 6]
def baseStart_1046231 : Nat := 118140960795 + 1046231 * 2 ^ 59
def prefixEnd_1046231 : Nat := 4983230072969 + 3 ^ 40 * 1046231 * 2
def baseEnd_1046231 : Nat := 179073126211400450033659

theorem tailTrace_1046231 : CollatzResearch.WordTrace tailWord_1046231 prefixEnd_1046231 179073126211400450033659 := by
  unfold tailWord_1046231
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159179472691243874306547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25439452981794162582871031 38159179472691243874306547)
  ·
    refine ⟨57238769209036865811459821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38159179472691243874306547 57238769209036865811459821)
    ·
      refine ⟨21464538453388824679297433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57238769209036865811459821 21464538453388824679297433)
      ·
        refine ⟨16098403840041618509473075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21464538453388824679297433 16098403840041618509473075)
        ·
          refine ⟨24147605760062427764209613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098403840041618509473075 24147605760062427764209613)
          ·
            refine ⟨9055352160023410411578605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24147605760062427764209613 9055352160023410411578605)
            ·
              refine ⟨3395757060008778904341977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9055352160023410411578605 3395757060008778904341977)
              ·
                refine ⟨2546817795006584178256483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395757060008778904341977 2546817795006584178256483)
                ·
                  refine ⟨3820226692509876267384725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546817795006584178256483 3820226692509876267384725)
                  ·
                    refine ⟨179073126211400450033659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3820226692509876267384725 179073126211400450033659)
                    ·
                      rfl

theorem cell23_1046231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_1046231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046231 prefixEnd_1046231 := by exact prefixLift 1046231
  have htrace : WordTrace (prefixWord ++ tailWord_1046231) baseStart_1046231 baseEnd_1046231 := by
    simpa [prefixWord, tailWord_1046231, baseEnd_1046231] using wordTrace_append hprefix tailTrace_1046231
  have hstable : (prefixWord ++ tailWord_1046231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046231).length < 2 ^ (prefixWord ++ tailWord_1046231).sum := by decide
  have hdescent : baseEnd_1046231 < baseStart_1046231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046255 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 3, 2, 2]
def baseStart_1046255 : Nat := 118140960795 + 1046255 * 2 ^ 59
def prefixEnd_1046255 : Nat := 4983230072969 + 3 ^ 40 * 1046255 * 2
def baseEnd_1046255 : Nat := 537231702169909256200867

theorem tailTrace_1046255 : CollatzResearch.WordTrace tailWord_1046255 prefixEnd_1046255 537231702169909256200867 := by
  unfold tailWord_1046255
  simp only [CollatzResearch.WordTrace]
  refine ⟨38160054824604295973180219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25440036549736197315453479 38160054824604295973180219)
  ·
    refine ⟨57240082236906443959770329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38160054824604295973180219 57240082236906443959770329)
    ·
      refine ⟨42930061677679832969827747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57240082236906443959770329 42930061677679832969827747)
      ·
        refine ⟨64395092516519749454741621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42930061677679832969827747 64395092516519749454741621)
        ·
          refine ⟨6037039923423726511382027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64395092516519749454741621 6037039923423726511382027)
          ·
            refine ⟨9055559885135589767073041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037039923423726511382027 9055559885135589767073041)
            ·
              refine ⟨6791669913851692325304781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9055559885135589767073041 6791669913851692325304781)
              ·
                refine ⟨2546876217694384621989293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791669913851692325304781 2546876217694384621989293)
                ·
                  refine ⟨955078581635394233245985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2546876217694384621989293 955078581635394233245985)
                  ·
                    refine ⟨716308936226545674934489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955078581635394233245985 716308936226545674934489)
                    ·
                      refine ⟨537231702169909256200867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716308936226545674934489 537231702169909256200867)
                      ·
                        rfl

theorem cell23_1046255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 2, 2].length) (baseStart_1046255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046255 prefixEnd_1046255 := by exact prefixLift 1046255
  have htrace : WordTrace (prefixWord ++ tailWord_1046255) baseStart_1046255 baseEnd_1046255 := by
    simpa [prefixWord, tailWord_1046255, baseEnd_1046255] using wordTrace_append hprefix tailTrace_1046255
  have hstable : (prefixWord ++ tailWord_1046255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046255).length < 2 ^ (prefixWord ++ tailWord_1046255).sum := by decide
  have hdescent : baseEnd_1046255 < baseStart_1046255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046258 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1046258 : Nat := 118140960795 + 1046258 * 2 ^ 59
def prefixEnd_1046258 : Nat := 4983230072969 + 3 ^ 40 * 1046258 * 2
def baseEnd_1046258 : Nat := 537233242611872744463353

theorem tailTrace_1046258 : CollatzResearch.WordTrace tailWord_1046258 prefixEnd_1046258 537233242611872744463353 := by
  unfold tailWord_1046258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540041060898356871384857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25440109495728951657026285 9540041060898356871384857)
  ·
    refine ⟨7155030795673767653538643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9540041060898356871384857 7155030795673767653538643)
    ·
      refine ⟨10732546193510651480307965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155030795673767653538643 10732546193510651480307965)
      ·
        refine ⟨4024704822566494305115487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10732546193510651480307965 4024704822566494305115487)
        ·
          refine ⟨6037057233849741457673231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024704822566494305115487 6037057233849741457673231)
          ·
            refine ⟨9055585850774612186509847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037057233849741457673231 9055585850774612186509847)
            ·
              refine ⟨13583378776161918279764771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055585850774612186509847 13583378776161918279764771)
              ·
                refine ⟨20375068164242877419647157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583378776161918279764771 20375068164242877419647157)
                ·
                  refine ⟨1910162640397769758091921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20375068164242877419647157 1910162640397769758091921)
                  ·
                    refine ⟨1432621980298327318568941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1910162640397769758091921 1432621980298327318568941)
                    ·
                      refine ⟨537233242611872744463353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432621980298327318568941 537233242611872744463353)
                      ·
                        rfl

theorem cell23_1046258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1046258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046258 prefixEnd_1046258 := by exact prefixLift 1046258
  have htrace : WordTrace (prefixWord ++ tailWord_1046258) baseStart_1046258 baseEnd_1046258 := by
    simpa [prefixWord, tailWord_1046258, baseEnd_1046258] using wordTrace_append hprefix tailTrace_1046258
  have hstable : (prefixWord ++ tailWord_1046258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046258).length < 2 ^ (prefixWord ++ tailWord_1046258).sum := by decide
  have hdescent : baseEnd_1046258 < baseStart_1046258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046268 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_1046268 : Nat := 118140960795 + 1046268 * 2 ^ 59
def prefixEnd_1046268 : Nat := 4983230072969 + 3 ^ 40 * 1046268 * 2
def baseEnd_1046268 : Nat := 537238377418417705338307

theorem tailTrace_1046268 : CollatzResearch.WordTrace tailWord_1046268 prefixEnd_1046268 537238377418417705338307 := by
  unfold tailWord_1046268
  simp only [CollatzResearch.WordTrace]
  refine ⟨19080264486778599596701729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25440352649038132795602305 19080264486778599596701729)
  ·
    refine ⟨14310198365083949697526297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19080264486778599596701729 14310198365083949697526297)
    ·
      refine ⟨10732648773812962273144723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14310198365083949697526297 10732648773812962273144723)
      ·
        refine ⟨16098973160719443409717085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732648773812962273144723 16098973160719443409717085)
        ·
          refine ⟨6037114935269791278643907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16098973160719443409717085 6037114935269791278643907)
          ·
            refine ⟨9055672402904686917965861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037114935269791278643907 9055672402904686917965861)
            ·
              refine ⟨1697938575544628797118599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9055672402904686917965861 1697938575544628797118599)
              ·
                refine ⟨2546907863316943195677899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697938575544628797118599 2546907863316943195677899)
                ·
                  refine ⟨3820361794975414793516849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546907863316943195677899 3820361794975414793516849)
                  ·
                    refine ⟨2865271346231561095137637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3820361794975414793516849 2865271346231561095137637)
                    ·
                      refine ⟨537238377418417705338307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2865271346231561095137637 537238377418417705338307)
                      ·
                        rfl

theorem cell23_1046268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_1046268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046268 prefixEnd_1046268 := by exact prefixLift 1046268
  have htrace : WordTrace (prefixWord ++ tailWord_1046268) baseStart_1046268 baseEnd_1046268 := by
    simpa [prefixWord, tailWord_1046268, baseEnd_1046268] using wordTrace_append hprefix tailTrace_1046268
  have hstable : (prefixWord ++ tailWord_1046268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046268).length < 2 ^ (prefixWord ++ tailWord_1046268).sum := by decide
  have hdescent : baseEnd_1046268 < baseStart_1046268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046305 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1046305 : Nat := 118140960795 + 1046305 * 2 ^ 59
def prefixEnd_1046305 : Nat := 4983230072969 + 3 ^ 40 * 1046305 * 2
def baseEnd_1046305 : Nat := 537257376202634060575637

theorem tailTrace_1046305 : CollatzResearch.WordTrace tailWord_1046305 prefixEnd_1046305 537257376202634060575637 := by
  unfold tailWord_1046305
  simp only [CollatzResearch.WordTrace]
  refine ⟨38161878474423154512500369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25441252316282103008333579 38161878474423154512500369)
  ·
    refine ⟨28621408855817365884375277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38161878474423154512500369 28621408855817365884375277)
    ·
      refine ⟨10733028320931512206640729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28621408855817365884375277 10733028320931512206640729)
      ·
        refine ⟨8049771240698634154980547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10733028320931512206640729 8049771240698634154980547)
        ·
          refine ⟨12074656861047951232470821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049771240698634154980547 12074656861047951232470821)
          ·
            refine ⟨2263998161446490856088279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12074656861047951232470821 2263998161446490856088279)
            ·
              refine ⟨3395997242169736284132419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263998161446490856088279 3395997242169736284132419)
              ·
                refine ⟨5093995863254604426198629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395997242169736284132419 5093995863254604426198629)
                ·
                  refine ⟨955124224360238329912243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5093995863254604426198629 955124224360238329912243)
                  ·
                    refine ⟨1432686336540357494868365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 955124224360238329912243 1432686336540357494868365)
                    ·
                      refine ⟨537257376202634060575637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1432686336540357494868365 537257376202634060575637)
                      ·
                        rfl

theorem cell23_1046305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1046305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046305 prefixEnd_1046305 := by exact prefixLift 1046305
  have htrace : WordTrace (prefixWord ++ tailWord_1046305) baseStart_1046305 baseEnd_1046305 := by
    simpa [prefixWord, tailWord_1046305, baseEnd_1046305] using wordTrace_append hprefix tailTrace_1046305
  have hstable : (prefixWord ++ tailWord_1046305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046305).length < 2 ^ (prefixWord ++ tailWord_1046305).sum := by decide
  have hdescent : baseEnd_1046305 < baseStart_1046305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046345 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 6, 2, 2]
def baseStart_1046345 : Nat := 118140960795 + 1046345 * 2 ^ 59
def prefixEnd_1046345 : Nat := 4983230072969 + 3 ^ 40 * 1046345 * 2
def baseEnd_1046345 : Nat := 537277915428813904075453

theorem tailTrace_1046345 : CollatzResearch.WordTrace tailWord_1046345 prefixEnd_1046345 537277915428813904075453 := by
  unfold tailWord_1046345
  simp only [CollatzResearch.WordTrace]
  refine ⟨38163337394278241343956489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25442224929518827562637659 38163337394278241343956489)
  ·
    refine ⟨28622503045708681007967367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38163337394278241343956489 28622503045708681007967367)
    ·
      refine ⟨42933754568563021511951051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28622503045708681007967367 42933754568563021511951051)
      ·
        refine ⟨64400631852844532267926577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42933754568563021511951051 64400631852844532267926577)
        ·
          refine ⟨48300473889633399200944933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64400631852844532267926577 48300473889633399200944933)
          ·
            refine ⟨9056338854306262350177175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48300473889633399200944933 9056338854306262350177175)
            ·
              refine ⟨13584508281459393525265763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056338854306262350177175 13584508281459393525265763)
              ·
                refine ⟨20376762422189090287898645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13584508281459393525265763 20376762422189090287898645)
                ·
                  refine ⟨955160738540113607245249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20376762422189090287898645 955160738540113607245249)
                  ·
                    refine ⟨716370553905085205433937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955160738540113607245249 716370553905085205433937)
                    ·
                      refine ⟨537277915428813904075453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716370553905085205433937 537277915428813904075453)
                      ·
                        rfl

theorem cell23_1046345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 2, 2].length) (baseStart_1046345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046345 prefixEnd_1046345 := by exact prefixLift 1046345
  have htrace : WordTrace (prefixWord ++ tailWord_1046345) baseStart_1046345 baseEnd_1046345 := by
    simpa [prefixWord, tailWord_1046345, baseEnd_1046345] using wordTrace_append hprefix tailTrace_1046345
  have hstable : (prefixWord ++ tailWord_1046345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046345).length < 2 ^ (prefixWord ++ tailWord_1046345).sum := by decide
  have hdescent : baseEnd_1046345 < baseStart_1046345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046349 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1046349 : Nat := 118140960795 + 1046349 * 2 ^ 59
def prefixEnd_1046349 : Nat := 4983230072969 + 3 ^ 40 * 1046349 * 2
def baseEnd_1046349 : Nat := 537279969351431888425435

theorem tailTrace_1046349 : CollatzResearch.WordTrace tailWord_1046349 prefixEnd_1046349 537279969351431888425435 := by
  unfold tailWord_1046349
  simp only [CollatzResearch.WordTrace]
  refine ⟨38163483286263750027102101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25442322190842500018068067 38163483286263750027102101)
  ·
    refine ⟨1788913279043613282520411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38163483286263750027102101 1788913279043613282520411)
    ·
      refine ⟨2683369918565419923780617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788913279043613282520411 2683369918565419923780617)
      ·
        refine ⟨2012527438924064942835463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683369918565419923780617 2012527438924064942835463)
        ·
          refine ⟨3018791158386097414253195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012527438924064942835463 3018791158386097414253195)
          ·
            refine ⟨4528186737579146121379793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018791158386097414253195 4528186737579146121379793)
            ·
              refine ⟨3396140053184359591034845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528186737579146121379793 3396140053184359591034845)
              ·
                refine ⟨1273552519944134846638067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396140053184359591034845 1273552519944134846638067)
                ·
                  refine ⟨1910328779916202269957101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273552519944134846638067 1910328779916202269957101)
                  ·
                    refine ⟨716373292468575851233913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910328779916202269957101 716373292468575851233913)
                    ·
                      refine ⟨537279969351431888425435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716373292468575851233913 537279969351431888425435)
                      ·
                        rfl

theorem cell23_1046349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1046349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046349 prefixEnd_1046349 := by exact prefixLift 1046349
  have htrace : WordTrace (prefixWord ++ tailWord_1046349) baseStart_1046349 baseEnd_1046349 := by
    simpa [prefixWord, tailWord_1046349, baseEnd_1046349] using wordTrace_append hprefix tailTrace_1046349
  have hstable : (prefixWord ++ tailWord_1046349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046349).length < 2 ^ (prefixWord ++ tailWord_1046349).sum := by decide
  have hdescent : baseEnd_1046349 < baseStart_1046349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046361 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_1046361 : Nat := 118140960795 + 1046361 * 2 ^ 59
def prefixEnd_1046361 : Nat := 4983230072969 + 3 ^ 40 * 1046361 * 2
def baseEnd_1046361 : Nat := 537286131119285841475379

theorem tailTrace_1046361 : CollatzResearch.WordTrace tailWord_1046361 prefixEnd_1046361 537286131119285841475379 := by
  unfold tailWord_1046361
  simp only [CollatzResearch.WordTrace]
  refine ⟨38163920962220276076538937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25442613974813517384359291 38163920962220276076538937)
  ·
    refine ⟨28622940721665207057404203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38163920962220276076538937 28622940721665207057404203)
    ·
      refine ⟨42934411082497810586106305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28622940721665207057404203 42934411082497810586106305)
      ·
        refine ⟨32200808311873357939579729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42934411082497810586106305 32200808311873357939579729)
        ·
          refine ⟨24150606233905018454684797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32200808311873357939579729 24150606233905018454684797)
          ·
            refine ⟨9056477337714381920506799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24150606233905018454684797 9056477337714381920506799)
            ·
              refine ⟨13584716006571572880760199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056477337714381920506799 13584716006571572880760199)
              ·
                refine ⟨20377074009857359321140299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13584716006571572880760199 20377074009857359321140299)
                ·
                  refine ⟨30565611014786038981710449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20377074009857359321140299 30565611014786038981710449)
                  ·
                    refine ⟨22924208261089529236282837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30565611014786038981710449 22924208261089529236282837)
                    ·
                      refine ⟨537286131119285841475379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 22924208261089529236282837 537286131119285841475379)
                      ·
                        rfl

theorem cell23_1046361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_1046361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046361 prefixEnd_1046361 := by exact prefixLift 1046361
  have htrace : WordTrace (prefixWord ++ tailWord_1046361) baseStart_1046361 baseEnd_1046361 := by
    simpa [prefixWord, tailWord_1046361, baseEnd_1046361] using wordTrace_append hprefix tailTrace_1046361
  have hstable : (prefixWord ++ tailWord_1046361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046361).length < 2 ^ (prefixWord ++ tailWord_1046361).sum := by decide
  have hdescent : baseEnd_1046361 < baseStart_1046361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046362 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_1046362 : Nat := 118140960795 + 1046362 * 2 ^ 59
def prefixEnd_1046362 : Nat := 4983230072969 + 3 ^ 40 * 1046362 * 2
def baseEnd_1046362 : Nat := 537286644599940337562875

theorem tailTrace_1046362 : CollatzResearch.WordTrace tailWord_1046362 prefixEnd_1046362 537286644599940337562875 := by
  unfold tailWord_1046362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540989358804163311831335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25442638290144435498216893 9540989358804163311831335)
  ·
    refine ⟨14311484038206244967747003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9540989358804163311831335 14311484038206244967747003)
    ·
      refine ⟨21467226057309367451620505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14311484038206244967747003 21467226057309367451620505)
      ·
        refine ⟨16100419542982025588715379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21467226057309367451620505 16100419542982025588715379)
        ·
          refine ⟨24150629314473038383073069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100419542982025588715379 24150629314473038383073069)
          ·
            refine ⟨9056485992927389393652401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24150629314473038383073069 9056485992927389393652401)
            ·
              refine ⟨6792364494695542045239301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056485992927389393652401 6792364494695542045239301)
              ·
                refine ⟨1273568342755414133482369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6792364494695542045239301 1273568342755414133482369)
                ·
                  refine ⟨955176257066560600111777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273568342755414133482369 955176257066560600111777)
                  ·
                    refine ⟨716382192799920450083833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955176257066560600111777 716382192799920450083833)
                    ·
                      refine ⟨537286644599940337562875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716382192799920450083833 537286644599940337562875)
                      ·
                        rfl

theorem cell23_1046362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_1046362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046362 prefixEnd_1046362 := by exact prefixLift 1046362
  have htrace : WordTrace (prefixWord ++ tailWord_1046362) baseStart_1046362 baseEnd_1046362 := by
    simpa [prefixWord, tailWord_1046362, baseEnd_1046362] using wordTrace_append hprefix tailTrace_1046362
  have hstable : (prefixWord ++ tailWord_1046362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046362).length < 2 ^ (prefixWord ++ tailWord_1046362).sum := by decide
  have hdescent : baseEnd_1046362 < baseStart_1046362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046368 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 7]
def baseStart_1046368 : Nat := 118140960795 + 1046368 * 2 ^ 59
def prefixEnd_1046368 : Nat := 4983230072969 + 3 ^ 40 * 1046368 * 2
def baseEnd_1046368 : Nat := 59698858387096368231983

theorem tailTrace_1046368 : CollatzResearch.WordTrace tailWord_1046368 prefixEnd_1046368 59698858387096368231983 := by
  unfold tailWord_1046368
  simp only [CollatzResearch.WordTrace]
  refine ⟨19082088136597458136021879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25442784182129944181362505 19082088136597458136021879)
  ·
    refine ⟨28623132204896187204032819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19082088136597458136021879 28623132204896187204032819)
    ·
      refine ⟨42934698307344280806049229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28623132204896187204032819 42934698307344280806049229)
      ·
        refine ⟨16100511865254105302268461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42934698307344280806049229 16100511865254105302268461)
        ·
          refine ⟨6037691949470289488350673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16100511865254105302268461 6037691949470289488350673)
          ·
            refine ⟨4528268962102717116263005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6037691949470289488350673 4528268962102717116263005)
            ·
              refine ⟨1698100860788518918598627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4528268962102717116263005 1698100860788518918598627)
              ·
                refine ⟨2547151291182778377897941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698100860788518918598627 2547151291182778377897941)
                ·
                  refine ⟨59698858387096368231983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2547151291182778377897941 59698858387096368231983)
                  ·
                    rfl

theorem cell23_1046368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_1046368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046368 prefixEnd_1046368 := by exact prefixLift 1046368
  have htrace : WordTrace (prefixWord ++ tailWord_1046368) baseStart_1046368 baseEnd_1046368 := by
    simpa [prefixWord, tailWord_1046368, baseEnd_1046368] using wordTrace_append hprefix tailTrace_1046368
  have hstable : (prefixWord ++ tailWord_1046368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046368).length < 2 ^ (prefixWord ++ tailWord_1046368).sum := by decide
  have hdescent : baseEnd_1046368 < baseStart_1046368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046478 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1046478 : Nat := 118140960795 + 1046478 * 2 ^ 59
def prefixEnd_1046478 : Nat := 4983230072969 + 3 ^ 40 * 1046478 * 2
def baseEnd_1046478 : Nat := 537346208355861883712341

theorem tailTrace_1046478 : CollatzResearch.WordTrace tailWord_1046478 prefixEnd_1046478 537346208355861883712341 := by
  unfold tailWord_1046478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771023537849550632318511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25445458868530936705698725 4771023537849550632318511)
  ·
    refine ⟨7156535306774325948477767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4771023537849550632318511 7156535306774325948477767)
    ·
      refine ⟨10734802960161488922716651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7156535306774325948477767 10734802960161488922716651)
      ·
        refine ⟨16102204440242233384074977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10734802960161488922716651 16102204440242233384074977)
        ·
          refine ⟨12076653330181675038056233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16102204440242233384074977 12076653330181675038056233)
          ·
            refine ⟨9057489997636256278542175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12076653330181675038056233 9057489997636256278542175)
            ·
              refine ⟨13586234996454384417813263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057489997636256278542175 13586234996454384417813263)
              ·
                refine ⟨20379352494681576626719895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13586234996454384417813263 20379352494681576626719895)
                ·
                  refine ⟨30569028742022364940079843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20379352494681576626719895 30569028742022364940079843)
                  ·
                    refine ⟨45853543113033547410119765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30569028742022364940079843 45853543113033547410119765)
                    ·
                      refine ⟨537346208355861883712341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 45853543113033547410119765 537346208355861883712341)
                      ·
                        rfl

theorem cell23_1046478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1046478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046478 prefixEnd_1046478 := by exact prefixLift 1046478
  have htrace : WordTrace (prefixWord ++ tailWord_1046478) baseStart_1046478 baseEnd_1046478 := by
    simpa [prefixWord, tailWord_1046478, baseEnd_1046478] using wordTrace_append hprefix tailTrace_1046478
  have hstable : (prefixWord ++ tailWord_1046478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046478).length < 2 ^ (prefixWord ++ tailWord_1046478).sum := by decide
  have hdescent : baseEnd_1046478 < baseStart_1046478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046508 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_1046508 : Nat := 118140960795 + 1046508 * 2 ^ 59
def prefixEnd_1046508 : Nat := 4983230072969 + 3 ^ 40 * 1046508 * 2
def baseEnd_1046508 : Nat := 537361612775496766337203

theorem tailTrace_1046508 : CollatzResearch.WordTrace tailWord_1046508 prefixEnd_1046508 537361612775496766337203 := by
  unfold tailWord_1046508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084641246343860091070089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25446188328458480121426785 19084641246343860091070089)
  ·
    refine ⟨14313480934757895068302567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19084641246343860091070089 14313480934757895068302567)
    ·
      refine ⟨21470221402136842602453851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14313480934757895068302567 21470221402136842602453851)
      ·
        refine ⟨32205332103205263903680777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21470221402136842602453851 32205332103205263903680777)
        ·
          refine ⟨24153999077403947927760583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32205332103205263903680777 24153999077403947927760583)
          ·
            refine ⟨36230998616105921891640875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24153999077403947927760583 36230998616105921891640875)
            ·
              refine ⟨54346497924158882837461313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36230998616105921891640875 54346497924158882837461313)
              ·
                refine ⟨40759873443119162128095985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54346497924158882837461313 40759873443119162128095985)
                ·
                  refine ⟨30569905082339371596071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40759873443119162128095985 30569905082339371596071989)
                  ·
                    refine ⟨2865928601469316087131749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30569905082339371596071989 2865928601469316087131749)
                    ·
                      refine ⟨537361612775496766337203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2865928601469316087131749 537361612775496766337203)
                      ·
                        rfl

theorem cell23_1046508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_1046508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046508 prefixEnd_1046508 := by exact prefixLift 1046508
  have htrace : WordTrace (prefixWord ++ tailWord_1046508) baseStart_1046508 baseEnd_1046508 := by
    simpa [prefixWord, tailWord_1046508, baseEnd_1046508] using wordTrace_append hprefix tailTrace_1046508
  have hstable : (prefixWord ++ tailWord_1046508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046508).length < 2 ^ (prefixWord ++ tailWord_1046508).sum := by decide
  have hdescent : baseEnd_1046508 < baseStart_1046508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046536 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_1046536 : Nat := 118140960795 + 1046536 * 2 ^ 59
def prefixEnd_1046536 : Nat := 4983230072969 + 3 ^ 40 * 1046536 * 2
def baseEnd_1046536 : Nat := 537375990233822656787075

theorem tailTrace_1046536 : CollatzResearch.WordTrace tailWord_1046536 prefixEnd_1046536 537375990233822656787075 := by
  unfold tailWord_1046536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085151868293140482079731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25446869157724187309439641 19085151868293140482079731)
  ·
    refine ⟨28627727802439710723119597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19085151868293140482079731 28627727802439710723119597)
    ·
      refine ⟨10735397925914891521169849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28627727802439710723119597 10735397925914891521169849)
      ·
        refine ⟨8051548444436168640877387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10735397925914891521169849 8051548444436168640877387)
        ·
          refine ⟨12077322666654252961316081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051548444436168640877387 12077322666654252961316081)
          ·
            refine ⟨9057991999990689720987061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12077322666654252961316081 9057991999990689720987061)
            ·
              refine ⟨849186749999127161342537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9057991999990689720987061 849186749999127161342537)
              ·
                refine ⟨636890062499345371006903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849186749999127161342537 636890062499345371006903)
                ·
                  refine ⟨955335093749018056510355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636890062499345371006903 955335093749018056510355)
                  ·
                    refine ⟨1433002640623527084765533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 955335093749018056510355 1433002640623527084765533)
                    ·
                      refine ⟨537375990233822656787075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433002640623527084765533 537375990233822656787075)
                      ·
                        rfl

theorem cell23_1046536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_1046536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046536 prefixEnd_1046536 := by exact prefixLift 1046536
  have htrace : WordTrace (prefixWord ++ tailWord_1046536) baseStart_1046536 baseEnd_1046536 := by
    simpa [prefixWord, tailWord_1046536, baseEnd_1046536] using wordTrace_append hprefix tailTrace_1046536
  have hstable : (prefixWord ++ tailWord_1046536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046536).length < 2 ^ (prefixWord ++ tailWord_1046536).sum := by decide
  have hdescent : baseEnd_1046536 < baseStart_1046536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046552 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_1046552 : Nat := 118140960795 + 1046552 * 2 ^ 59
def prefixEnd_1046552 : Nat := 4983230072969 + 3 ^ 40 * 1046552 * 2
def baseEnd_1046552 : Nat := 179128068641431531395667

theorem tailTrace_1046552 : CollatzResearch.WordTrace tailWord_1046552 prefixEnd_1046552 179128068641431531395667 := by
  unfold tailWord_1046552
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085443652264157848370955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25447258203018877131161273 19085443652264157848370955)
  ·
    refine ⟨28628165478396236772556433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19085443652264157848370955 28628165478396236772556433)
    ·
      refine ⟨21471124108797177579417325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28628165478396236772556433 21471124108797177579417325)
      ·
        refine ⟨8051671540798941592281497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21471124108797177579417325 8051671540798941592281497)
        ·
          refine ⟨6038753655599206194211123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8051671540798941592281497 6038753655599206194211123)
          ·
            refine ⟨9058130483398809291316685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038753655599206194211123 9058130483398809291316685)
            ·
              refine ⟨3396798931274553484243757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9058130483398809291316685 3396798931274553484243757)
              ·
                refine ⟨1273799599227957556591409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396798931274553484243757 1273799599227957556591409)
                ·
                  refine ⟨955349699420968167443557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273799599227957556591409 955349699420968167443557)
                  ·
                    refine ⟨179128068641431531395667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 955349699420968167443557 179128068641431531395667)
                    ·
                      rfl

theorem cell23_1046552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_1046552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046552 prefixEnd_1046552 := by exact prefixLift 1046552
  have htrace : WordTrace (prefixWord ++ tailWord_1046552) baseStart_1046552 baseEnd_1046552 := by
    simpa [prefixWord, tailWord_1046552, baseEnd_1046552] using wordTrace_append hprefix tailTrace_1046552
  have hstable : (prefixWord ++ tailWord_1046552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046552).length < 2 ^ (prefixWord ++ tailWord_1046552).sum := by decide
  have hdescent : baseEnd_1046552 < baseStart_1046552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046562 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1046562 : Nat := 118140960795 + 1046562 * 2 ^ 59
def prefixEnd_1046562 : Nat := 4983230072969 + 3 ^ 40 * 1046562 * 2
def baseEnd_1046562 : Nat := 537389340730839555061955

theorem tailTrace_1046562 : CollatzResearch.WordTrace tailWord_1046562 prefixEnd_1046562 537389340730839555061955 := by
  unfold tailWord_1046562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542813008623021851151485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25447501356328058269737293 9542813008623021851151485)
  ·
    refine ⟨3578554878233633194181807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9542813008623021851151485 3578554878233633194181807)
    ·
      refine ⟨5367832317350449791272711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578554878233633194181807 5367832317350449791272711)
      ·
        refine ⟨8051748476025674686909067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367832317350449791272711 8051748476025674686909067)
        ·
          refine ⟨12077622714038512030363601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051748476025674686909067 12077622714038512030363601)
          ·
            refine ⟨9058217035528884022772701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12077622714038512030363601 9058217035528884022772701)
            ·
              refine ⟨3396831388323331508539763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9058217035528884022772701 3396831388323331508539763)
              ·
                refine ⟨5095247082484997262809645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396831388323331508539763 5095247082484997262809645)
                ·
                  refine ⟨1910717655931873973553617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5095247082484997262809645 1910717655931873973553617)
                  ·
                    refine ⟨1433038241948905480165213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1910717655931873973553617 1433038241948905480165213)
                    ·
                      refine ⟨537389340730839555061955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433038241948905480165213 537389340730839555061955)
                      ·
                        rfl

theorem cell23_1046562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1046562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046562 prefixEnd_1046562 := by exact prefixLift 1046562
  have htrace : WordTrace (prefixWord ++ tailWord_1046562) baseStart_1046562 baseEnd_1046562 := by
    simpa [prefixWord, tailWord_1046562, baseEnd_1046562] using wordTrace_append hprefix tailTrace_1046562
  have hstable : (prefixWord ++ tailWord_1046562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046562).length < 2 ^ (prefixWord ++ tailWord_1046562).sum := by decide
  have hdescent : baseEnd_1046562 < baseStart_1046562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046593 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1046593 : Nat := 118140960795 + 1046593 * 2 ^ 59
def prefixEnd_1046593 : Nat := 4983230072969 + 3 ^ 40 * 1046593 * 2
def baseEnd_1046593 : Nat := 537405258631128933774313

theorem tailTrace_1046593 : CollatzResearch.WordTrace tailWord_1046593 prefixEnd_1046593 537405258631128933774313 := by
  unfold tailWord_1046593
  simp only [CollatzResearch.WordTrace]
  refine ⟨38172382697379779698984433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25448255131586519799322955 38172382697379779698984433)
  ·
    refine ⟨28629287023034834774238325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38172382697379779698984433 28629287023034834774238325)
    ·
      refine ⟨2683995658409515760084843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28629287023034834774238325 2683995658409515760084843)
      ·
        refine ⟨4025993487614273640127265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683995658409515760084843 4025993487614273640127265)
        ·
          refine ⟨3019495115710705230095449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025993487614273640127265 3019495115710705230095449)
          ·
            refine ⟨2264621336783028922571587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019495115710705230095449 2264621336783028922571587)
            ·
              refine ⟨3396932005174543383857381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264621336783028922571587 3396932005174543383857381)
              ·
                refine ⟨636924750970226884473259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3396932005174543383857381 636924750970226884473259)
                ·
                  refine ⟨955387126455340326709889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636924750970226884473259 955387126455340326709889)
                  ·
                    refine ⟨716540344841505245032417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955387126455340326709889 716540344841505245032417)
                    ·
                      refine ⟨537405258631128933774313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716540344841505245032417 537405258631128933774313)
                      ·
                        rfl

theorem cell23_1046593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1046593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046593 prefixEnd_1046593 := by exact prefixLift 1046593
  have htrace : WordTrace (prefixWord ++ tailWord_1046593) baseStart_1046593 baseEnd_1046593 := by
    simpa [prefixWord, tailWord_1046593, baseEnd_1046593] using wordTrace_append hprefix tailTrace_1046593
  have hstable : (prefixWord ++ tailWord_1046593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046593).length < 2 ^ (prefixWord ++ tailWord_1046593).sum := by decide
  have hdescent : baseEnd_1046593 < baseStart_1046593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046636 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_1046636 : Nat := 118140960795 + 1046636 * 2 ^ 59
def prefixEnd_1046636 : Nat := 4983230072969 + 3 ^ 40 * 1046636 * 2
def baseEnd_1046636 : Nat := 537427338299272265536615

theorem tailTrace_1046636 : CollatzResearch.WordTrace tailWord_1046636 prefixEnd_1046636 537427338299272265536615 := by
  unfold tailWord_1046636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086975518111999021399881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25449300690815998695199841 19086975518111999021399881)
  ·
    refine ⟨14315231638583999266049911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19086975518111999021399881 14315231638583999266049911)
    ·
      refine ⟨21472847457875998899074867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14315231638583999266049911 21472847457875998899074867)
      ·
        refine ⟨32209271186813998348612301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21472847457875998899074867 32209271186813998348612301)
        ·
          refine ⟨12078476695055249380729613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32209271186813998348612301 12078476695055249380729613)
          ·
            refine ⟨4529428760645718517773605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12078476695055249380729613 4529428760645718517773605)
            ·
              refine ⟨849267892621072222082551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4529428760645718517773605 849267892621072222082551)
              ·
                refine ⟨1273901838931608333123827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849267892621072222082551 1273901838931608333123827)
                ·
                  refine ⟨1910852758397412499685741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273901838931608333123827 1910852758397412499685741)
                  ·
                    refine ⟨716569784399029687382153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910852758397412499685741 716569784399029687382153)
                    ·
                      refine ⟨537427338299272265536615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716569784399029687382153 537427338299272265536615)
                      ·
                        rfl

theorem cell23_1046636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_1046636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046636 prefixEnd_1046636 := by exact prefixLift 1046636
  have htrace : WordTrace (prefixWord ++ tailWord_1046636) baseStart_1046636 baseEnd_1046636 := by
    simpa [prefixWord, tailWord_1046636, baseEnd_1046636] using wordTrace_append hprefix tailTrace_1046636
  have hstable : (prefixWord ++ tailWord_1046636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046636).length < 2 ^ (prefixWord ++ tailWord_1046636).sum := by decide
  have hdescent : baseEnd_1046636 < baseStart_1046636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046666 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_1046666 : Nat := 118140960795 + 1046666 * 2 ^ 59
def prefixEnd_1046666 : Nat := 4983230072969 + 3 ^ 40 * 1046666 * 2
def baseEnd_1046666 : Nat := 537442742718907148161477

theorem tailTrace_1046666 : CollatzResearch.WordTrace tailWord_1046666 prefixEnd_1046666 537442742718907148161477 := by
  unfold tailWord_1046666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9543761306528828291597963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25450030150743542110927901 9543761306528828291597963)
  ·
    refine ⟨14315641959793242437396945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9543761306528828291597963 14315641959793242437396945)
    ·
      refine ⟨10736731469844931828047709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14315641959793242437396945 10736731469844931828047709)
      ·
        refine ⟨4026274301191849435517891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10736731469844931828047709 4026274301191849435517891)
        ·
          refine ⟨6039411451787774153276837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026274301191849435517891 6039411451787774153276837)
          ·
            refine ⟨1132389647210207653739407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6039411451787774153276837 1132389647210207653739407)
            ·
              refine ⟨1698584470815311480609111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132389647210207653739407 1698584470815311480609111)
              ·
                refine ⟨2547876706222967220913667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698584470815311480609111 2547876706222967220913667)
                ·
                  refine ⟨3821815059334450831370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547876706222967220913667 3821815059334450831370501)
                  ·
                    refine ⟨716590323625209530881969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3821815059334450831370501 716590323625209530881969)
                    ·
                      refine ⟨537442742718907148161477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716590323625209530881969 537442742718907148161477)
                      ·
                        rfl

theorem cell23_1046666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_1046666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046666 prefixEnd_1046666 := by exact prefixLift 1046666
  have htrace : WordTrace (prefixWord ++ tailWord_1046666) baseStart_1046666 baseEnd_1046666 := by
    simpa [prefixWord, tailWord_1046666, baseEnd_1046666] using wordTrace_append hprefix tailTrace_1046666
  have hstable : (prefixWord ++ tailWord_1046666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046666).length < 2 ^ (prefixWord ++ tailWord_1046666).sum := by decide
  have hdescent : baseEnd_1046666 < baseStart_1046666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046678 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1046678 : Nat := 118140960795 + 1046678 * 2 ^ 59
def prefixEnd_1046678 : Nat := 4983230072969 + 3 ^ 40 * 1046678 * 2
def baseEnd_1046678 : Nat := 537448904486761101211423

theorem tailTrace_1046678 : CollatzResearch.WordTrace tailWord_1046678 prefixEnd_1046678 537448904486761101211423 := by
  unfold tailWord_1046678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385967681379489950989293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25450321934714559477219125 2385967681379489950989293)
  ·
    refine ⟨894737880517308731620985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2385967681379489950989293 894737880517308731620985)
    ·
      refine ⟨671053410387981548715739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894737880517308731620985 671053410387981548715739)
      ·
        refine ⟨1006580115581972323073609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671053410387981548715739 1006580115581972323073609)
        ·
          refine ⟨754935086686479242305207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006580115581972323073609 754935086686479242305207)
          ·
            refine ⟨1132402630029718863457811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754935086686479242305207 1132402630029718863457811)
            ·
              refine ⟨1698603945044578295186717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132402630029718863457811 1698603945044578295186717)
              ·
                refine ⟨636976479391716860695019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1698603945044578295186717 636976479391716860695019)
                ·
                  refine ⟨955464719087575291042529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636976479391716860695019 955464719087575291042529)
                  ·
                    refine ⟨716598539315681468281897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955464719087575291042529 716598539315681468281897)
                    ·
                      refine ⟨537448904486761101211423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716598539315681468281897 537448904486761101211423)
                      ·
                        rfl

theorem cell23_1046678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1046678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046678 prefixEnd_1046678 := by exact prefixLift 1046678
  have htrace : WordTrace (prefixWord ++ tailWord_1046678) baseStart_1046678 baseEnd_1046678 := by
    simpa [prefixWord, tailWord_1046678, baseEnd_1046678] using wordTrace_append hprefix tailTrace_1046678
  have hstable : (prefixWord ++ tailWord_1046678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046678).length < 2 ^ (prefixWord ++ tailWord_1046678).sum := by decide
  have hdescent : baseEnd_1046678 < baseStart_1046678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046689 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 5]
def baseStart_1046689 : Nat := 118140960795 + 1046689 * 2 ^ 59
def prefixEnd_1046689 : Nat := 4983230072969 + 3 ^ 40 * 1046689 * 2
def baseEnd_1046689 : Nat := 59717172530440062019319

theorem tailTrace_1046689 : CollatzResearch.WordTrace tailWord_1046689 prefixEnd_1046689 59717172530440062019319 := by
  unfold tailWord_1046689
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175884105031988094479121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25450589403354658729652747 38175884105031988094479121)
  ·
    refine ⟨28631913078773991070859341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38175884105031988094479121 28631913078773991070859341)
    ·
      refine ⟨10736967404540246651572253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28631913078773991070859341 10736967404540246651572253)
      ·
        refine ⟨4026362776702592494339595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10736967404540246651572253 4026362776702592494339595)
        ·
          refine ⟨6039544165053888741509393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026362776702592494339595 6039544165053888741509393)
          ·
            refine ⟨4529658123790416556132045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039544165053888741509393 4529658123790416556132045)
            ·
              refine ⟨1698621796421406208549517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4529658123790416556132045 1698621796421406208549517)
              ·
                refine ⟨636983173658027328206069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1698621796421406208549517 636983173658027328206069)
                ·
                  refine ⟨59717172530440062019319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 636983173658027328206069 59717172530440062019319)
                  ·
                    rfl

theorem cell23_1046689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 5].length) (baseStart_1046689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046689 prefixEnd_1046689 := by exact prefixLift 1046689
  have htrace : WordTrace (prefixWord ++ tailWord_1046689) baseStart_1046689 baseEnd_1046689 := by
    simpa [prefixWord, tailWord_1046689, baseEnd_1046689] using wordTrace_append hprefix tailTrace_1046689
  have hstable : (prefixWord ++ tailWord_1046689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046689).length < 2 ^ (prefixWord ++ tailWord_1046689).sum := by decide
  have hdescent : baseEnd_1046689 < baseStart_1046689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046745 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 10]
def baseStart_1046745 : Nat := 118140960795 + 1046745 * 2 ^ 59
def prefixEnd_1046745 : Nat := 4983230072969 + 3 ^ 40 * 1046745 * 2
def baseEnd_1046745 : Nat := 59720367521179148785957

theorem tailTrace_1046745 : CollatzResearch.WordTrace tailWord_1046745 prefixEnd_1046745 59720367521179148785957 := by
  unfold tailWord_1046745
  simp only [CollatzResearch.WordTrace]
  refine ⟨38177926592829109658517689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25451951061886073105678459 38177926592829109658517689)
  ·
    refine ⟨28633444944621832243888267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38177926592829109658517689 28633444944621832243888267)
    ·
      refine ⟨42950167416932748365832401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633444944621832243888267 42950167416932748365832401)
      ·
        refine ⟨32212625562699561274374301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42950167416932748365832401 32212625562699561274374301)
        ·
          refine ⟨12079734586012335477890363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32212625562699561274374301 12079734586012335477890363)
          ·
            refine ⟨18119601879018503216835545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079734586012335477890363 18119601879018503216835545)
            ·
              refine ⟨13589701409263877412626659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18119601879018503216835545 13589701409263877412626659)
              ·
                refine ⟨20384552113895816118939989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589701409263877412626659 20384552113895816118939989)
                ·
                  refine ⟨59720367521179148785957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20384552113895816118939989 59720367521179148785957)
                  ·
                    rfl

theorem cell23_1046745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_1046745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046745 prefixEnd_1046745 := by exact prefixLift 1046745
  have htrace : WordTrace (prefixWord ++ tailWord_1046745) baseStart_1046745 baseEnd_1046745 := by
    simpa [prefixWord, tailWord_1046745, baseEnd_1046745] using wordTrace_append hprefix tailTrace_1046745
  have hstable : (prefixWord ++ tailWord_1046745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046745).length < 2 ^ (prefixWord ++ tailWord_1046745).sum := by decide
  have hdescent : baseEnd_1046745 < baseStart_1046745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046775 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 11]
def baseStart_1046775 : Nat := 118140960795 + 1046775 * 2 ^ 59
def prefixEnd_1046775 : Nat := 4983230072969 + 3 ^ 40 * 1046775 * 2
def baseEnd_1046775 : Nat := 179166237370082407232825

theorem tailTrace_1046775 : CollatzResearch.WordTrace tailWord_1046775 prefixEnd_1046775 179166237370082407232825 := by
  unfold tailWord_1046775
  simp only [CollatzResearch.WordTrace]
  refine ⟨38179020782720424782109779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25452680521813616521406519 38179020782720424782109779)
  ·
    refine ⟨57268531174080637173164669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38179020782720424782109779 57268531174080637173164669)
    ·
      refine ⟨21475699190280238939936751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57268531174080637173164669 21475699190280238939936751)
      ·
        refine ⟨32213548785420358409905127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21475699190280238939936751 32213548785420358409905127)
        ·
          refine ⟨48320323178130537614857691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32213548785420358409905127 48320323178130537614857691)
          ·
            refine ⟨72480484767195806422286537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48320323178130537614857691 72480484767195806422286537)
            ·
              refine ⟨54360363575396854816714903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72480484767195806422286537 54360363575396854816714903)
              ·
                refine ⟨81540545363095282225072355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54360363575396854816714903 81540545363095282225072355)
                ·
                  refine ⟨122310818044642923337608533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81540545363095282225072355 122310818044642923337608533)
                  ·
                    refine ⟨179166237370082407232825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 122310818044642923337608533 179166237370082407232825)
                    ·
                      rfl

theorem cell23_1046775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_1046775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046775 prefixEnd_1046775 := by exact prefixLift 1046775
  have htrace : WordTrace (prefixWord ++ tailWord_1046775) baseStart_1046775 baseEnd_1046775 := by
    simpa [prefixWord, tailWord_1046775, baseEnd_1046775] using wordTrace_append hprefix tailTrace_1046775
  have hstable : (prefixWord ++ tailWord_1046775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046775).length < 2 ^ (prefixWord ++ tailWord_1046775).sum := by decide
  have hdescent : baseEnd_1046775 < baseStart_1046775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046813 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 6]
def baseStart_1046813 : Nat := 118140960795 + 1046813 * 2 ^ 59
def prefixEnd_1046813 : Nat := 4983230072969 + 3 ^ 40 * 1046813 * 2
def baseEnd_1046813 : Nat := 59724247152790897002589

theorem tailTrace_1046813 : CollatzResearch.WordTrace tailWord_1046813 prefixEnd_1046813 59724247152790897002589 := by
  unfold tailWord_1046813
  simp only [CollatzResearch.WordTrace]
  refine ⟨38180406756582757271993093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25453604504388504847995395 38180406756582757271993093)
  ·
    refine ⟨7158826266859266988498705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38180406756582757271993093 7158826266859266988498705)
    ·
      refine ⟨5369119700144450241374029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7158826266859266988498705 5369119700144450241374029)
      ·
        refine ⟨2013419887554168840515261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5369119700144450241374029 2013419887554168840515261)
        ·
          refine ⟨755032457832813315193223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2013419887554168840515261 755032457832813315193223)
          ·
            refine ⟨1132548686749219972789835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755032457832813315193223 1132548686749219972789835)
            ·
              refine ⟨1698823030123829959184753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132548686749219972789835 1698823030123829959184753)
              ·
                refine ⟨1274117272592872469388565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698823030123829959184753 1274117272592872469388565)
                ·
                  refine ⟨59724247152790897002589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1274117272592872469388565 59724247152790897002589)
                  ·
                    rfl

theorem cell23_1046813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_1046813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046813 prefixEnd_1046813 := by exact prefixLift 1046813
  have htrace : WordTrace (prefixWord ++ tailWord_1046813) baseStart_1046813 baseEnd_1046813 := by
    simpa [prefixWord, tailWord_1046813, baseEnd_1046813] using wordTrace_append hprefix tailTrace_1046813
  have hstable : (prefixWord ++ tailWord_1046813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046813).length < 2 ^ (prefixWord ++ tailWord_1046813).sum := by decide
  have hdescent : baseEnd_1046813 < baseStart_1046813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046832 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_1046832 : Nat := 118140960795 + 1046832 * 2 ^ 59
def prefixEnd_1046832 : Nat := 4983230072969 + 3 ^ 40 * 1046832 * 2
def baseEnd_1046832 : Nat := 537527980507553498685713

theorem tailTrace_1046832 : CollatzResearch.WordTrace tailWord_1046832 prefixEnd_1046832 537527980507553498685713 := by
  unfold tailWord_1046832
  simp only [CollatzResearch.WordTrace]
  refine ⟨19090549871756961758467375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25454066495675949011289833 19090549871756961758467375)
  ·
    refine ⟨28635824807635442637701063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19090549871756961758467375 28635824807635442637701063)
    ·
      refine ⟨42953737211453163956551595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28635824807635442637701063 42953737211453163956551595)
      ·
        refine ⟨64430605817179745934827393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42953737211453163956551595 64430605817179745934827393)
        ·
          refine ⟨48322954362884809451120545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64430605817179745934827393 48322954362884809451120545)
          ·
            refine ⟨36242215772163607088340409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48322954362884809451120545 36242215772163607088340409)
            ·
              refine ⟨27181661829122705316255307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36242215772163607088340409 27181661829122705316255307)
              ·
                refine ⟨40772492743684057974382961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27181661829122705316255307 40772492743684057974382961)
                ·
                  refine ⟨30579369557763043480787221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40772492743684057974382961 30579369557763043480787221)
                  ·
                    refine ⟨1433407948020142663161901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30579369557763043480787221 1433407948020142663161901)
                    ·
                      refine ⟨537527980507553498685713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433407948020142663161901 537527980507553498685713)
                      ·
                        rfl

theorem cell23_1046832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_1046832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046832 prefixEnd_1046832 := by exact prefixLift 1046832
  have htrace : WordTrace (prefixWord ++ tailWord_1046832) baseStart_1046832 baseEnd_1046832 := by
    simpa [prefixWord, tailWord_1046832, baseEnd_1046832] using wordTrace_append hprefix tailTrace_1046832
  have hstable : (prefixWord ++ tailWord_1046832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046832).length < 2 ^ (prefixWord ++ tailWord_1046832).sum := by decide
  have hdescent : baseEnd_1046832 < baseStart_1046832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046839 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 2, 4]
def baseStart_1046839 : Nat := 118140960795 + 1046839 * 2 ^ 59
def prefixEnd_1046839 : Nat := 4983230072969 + 3 ^ 40 * 1046839 * 2
def baseEnd_1046839 : Nat := 179177191624044990432727

theorem tailTrace_1046839 : CollatzResearch.WordTrace tailWord_1046839 prefixEnd_1046839 179177191624044990432727 := by
  unfold tailWord_1046839
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181355054488563712439571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25454236702992375808293047 38181355054488563712439571)
  ·
    refine ⟨57272032581732845568659357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38181355054488563712439571 57272032581732845568659357)
    ·
      refine ⟨21477012218149817088247259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57272032581732845568659357 21477012218149817088247259)
      ·
        refine ⟨32215518327224725632370889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21477012218149817088247259 32215518327224725632370889)
        ·
          refine ⟨24161638745418544224278167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32215518327224725632370889 24161638745418544224278167)
          ·
            refine ⟨36242458118127816336417251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161638745418544224278167 36242458118127816336417251)
            ·
              refine ⟨54363687177191724504625877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36242458118127816336417251 54363687177191724504625877)
              ·
                refine ⟨1274148918215431043077169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54363687177191724504625877 1274148918215431043077169)
                ·
                  refine ⟨955611688661573282307877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274148918215431043077169 955611688661573282307877)
                  ·
                    refine ⟨179177191624044990432727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 955611688661573282307877 179177191624044990432727)
                    ·
                      rfl

theorem cell23_1046839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_1046839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046839 prefixEnd_1046839 := by exact prefixLift 1046839
  have htrace : WordTrace (prefixWord ++ tailWord_1046839) baseStart_1046839 baseEnd_1046839 := by
    simpa [prefixWord, tailWord_1046839, baseEnd_1046839] using wordTrace_append hprefix tailTrace_1046839
  have hstable : (prefixWord ++ tailWord_1046839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046839).length < 2 ^ (prefixWord ++ tailWord_1046839).sum := by decide
  have hdescent : baseEnd_1046839 < baseStart_1046839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046846 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1046846 : Nat := 118140960795 + 1046846 * 2 ^ 59
def prefixEnd_1046846 : Nat := 4983230072969 + 3 ^ 40 * 1046846 * 2
def baseEnd_1046846 : Nat := 537535169236716443910649

theorem tailTrace_1046846 : CollatzResearch.WordTrace tailWord_1046846 prefixEnd_1046846 537535169236716443910649 := by
  unfold tailWord_1046846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772701295682900488493049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25454406910308802605296261 4772701295682900488493049)
  ·
    refine ⟨3579525971762175366369787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4772701295682900488493049 3579525971762175366369787)
    ·
      refine ⟨5369288957643263049554681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579525971762175366369787 5369288957643263049554681)
      ·
        refine ⟨4026966718232447287166011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5369288957643263049554681 4026966718232447287166011)
        ·
          refine ⟨6040450077348670930749017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026966718232447287166011 6040450077348670930749017)
          ·
            refine ⟨4530337558011503198061763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6040450077348670930749017 4530337558011503198061763)
            ·
              refine ⟨6795506337017254797092645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530337558011503198061763 6795506337017254797092645)
              ·
                refine ⟨1274157438190735274454871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6795506337017254797092645 1274157438190735274454871)
                ·
                  refine ⟨1911236157286102911682307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274157438190735274454871 1911236157286102911682307)
                  ·
                    refine ⟨2866854235929154367523461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1911236157286102911682307 2866854235929154367523461)
                    ·
                      refine ⟨537535169236716443910649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2866854235929154367523461 537535169236716443910649)
                      ·
                        rfl

theorem cell23_1046846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1046846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046846 prefixEnd_1046846 := by exact prefixLift 1046846
  have htrace : WordTrace (prefixWord ++ tailWord_1046846) baseStart_1046846 baseEnd_1046846 := by
    simpa [prefixWord, tailWord_1046846, baseEnd_1046846] using wordTrace_append hprefix tailTrace_1046846
  have hstable : (prefixWord ++ tailWord_1046846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046846).length < 2 ^ (prefixWord ++ tailWord_1046846).sum := by decide
  have hdescent : baseEnd_1046846 < baseStart_1046846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046863 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 1, 2, 2]
def baseStart_1046863 : Nat := 118140960795 + 1046863 * 2 ^ 59
def prefixEnd_1046863 : Nat := 4983230072969 + 3 ^ 40 * 1046863 * 2
def baseEnd_1046863 : Nat := 537543898407842877398071

theorem tailTrace_1046863 : CollatzResearch.WordTrace tailWord_1046863 prefixEnd_1046863 537543898407842877398071 := by
  unfold tailWord_1046863
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182230406401615811313243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25454820270934410540875495 38182230406401615811313243)
  ·
    refine ⟨57273345609602423716969865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38182230406401615811313243 57273345609602423716969865)
    ·
      refine ⟨42955009207201817787727399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57273345609602423716969865 42955009207201817787727399)
      ·
        refine ⟨64432513810802726681591099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42955009207201817787727399 64432513810802726681591099)
        ·
          refine ⟨96648770716204090022386649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64432513810802726681591099 96648770716204090022386649)
          ·
            refine ⟨72486578037153067516789987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96648770716204090022386649 72486578037153067516789987)
            ·
              refine ⟨108729867055729601275184981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72486578037153067516789987 108729867055729601275184981)
              ·
                refine ⟨637089064779665632471787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 108729867055729601275184981 637089064779665632471787)
                ·
                  refine ⟨955633597169498448707681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637089064779665632471787 955633597169498448707681)
                  ·
                    refine ⟨716725197877123836530761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955633597169498448707681 716725197877123836530761)
                    ·
                      refine ⟨537543898407842877398071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716725197877123836530761 537543898407842877398071)
                      ·
                        rfl

theorem cell23_1046863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 2, 2].length) (baseStart_1046863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046863 prefixEnd_1046863 := by exact prefixLift 1046863
  have htrace : WordTrace (prefixWord ++ tailWord_1046863) baseStart_1046863 baseEnd_1046863 := by
    simpa [prefixWord, tailWord_1046863, baseEnd_1046863] using wordTrace_append hprefix tailTrace_1046863
  have hstable : (prefixWord ++ tailWord_1046863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046863).length < 2 ^ (prefixWord ++ tailWord_1046863).sum := by decide
  have hdescent : baseEnd_1046863 < baseStart_1046863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046866 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1046866 : Nat := 118140960795 + 1046866 * 2 ^ 59
def prefixEnd_1046866 : Nat := 4983230072969 + 3 ^ 40 * 1046866 * 2
def baseEnd_1046866 : Nat := 537545438849806365660557

theorem tailTrace_1046866 : CollatzResearch.WordTrace tailWord_1046866 prefixEnd_1046866 537545438849806365660557 := by
  unfold tailWord_1046866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545584956347686830918113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25454893216927164882448301 9545584956347686830918113)
  ·
    refine ⟨7159188717260765123188585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9545584956347686830918113 7159188717260765123188585)
    ·
      refine ⟨5369391537945573842391439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7159188717260765123188585 5369391537945573842391439)
      ·
        refine ⟨8054087306918360763587159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369391537945573842391439 8054087306918360763587159)
        ·
          refine ⟨12081130960377541145380739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054087306918360763587159 12081130960377541145380739)
          ·
            refine ⟨18121696440566311718071109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081130960377541145380739 18121696440566311718071109)
            ·
              refine ⟨3397818082606183447138333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18121696440566311718071109 3397818082606183447138333)
              ·
                refine ⟨1274181780977318792676875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3397818082606183447138333 1274181780977318792676875)
                ·
                  refine ⟨1911272671465978189015313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274181780977318792676875 1911272671465978189015313)
                  ·
                    refine ⟨1433454503599483641761485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911272671465978189015313 1433454503599483641761485)
                    ·
                      refine ⟨537545438849806365660557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433454503599483641761485 537545438849806365660557)
                      ·
                        rfl

theorem cell23_1046866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1046866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046866 prefixEnd_1046866 := by exact prefixLift 1046866
  have htrace : WordTrace (prefixWord ++ tailWord_1046866) baseStart_1046866 baseEnd_1046866 := by
    simpa [prefixWord, tailWord_1046866, baseEnd_1046866] using wordTrace_append hprefix tailTrace_1046866
  have hstable : (prefixWord ++ tailWord_1046866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046866).length < 2 ^ (prefixWord ++ tailWord_1046866).sum := by decide
  have hdescent : baseEnd_1046866 < baseStart_1046866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046869 : List Nat := [1, 3, 2, 2, 4, 2, 9]
def baseStart_1046869 : Nat := 118140960795 + 1046869 * 2 ^ 59
def prefixEnd_1046869 : Nat := 4983230072969 + 3 ^ 40 * 1046869 * 2
def baseEnd_1046869 : Nat := 6636382460392220418803

theorem tailTrace_1046869 : CollatzResearch.WordTrace tailWord_1046869 prefixEnd_1046869 6636382460392220418803 := by
  unfold tailWord_1046869
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182449244379878836031661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25454966162919919224021107 38182449244379878836031661)
  ·
    refine ⟨14318418466642454563511873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38182449244379878836031661 14318418466642454563511873)
    ·
      refine ⟨10738813849981840922633905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14318418466642454563511873 10738813849981840922633905)
      ·
        refine ⟨8054110387486380691975429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10738813849981840922633905 8054110387486380691975429)
        ·
          refine ⟨1510145697653696379745393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8054110387486380691975429 1510145697653696379745393)
          ·
            refine ⟨1132609273240272284809045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510145697653696379745393 1132609273240272284809045)
            ·
              refine ⟨6636382460392220418803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1132609273240272284809045 6636382460392220418803)
              ·
                rfl

theorem cell23_1046869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 9].length) (baseStart_1046869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046869 prefixEnd_1046869 := by exact prefixLift 1046869
  have htrace : WordTrace (prefixWord ++ tailWord_1046869) baseStart_1046869 baseEnd_1046869 := by
    simpa [prefixWord, tailWord_1046869, baseEnd_1046869] using wordTrace_append hprefix tailTrace_1046869
  have hstable : (prefixWord ++ tailWord_1046869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046869).length < 2 ^ (prefixWord ++ tailWord_1046869).sum := by decide
  have hdescent : baseEnd_1046869 < baseStart_1046869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046880 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2]
def baseStart_1046880 : Nat := 118140960795 + 1046880 * 2 ^ 59
def prefixEnd_1046880 : Nat := 4983230072969 + 3 ^ 40 * 1046880 * 2
def baseEnd_1046880 : Nat := 537552627578969310885493

theorem tailTrace_1046880 : CollatzResearch.WordTrace tailWord_1046880 prefixEnd_1046880 537552627578969310885493 := by
  unfold tailWord_1046880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091425223670013857341047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25455233631560018476454729 19091425223670013857341047)
  ·
    refine ⟨28637137835505020786011571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19091425223670013857341047 28637137835505020786011571)
    ·
      refine ⟨42955706753257531179017357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28637137835505020786011571 42955706753257531179017357)
      ·
        refine ⟨16108390032471574192131509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42955706753257531179017357 16108390032471574192131509)
        ·
          refine ⟨1510161565544210080512329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16108390032471574192131509 1510161565544210080512329)
          ·
            refine ⟨1132621174158157560384247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510161565544210080512329 1132621174158157560384247)
            ·
              refine ⟨1698931761237236340576371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132621174158157560384247 1698931761237236340576371)
              ·
                refine ⟨2548397641855854510864557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698931761237236340576371 2548397641855854510864557)
                ·
                  refine ⟨955649115695945441574209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2548397641855854510864557 955649115695945441574209)
                  ·
                    refine ⟨716736836771959081180657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955649115695945441574209 716736836771959081180657)
                    ·
                      refine ⟨537552627578969310885493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716736836771959081180657 537552627578969310885493)
                      ·
                        rfl

theorem cell23_1046880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_1046880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046880 prefixEnd_1046880 := by exact prefixLift 1046880
  have htrace : WordTrace (prefixWord ++ tailWord_1046880) baseStart_1046880 baseEnd_1046880 := by
    simpa [prefixWord, tailWord_1046880, baseEnd_1046880] using wordTrace_append hprefix tailTrace_1046880
  have hstable : (prefixWord ++ tailWord_1046880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046880).length < 2 ^ (prefixWord ++ tailWord_1046880).sum := by decide
  have hdescent : baseEnd_1046880 < baseStart_1046880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046890 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1046890 : Nat := 118140960795 + 1046890 * 2 ^ 59
def prefixEnd_1046890 : Nat := 4983230072969 + 3 ^ 40 * 1046890 * 2
def baseEnd_1046890 : Nat := 179185920795171423920149

theorem tailTrace_1046890 : CollatzResearch.WordTrace tailWord_1046890 prefixEnd_1046890 179185920795171423920149 := by
  unfold tailWord_1046890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545803794325949855636531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25455476784869199615030749 9545803794325949855636531)
  ·
    refine ⟨14318705691488924783454797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9545803794325949855636531 14318705691488924783454797)
    ·
      refine ⟨5369514634308346793795549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14318705691488924783454797 5369514634308346793795549)
      ·
        refine ⟨2013567987865630047673331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5369514634308346793795549 2013567987865630047673331)
        ·
          refine ⟨3020351981798445071509997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013567987865630047673331 3020351981798445071509997)
          ·
            refine ⟨1132631993174416901816249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020351981798445071509997 1132631993174416901816249)
            ·
              refine ⟨849473994880812676362187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132631993174416901816249 849473994880812676362187)
              ·
                refine ⟨1274210992321219014543281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849473994880812676362187 1274210992321219014543281)
                ·
                  refine ⟨955658244240914260907461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274210992321219014543281 955658244240914260907461)
                  ·
                    refine ⟨179185920795171423920149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 955658244240914260907461 179185920795171423920149)
                    ·
                      rfl

theorem cell23_1046890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1046890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046890 prefixEnd_1046890 := by exact prefixLift 1046890
  have htrace : WordTrace (prefixWord ++ tailWord_1046890) baseStart_1046890 baseEnd_1046890 := by
    simpa [prefixWord, tailWord_1046890, baseEnd_1046890] using wordTrace_append hprefix tailTrace_1046890
  have hstable : (prefixWord ++ tailWord_1046890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046890).length < 2 ^ (prefixWord ++ tailWord_1046890).sum := by decide
  have hdescent : baseEnd_1046890 < baseStart_1046890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046912 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_1046912 : Nat := 118140960795 + 1046912 * 2 ^ 59
def prefixEnd_1046912 : Nat := 4983230072969 + 3 ^ 40 * 1046912 * 2
def baseEnd_1046912 : Nat := 179189686319971061895115

theorem tailTrace_1046912 : CollatzResearch.WordTrace tailWord_1046912 prefixEnd_1046912 179189686319971061895115 := by
  unfold tailWord_1046912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092008791612048589923495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25456011722149398119897993 19092008791612048589923495)
  ·
    refine ⟨28638013187418072884885243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092008791612048589923495 28638013187418072884885243)
    ·
      refine ⟨42957019781127109327327865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28638013187418072884885243 42957019781127109327327865)
      ·
        refine ⟨32217764835845331995495899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42957019781127109327327865 32217764835845331995495899)
        ·
          refine ⟨48326647253767997993243849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32217764835845331995495899 48326647253767997993243849)
          ·
            refine ⟨36244985440325998494932887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48326647253767997993243849 36244985440325998494932887)
            ·
              refine ⟨54367478160488997742399331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36244985440325998494932887 54367478160488997742399331)
              ·
                refine ⟨81551217240733496613598997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54367478160488997742399331 81551217240733496613598997)
                ·
                  refine ⟨3822713308159382653762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81551217240733496613598997 3822713308159382653762453)
                  ·
                    refine ⟨179189686319971061895115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3822713308159382653762453 179189686319971061895115)
                    ·
                      rfl

theorem cell23_1046912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_1046912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046912 prefixEnd_1046912 := by exact prefixLift 1046912
  have htrace : WordTrace (prefixWord ++ tailWord_1046912) baseStart_1046912 baseEnd_1046912 := by
    simpa [prefixWord, tailWord_1046912, baseEnd_1046912] using wordTrace_append hprefix tailTrace_1046912
  have hstable : (prefixWord ++ tailWord_1046912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046912).length < 2 ^ (prefixWord ++ tailWord_1046912).sum := by decide
  have hdescent : baseEnd_1046912 < baseStart_1046912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046949 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_1046949 : Nat := 118140960795 + 1046949 * 2 ^ 59
def prefixEnd_1046949 : Nat := 4983230072969 + 3 ^ 40 * 1046949 * 2
def baseEnd_1046949 : Nat := 537588057744129540922675

theorem tailTrace_1046949 : CollatzResearch.WordTrace tailWord_1046949 prefixEnd_1046949 537588057744129540922675 := by
  unfold tailWord_1046949
  simp only [CollatzResearch.WordTrace]
  refine ⟨38185367084090052498943901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25456911389393368332629267 38185367084090052498943901)
  ·
    refine ⟨14319512656533769687103963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38185367084090052498943901 14319512656533769687103963)
    ·
      refine ⟨21479268984800654530655945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14319512656533769687103963 21479268984800654530655945)
      ·
        refine ⟨16109451738600490897991959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21479268984800654530655945 16109451738600490897991959)
        ·
          refine ⟨24164177607900736346987939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109451738600490897991959 24164177607900736346987939)
          ·
            refine ⟨36246266411851104520481909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24164177607900736346987939 36246266411851104520481909)
            ·
              refine ⟨3398087476111041048795179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36246266411851104520481909 3398087476111041048795179)
              ·
                refine ⟨5097131214166561573192769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398087476111041048795179 5097131214166561573192769)
                ·
                  refine ⟨3822848410624921179894577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5097131214166561573192769 3822848410624921179894577)
                  ·
                    refine ⟨2867136307968690884920933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3822848410624921179894577 2867136307968690884920933)
                    ·
                      refine ⟨537588057744129540922675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2867136307968690884920933 537588057744129540922675)
                      ·
                        rfl

theorem cell23_1046949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_1046949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1046949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1046949 prefixEnd_1046949 := by exact prefixLift 1046949
  have htrace : WordTrace (prefixWord ++ tailWord_1046949) baseStart_1046949 baseEnd_1046949 := by
    simpa [prefixWord, tailWord_1046949, baseEnd_1046949] using wordTrace_append hprefix tailTrace_1046949
  have hstable : (prefixWord ++ tailWord_1046949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046949).length < 2 ^ (prefixWord ++ tailWord_1046949).sum := by decide
  have hdescent : baseEnd_1046949 < baseStart_1046949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047009 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1047009 : Nat := 118140960795 + 1047009 * 2 ^ 59
def prefixEnd_1047009 : Nat := 4983230072969 + 3 ^ 40 * 1047009 * 2
def baseEnd_1047009 : Nat := 537618866583399306172399

theorem tailTrace_1047009 : CollatzResearch.WordTrace tailWord_1047009 prefixEnd_1047009 537618866583399306172399 := by
  unfold tailWord_1047009
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187555463872682746128081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25458370309248455164085387 38187555463872682746128081)
  ·
    refine ⟨28640666597904512059596061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38187555463872682746128081 28640666597904512059596061)
    ·
      refine ⟨10740249974214192022348523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28640666597904512059596061 10740249974214192022348523)
      ·
        refine ⟨16110374961321288033522785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740249974214192022348523 16110374961321288033522785)
        ·
          refine ⟨12082781220990966025142089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16110374961321288033522785 12082781220990966025142089)
          ·
            refine ⟨9062085915743224518856567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12082781220990966025142089 9062085915743224518856567)
            ·
              refine ⟨13593128873614836778284851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062085915743224518856567 13593128873614836778284851)
              ·
                refine ⟨20389693310422255167427277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593128873614836778284851 20389693310422255167427277)
                ·
                  refine ⟨7646134991408345687785229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20389693310422255167427277 7646134991408345687785229)
                  ·
                    refine ⟨2867300621778129632919461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7646134991408345687785229 2867300621778129632919461)
                    ·
                      refine ⟨537618866583399306172399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2867300621778129632919461 537618866583399306172399)
                      ·
                        rfl

theorem cell23_1047009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1047009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047009 prefixEnd_1047009 := by exact prefixLift 1047009
  have htrace : WordTrace (prefixWord ++ tailWord_1047009) baseStart_1047009 baseEnd_1047009 := by
    simpa [prefixWord, tailWord_1047009, baseEnd_1047009] using wordTrace_append hprefix tailTrace_1047009
  have hstable : (prefixWord ++ tailWord_1047009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047009).length < 2 ^ (prefixWord ++ tailWord_1047009).sum := by decide
  have hdescent : baseEnd_1047009 < baseStart_1047009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047080 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1047080 : Nat := 118140960795 + 1047080 * 2 ^ 59
def prefixEnd_1047080 : Nat := 4983230072969 + 3 ^ 40 * 1047080 * 2
def baseEnd_1047080 : Nat := 537655323709868528384573

theorem tailTrace_1047080 : CollatzResearch.WordTrace tailWord_1047080 prefixEnd_1047080 537655323709868528384573 := by
  unfold tailWord_1047080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095072523307730935981347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25460096697743641247975129 19095072523307730935981347)
  ·
    refine ⟨28642608784961596403972021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19095072523307730935981347 28642608784961596403972021)
    ·
      refine ⟨2685244573590149662872377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28642608784961596403972021 2685244573590149662872377)
      ·
        refine ⟨2013933430192612247154283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2685244573590149662872377 2013933430192612247154283)
        ·
          refine ⟨3020900145288918370731425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013933430192612247154283 3020900145288918370731425)
          ·
            refine ⟨2265675108966688778048569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3020900145288918370731425 2265675108966688778048569)
            ·
              refine ⟨1699256331725016583536427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265675108966688778048569 1699256331725016583536427)
              ·
                refine ⟨2548884497587524875304641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699256331725016583536427 2548884497587524875304641)
                ·
                  refine ⟨1911663373190643656478481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548884497587524875304641 1911663373190643656478481)
                  ·
                    refine ⟨1433747529892982742358861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911663373190643656478481 1433747529892982742358861)
                    ·
                      refine ⟨537655323709868528384573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433747529892982742358861 537655323709868528384573)
                      ·
                        rfl

theorem cell23_1047080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1047080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047080 prefixEnd_1047080 := by exact prefixLift 1047080
  have htrace : WordTrace (prefixWord ++ tailWord_1047080) baseStart_1047080 baseEnd_1047080 := by
    simpa [prefixWord, tailWord_1047080, baseEnd_1047080] using wordTrace_append hprefix tailTrace_1047080
  have hstable : (prefixWord ++ tailWord_1047080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047080).length < 2 ^ (prefixWord ++ tailWord_1047080).sum := by decide
  have hdescent : baseEnd_1047080 < baseStart_1047080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047099 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_1047099 : Nat := 118140960795 + 1047099 * 2 ^ 59
def prefixEnd_1047099 : Nat := 4983230072969 + 3 ^ 40 * 1047099 * 2
def baseEnd_1047099 : Nat := 537665079842303954046985

theorem tailTrace_1047099 : CollatzResearch.WordTrace tailWord_1047099 prefixEnd_1047099 537665079842303954046985 := by
  unfold tailWord_1047099
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190838033546628116904351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25460558689031085411269567 38190838033546628116904351)
  ·
    refine ⟨57286257050319942175356527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38190838033546628116904351 57286257050319942175356527)
    ·
      refine ⟨85929385575479913263034791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57286257050319942175356527 85929385575479913263034791)
      ·
        refine ⟨128894078363219869894552187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85929385575479913263034791 128894078363219869894552187)
        ·
          refine ⟨193341117544829804841828281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128894078363219869894552187 193341117544829804841828281)
          ·
            refine ⟨145005838158622353631371211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193341117544829804841828281 145005838158622353631371211)
            ·
              refine ⟨217508757237933530447056817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145005838158622353631371211 217508757237933530447056817)
              ·
                refine ⟨163131567928450147835292613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217508757237933530447056817 163131567928450147835292613)
                ·
                  refine ⟨30587168986584402719117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163131567928450147835292613 30587168986584402719117365)
                  ·
                    refine ⟨2867547092492287754917253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30587168986584402719117365 2867547092492287754917253)
                    ·
                      refine ⟨537665079842303954046985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2867547092492287754917253 537665079842303954046985)
                      ·
                        rfl

theorem cell23_1047099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_1047099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047099 prefixEnd_1047099 := by exact prefixLift 1047099
  have htrace : WordTrace (prefixWord ++ tailWord_1047099) baseStart_1047099 baseEnd_1047099 := by
    simpa [prefixWord, tailWord_1047099, baseEnd_1047099] using wordTrace_append hprefix tailTrace_1047099
  have hstable : (prefixWord ++ tailWord_1047099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047099).length < 2 ^ (prefixWord ++ tailWord_1047099).sum := by decide
  have hdescent : baseEnd_1047099 < baseStart_1047099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047103 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 2, 3, 2]
def baseStart_1047103 : Nat := 118140960795 + 1047103 * 2 ^ 59
def prefixEnd_1047103 : Nat := 4983230072969 + 3 ^ 40 * 1047103 * 2
def baseEnd_1047103 : Nat := 537667133764921938396967

theorem tailTrace_1047103 : CollatzResearch.WordTrace tailWord_1047103 prefixEnd_1047103 537667133764921938396967 := by
  unfold tailWord_1047103
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190983925532136800049963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25460655950354757866699975 38190983925532136800049963)
  ·
    refine ⟨57286475888298205200074945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38190983925532136800049963 57286475888298205200074945)
    ·
      refine ⟨42964856916223653900056209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57286475888298205200074945 42964856916223653900056209)
      ·
        refine ⟨32223642687167740425042157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42964856916223653900056209 32223642687167740425042157)
        ·
          refine ⟨12083866007687902659390809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32223642687167740425042157 12083866007687902659390809)
          ·
            refine ⟨9062899505765926994543107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083866007687902659390809 9062899505765926994543107)
            ·
              refine ⟨13594349258648890491814661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062899505765926994543107 13594349258648890491814661)
              ·
                refine ⟨2548940485996666967215249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13594349258648890491814661 2548940485996666967215249)
                ·
                  refine ⟨1911705364497500225411437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2548940485996666967215249 1911705364497500225411437)
                  ·
                    refine ⟨716889511686562584529289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911705364497500225411437 716889511686562584529289)
                    ·
                      refine ⟨537667133764921938396967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716889511686562584529289 537667133764921938396967)
                      ·
                        rfl

theorem cell23_1047103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_1047103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047103 prefixEnd_1047103 := by exact prefixLift 1047103
  have htrace : WordTrace (prefixWord ++ tailWord_1047103) baseStart_1047103 baseEnd_1047103 := by
    simpa [prefixWord, tailWord_1047103, baseEnd_1047103] using wordTrace_append hprefix tailTrace_1047103
  have hstable : (prefixWord ++ tailWord_1047103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047103).length < 2 ^ (prefixWord ++ tailWord_1047103).sum := by decide
  have hdescent : baseEnd_1047103 < baseStart_1047103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047116 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1047116 : Nat := 118140960795 + 1047116 * 2 ^ 59
def prefixEnd_1047116 : Nat := 4983230072969 + 3 ^ 40 * 1047116 * 2
def baseEnd_1047116 : Nat := 537673809013430387534407

theorem tailTrace_1047116 : CollatzResearch.WordTrace tailWord_1047116 prefixEnd_1047116 537673809013430387534407 := by
  unfold tailWord_1047116
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095729037242520010136601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25460972049656693346848801 19095729037242520010136601)
  ·
    refine ⟨14321796777931890007602451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19095729037242520010136601 14321796777931890007602451)
    ·
      refine ⟨21482695166897835011403677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14321796777931890007602451 21482695166897835011403677)
      ·
        refine ⟨8056010687586688129276379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21482695166897835011403677 8056010687586688129276379)
        ·
          refine ⟨12084016031380032193914569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8056010687586688129276379 12084016031380032193914569)
          ·
            refine ⟨9063012023535024145435927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12084016031380032193914569 9063012023535024145435927)
            ·
              refine ⟨13594518035302536218153891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063012023535024145435927 13594518035302536218153891)
              ·
                refine ⟨20391777052953804327230837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594518035302536218153891 20391777052953804327230837)
                ·
                  refine ⟨1911729098714419155677891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20391777052953804327230837 1911729098714419155677891)
                  ·
                    refine ⟨2867593648071628733516837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1911729098714419155677891 2867593648071628733516837)
                    ·
                      refine ⟨537673809013430387534407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2867593648071628733516837 537673809013430387534407)
                      ·
                        rfl

theorem cell23_1047116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1047116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047116 prefixEnd_1047116 := by exact prefixLift 1047116
  have htrace : WordTrace (prefixWord ++ tailWord_1047116) baseStart_1047116 baseEnd_1047116 := by
    simpa [prefixWord, tailWord_1047116, baseEnd_1047116] using wordTrace_append hprefix tailTrace_1047116
  have hstable : (prefixWord ++ tailWord_1047116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047116).length < 2 ^ (prefixWord ++ tailWord_1047116).sum := by decide
  have hdescent : baseEnd_1047116 < baseStart_1047116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047144 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1047144 : Nat := 118140960795 + 1047144 * 2 ^ 59
def prefixEnd_1047144 : Nat := 4983230072969 + 3 ^ 40 * 1047144 * 2
def baseEnd_1047144 : Nat := 537688186471756277984279

theorem tailTrace_1047144 : CollatzResearch.WordTrace tailWord_1047144 prefixEnd_1047144 537688186471756277984279 := by
  unfold tailWord_1047144
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096239659191800401146243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25461652878922400534861657 19096239659191800401146243)
  ·
    refine ⟨28644359488787700601719365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19096239659191800401146243 28644359488787700601719365)
    ·
      refine ⟨5370817404147693862822381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28644359488787700601719365 5370817404147693862822381)
      ·
        refine ⟨2014056526555385198558393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5370817404147693862822381 2014056526555385198558393)
        ·
          refine ⟨1510542394916538898918795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014056526555385198558393 1510542394916538898918795)
          ·
            refine ⟨2265813592374808348378193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510542394916538898918795 2265813592374808348378193)
            ·
              refine ⟨1699360194281106261283645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265813592374808348378193 1699360194281106261283645)
              ·
                refine ⟨637260072855414847981367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699360194281106261283645 637260072855414847981367)
                ·
                  refine ⟨955890109283122271972051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637260072855414847981367 955890109283122271972051)
                  ·
                    refine ⟨1433835163924683407958077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 955890109283122271972051 1433835163924683407958077)
                    ·
                      refine ⟨537688186471756277984279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433835163924683407958077 537688186471756277984279)
                      ·
                        rfl

theorem cell23_1047144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1047144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047144 prefixEnd_1047144 := by exact prefixLift 1047144
  have htrace : WordTrace (prefixWord ++ tailWord_1047144) baseStart_1047144 baseEnd_1047144 := by
    simpa [prefixWord, tailWord_1047144, baseEnd_1047144] using wordTrace_append hprefix tailTrace_1047144
  have hstable : (prefixWord ++ tailWord_1047144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047144).length < 2 ^ (prefixWord ++ tailWord_1047144).sum := by decide
  have hdescent : baseEnd_1047144 < baseStart_1047144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047150 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1047150 : Nat := 118140960795 + 1047150 * 2 ^ 59
def prefixEnd_1047150 : Nat := 4983230072969 + 3 ^ 40 * 1047150 * 2
def baseEnd_1047150 : Nat := 537691267355683254509251

theorem tailTrace_1047150 : CollatzResearch.WordTrace tailWord_1047150 prefixEnd_1047150 537691267355683254509251 := by
  unfold tailWord_1047150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774087269545232978376363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25461798770907909218007269 4774087269545232978376363)
  ·
    refine ⟨7161130904317849467564545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4774087269545232978376363 7161130904317849467564545)
    ·
      refine ⟨5370848178238387100673409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7161130904317849467564545 5370848178238387100673409)
      ·
        refine ⟨4028136133678790325505057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5370848178238387100673409 4028136133678790325505057)
        ·
          refine ⟨3021102100259092744128793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4028136133678790325505057 3021102100259092744128793)
          ·
            refine ⟨2265826575194319558096595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3021102100259092744128793 2265826575194319558096595)
            ·
              refine ⟨3398739862791479337144893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265826575194319558096595 3398739862791479337144893)
              ·
                refine ⟨1274527448546804751429335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398739862791479337144893 1274527448546804751429335)
                ·
                  refine ⟨1911791172820207127144003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274527448546804751429335 1911791172820207127144003)
                  ·
                    refine ⟨2867686759230310690716005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1911791172820207127144003 2867686759230310690716005)
                    ·
                      refine ⟨537691267355683254509251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2867686759230310690716005 537691267355683254509251)
                      ·
                        rfl

theorem cell23_1047150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1047150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047150 prefixEnd_1047150 := by exact prefixLift 1047150
  have htrace : WordTrace (prefixWord ++ tailWord_1047150) baseStart_1047150 baseEnd_1047150 := by
    simpa [prefixWord, tailWord_1047150, baseEnd_1047150] using wordTrace_append hprefix tailTrace_1047150
  have hstable : (prefixWord ++ tailWord_1047150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047150).length < 2 ^ (prefixWord ++ tailWord_1047150).sum := by decide
  have hdescent : baseEnd_1047150 < baseStart_1047150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047201 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1047201 : Nat := 118140960795 + 1047201 * 2 ^ 59
def prefixEnd_1047201 : Nat := 4983230072969 + 3 ^ 40 * 1047201 * 2
def baseEnd_1047201 : Nat := 537717454869062554971517

theorem tailTrace_1047201 : CollatzResearch.WordTrace tailWord_1047201 prefixEnd_1047201 537717454869062554971517 := by
  unfold tailWord_1047201
  simp only [CollatzResearch.WordTrace]
  refine ⟨38194558279177099537117457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25463038852784733024744971 38194558279177099537117457)
  ·
    refine ⟨28645918709382824652838093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38194558279177099537117457 28645918709382824652838093)
    ·
      refine ⟨10742219516018559244814285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28645918709382824652838093 10742219516018559244814285)
      ·
        refine ⟨4028332318506959716805357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10742219516018559244814285 4028332318506959716805357)
        ·
          refine ⟨1510624619440109893802009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4028332318506959716805357 1510624619440109893802009)
          ·
            refine ⟨1132968464580082420351507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510624619440109893802009 1132968464580082420351507)
            ·
              refine ⟨1699452696870123630527261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132968464580082420351507 1699452696870123630527261)
              ·
                refine ⟨637294761326296361447723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699452696870123630527261 637294761326296361447723)
                ·
                  refine ⟨955942141989444542171585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637294761326296361447723 955942141989444542171585)
                  ·
                    refine ⟨716956606492083406628689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 955942141989444542171585 716956606492083406628689)
                    ·
                      refine ⟨537717454869062554971517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716956606492083406628689 537717454869062554971517)
                      ·
                        rfl

theorem cell23_1047201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1047201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047201 prefixEnd_1047201 := by exact prefixLift 1047201
  have htrace : WordTrace (prefixWord ++ tailWord_1047201) baseStart_1047201 baseEnd_1047201 := by
    simpa [prefixWord, tailWord_1047201, baseEnd_1047201] using wordTrace_append hprefix tailTrace_1047201
  have hstable : (prefixWord ++ tailWord_1047201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047201).length < 2 ^ (prefixWord ++ tailWord_1047201).sum := by decide
  have hdescent : baseEnd_1047201 < baseStart_1047201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047226 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1047226 : Nat := 118140960795 + 1047226 * 2 ^ 59
def prefixEnd_1047226 : Nat := 4983230072969 + 3 ^ 40 * 1047226 * 2
def baseEnd_1047226 : Nat := 537730291885424957158901

theorem tailTrace_1047226 : CollatzResearch.WordTrace tailWord_1047226 prefixEnd_1047226 537730291885424957158901 := by
  unfold tailWord_1047226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548867526021632201694383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25463646736057685871185021 9548867526021632201694383)
  ·
    refine ⟨14323301289032448302541575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9548867526021632201694383 14323301289032448302541575)
    ·
      refine ⟨21484951933548672453812363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323301289032448302541575 21484951933548672453812363)
      ·
        refine ⟨32227427900323008680718545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21484951933548672453812363 32227427900323008680718545)
        ·
          refine ⟨24170570925242256510538909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32227427900323008680718545 24170570925242256510538909)
          ·
            refine ⟨9063964096965846191452091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24170570925242256510538909 9063964096965846191452091)
            ·
              refine ⟨13595946145448769287178137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9063964096965846191452091 13595946145448769287178137)
              ·
                refine ⟨10196959609086576965383603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13595946145448769287178137 10196959609086576965383603)
                ·
                  refine ⟨15295439413629865448075405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196959609086576965383603 15295439413629865448075405)
                  ·
                    refine ⟨5735789780111199543028277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15295439413629865448075405 5735789780111199543028277)
                    ·
                      refine ⟨537730291885424957158901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5735789780111199543028277 537730291885424957158901)
                      ·
                        rfl

theorem cell23_1047226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1047226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047226 prefixEnd_1047226 := by exact prefixLift 1047226
  have htrace : WordTrace (prefixWord ++ tailWord_1047226) baseStart_1047226 baseEnd_1047226 := by
    simpa [prefixWord, tailWord_1047226, baseEnd_1047226] using wordTrace_append hprefix tailTrace_1047226
  have hstable : (prefixWord ++ tailWord_1047226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047226).length < 2 ^ (prefixWord ++ tailWord_1047226).sum := by decide
  have hdescent : baseEnd_1047226 < baseStart_1047226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047238 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1047238 : Nat := 118140960795 + 1047238 * 2 ^ 59
def prefixEnd_1047238 : Nat := 4983230072969 + 3 ^ 40 * 1047238 * 2
def baseEnd_1047238 : Nat := 537736453653278910208847

theorem tailTrace_1047238 : CollatzResearch.WordTrace tailWord_1047238 prefixEnd_1047238 537736453653278910208847 := by
  unfold tailWord_1047238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193622118126345464256699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25463938520028703237476245 1193622118126345464256699)
  ·
    refine ⟨1790433177189518196385049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193622118126345464256699 1790433177189518196385049)
    ·
      refine ⟨1342824882892138647288787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1790433177189518196385049 1342824882892138647288787)
      ·
        refine ⟨2014237324338207970933181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342824882892138647288787 2014237324338207970933181)
        ·
          refine ⟨755338996626827989099943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2014237324338207970933181 755338996626827989099943)
          ·
            refine ⟨1133008494940241983649915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755338996626827989099943 1133008494940241983649915)
            ·
              refine ⟨1699512742410362975474873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133008494940241983649915 1699512742410362975474873)
              ·
                refine ⟨1274634556807772231606155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699512742410362975474873 1274634556807772231606155)
                ·
                  refine ⟨1911951835211658347409233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274634556807772231606155 1911951835211658347409233)
                  ·
                    refine ⟨1433963876408743760556925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1911951835211658347409233 1433963876408743760556925)
                    ·
                      refine ⟨537736453653278910208847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1433963876408743760556925 537736453653278910208847)
                      ·
                        rfl

theorem cell23_1047238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1047238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047238 prefixEnd_1047238 := by exact prefixLift 1047238
  have htrace : WordTrace (prefixWord ++ tailWord_1047238) baseStart_1047238 baseEnd_1047238 := by
    simpa [prefixWord, tailWord_1047238, baseEnd_1047238] using wordTrace_append hprefix tailTrace_1047238
  have hstable : (prefixWord ++ tailWord_1047238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047238).length < 2 ^ (prefixWord ++ tailWord_1047238).sum := by decide
  have hdescent : baseEnd_1047238 < baseStart_1047238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047244 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1047244 : Nat := 118140960795 + 1047244 * 2 ^ 59
def prefixEnd_1047244 : Nat := 4983230072969 + 3 ^ 40 * 1047244 * 2
def baseEnd_1047244 : Nat := 537739534537205886733819

theorem tailTrace_1047244 : CollatzResearch.WordTrace tailWord_1047244 prefixEnd_1047244 537739534537205886733819 := by
  unfold tailWord_1047244
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098063309010658940466393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25464084412014211920621857 19098063309010658940466393)
  ·
    refine ⟨14323547481757994205349795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098063309010658940466393 14323547481757994205349795)
    ·
      refine ⟨21485321222636991308024693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323547481757994205349795 21485321222636991308024693)
      ·
        refine ⟨2014248864622217935127315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21485321222636991308024693 2014248864622217935127315)
        ·
          refine ⟨3021373296933326902690973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014248864622217935127315 3021373296933326902690973)
          ·
            refine ⟨1133014986349997588509115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3021373296933326902690973 1133014986349997588509115)
            ·
              refine ⟨1699522479524996382763673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133014986349997588509115 1699522479524996382763673)
              ·
                refine ⟨1274641859643747287072755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699522479524996382763673 1274641859643747287072755)
                ·
                  refine ⟨1911962789465620930609133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274641859643747287072755 1911962789465620930609133)
                  ·
                    refine ⟨716986046049607848978425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1911962789465620930609133 716986046049607848978425)
                    ·
                      refine ⟨537739534537205886733819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 716986046049607848978425 537739534537205886733819)
                      ·
                        rfl

theorem cell23_1047244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1047244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047244 prefixEnd_1047244 := by exact prefixLift 1047244
  have htrace : WordTrace (prefixWord ++ tailWord_1047244) baseStart_1047244 baseEnd_1047244 := by
    simpa [prefixWord, tailWord_1047244, baseEnd_1047244] using wordTrace_append hprefix tailTrace_1047244
  have hstable : (prefixWord ++ tailWord_1047244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047244).length < 2 ^ (prefixWord ++ tailWord_1047244).sum := by decide
  have hdescent : baseEnd_1047244 < baseStart_1047244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047260 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1047260 : Nat := 118140960795 + 1047260 * 2 ^ 59
def prefixEnd_1047260 : Nat := 4983230072969 + 3 ^ 40 * 1047260 * 2
def baseEnd_1047260 : Nat := 537747750227677824133745

theorem tailTrace_1047260 : CollatzResearch.WordTrace tailWord_1047260 prefixEnd_1047260 537747750227677824133745 := by
  unfold tailWord_1047260
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098355092981676306757617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25464473457308901742343489 19098355092981676306757617)
  ·
    refine ⟨14323766319736257230068213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098355092981676306757617 14323766319736257230068213)
    ·
      refine ⟨1342853092475274115318895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14323766319736257230068213 1342853092475274115318895)
      ·
        refine ⟨2014279638712911172978343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342853092475274115318895 2014279638712911172978343)
        ·
          refine ⟨3021419458069366759467515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014279638712911172978343 3021419458069366759467515)
          ·
            refine ⟨4532129187104050139201273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021419458069366759467515 4532129187104050139201273)
            ·
              refine ⟨3399096890328037604400955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4532129187104050139201273 3399096890328037604400955)
              ·
                refine ⟨5098645335492056406601433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399096890328037604400955 5098645335492056406601433)
                ·
                  refine ⟨3823984001619042304951075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098645335492056406601433 3823984001619042304951075)
                  ·
                    refine ⟨5735976002428563457426613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3823984001619042304951075 5735976002428563457426613)
                    ·
                      refine ⟨537747750227677824133745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5735976002428563457426613 537747750227677824133745)
                      ·
                        rfl

theorem cell23_1047260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1047260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047260 prefixEnd_1047260 := by exact prefixLift 1047260
  have htrace : WordTrace (prefixWord ++ tailWord_1047260) baseStart_1047260 baseEnd_1047260 := by
    simpa [prefixWord, tailWord_1047260, baseEnd_1047260] using wordTrace_append hprefix tailTrace_1047260
  have hstable : (prefixWord ++ tailWord_1047260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047260).length < 2 ^ (prefixWord ++ tailWord_1047260).sum := by decide
  have hdescent : baseEnd_1047260 < baseStart_1047260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047276 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_1047276 : Nat := 118140960795 + 1047276 * 2 ^ 59
def prefixEnd_1047276 : Nat := 4983230072969 + 3 ^ 40 * 1047276 * 2
def baseEnd_1047276 : Nat := 179251988639383253844557

theorem tailTrace_1047276 : CollatzResearch.WordTrace tailWord_1047276 prefixEnd_1047276 179251988639383253844557 := by
  unfold tailWord_1047276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098646876952693673048841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25464862502603591564065121 19098646876952693673048841)
  ·
    refine ⟨14323985157714520254786631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098646876952693673048841 14323985157714520254786631)
    ·
      refine ⟨21485977736571780382179947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323985157714520254786631 21485977736571780382179947)
      ·
        refine ⟨32228966604857670573269921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21485977736571780382179947 32228966604857670573269921)
        ·
          refine ⟨24171724953643252929952441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32228966604857670573269921 24171724953643252929952441)
          ·
            refine ⟨18128793715232439697464331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24171724953643252929952441 18128793715232439697464331)
            ·
              refine ⟨27193190572848659546196497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18128793715232439697464331 27193190572848659546196497)
              ·
                refine ⟨20394892929636494659647373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27193190572848659546196497 20394892929636494659647373)
                ·
                  refine ⟨7648084848613685497367765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20394892929636494659647373 7648084848613685497367765)
                  ·
                    refine ⟨179251988639383253844557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7648084848613685497367765 179251988639383253844557)
                    ·
                      rfl

theorem cell23_1047276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_1047276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047276 prefixEnd_1047276 := by exact prefixLift 1047276
  have htrace : WordTrace (prefixWord ++ tailWord_1047276) baseStart_1047276 baseEnd_1047276 := by
    simpa [prefixWord, tailWord_1047276, baseEnd_1047276] using wordTrace_append hprefix tailTrace_1047276
  have hstable : (prefixWord ++ tailWord_1047276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047276).length < 2 ^ (prefixWord ++ tailWord_1047276).sum := by decide
  have hdescent : baseEnd_1047276 < baseStart_1047276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047300 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1047300 : Nat := 118140960795 + 1047300 * 2 ^ 59
def prefixEnd_1047300 : Nat := 4983230072969 + 3 ^ 40 * 1047300 * 2
def baseEnd_1047300 : Nat := 537768289453857667633561

theorem tailTrace_1047300 : CollatzResearch.WordTrace tailWord_1047300 prefixEnd_1047300 537768289453857667633561 := by
  unfold tailWord_1047300
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099084552909219722485677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25465446070545626296647569 19099084552909219722485677)
  ·
    refine ⟨7162156707340957395932129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19099084552909219722485677 7162156707340957395932129)
    ·
      refine ⟨5371617530505718046949097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162156707340957395932129 5371617530505718046949097)
      ·
        refine ⟨4028713147879288535211823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5371617530505718046949097 4028713147879288535211823)
        ·
          refine ⟨6043069721818932802817735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028713147879288535211823 6043069721818932802817735)
          ·
            refine ⟨9064604582728399204226603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043069721818932802817735 9064604582728399204226603)
            ·
              refine ⟨13596906874092598806339905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064604582728399204226603 13596906874092598806339905)
              ·
                refine ⟨10197680155569449104754929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13596906874092598806339905 10197680155569449104754929)
                ·
                  refine ⟨7648260116677086828566197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197680155569449104754929 7648260116677086828566197)
                  ·
                    refine ⟨717024385938476890178081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7648260116677086828566197 717024385938476890178081)
                    ·
                      refine ⟨537768289453857667633561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717024385938476890178081 537768289453857667633561)
                      ·
                        rfl

theorem cell23_1047300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1047300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047300 prefixEnd_1047300 := by exact prefixLift 1047300
  have htrace : WordTrace (prefixWord ++ tailWord_1047300) baseStart_1047300 baseEnd_1047300 := by
    simpa [prefixWord, tailWord_1047300, baseEnd_1047300] using wordTrace_append hprefix tailTrace_1047300
  have hstable : (prefixWord ++ tailWord_1047300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047300).length < 2 ^ (prefixWord ++ tailWord_1047300).sum := by decide
  have hdescent : baseEnd_1047300 < baseStart_1047300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047314 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_1047314 : Nat := 118140960795 + 1047314 * 2 ^ 59
def prefixEnd_1047314 : Nat := 4983230072969 + 3 ^ 40 * 1047314 * 2
def baseEnd_1047314 : Nat := 59752830909224512539833

theorem tailTrace_1047314 : CollatzResearch.WordTrace tailWord_1047314 prefixEnd_1047314 59752830909224512539833 := by
  unfold tailWord_1047314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549669931941929958995249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25465786485178479890653997 9549669931941929958995249)
  ·
    refine ⟨7162252448956447469246437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9549669931941929958995249 7162252448956447469246437)
    ·
      refine ⟨1342922334179333900483707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7162252448956447469246437 1342922334179333900483707)
      ·
        refine ⟨2014383501269000850725561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342922334179333900483707 2014383501269000850725561)
        ·
          refine ⟨1510787625951750638044171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014383501269000850725561 1510787625951750638044171)
          ·
            refine ⟨2266181438927625957066257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510787625951750638044171 2266181438927625957066257)
            ·
              refine ⟨1699636079195719467799693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266181438927625957066257 1699636079195719467799693)
              ·
                refine ⟨637363529698394800424885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699636079195719467799693 637363529698394800424885)
                ·
                  refine ⟨59752830909224512539833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637363529698394800424885 59752830909224512539833)
                  ·
                    rfl

theorem cell23_1047314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_1047314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047314 prefixEnd_1047314 := by exact prefixLift 1047314
  have htrace : WordTrace (prefixWord ++ tailWord_1047314) baseStart_1047314 baseEnd_1047314 := by
    simpa [prefixWord, tailWord_1047314, baseEnd_1047314] using wordTrace_append hprefix tailTrace_1047314
  have hstable : (prefixWord ++ tailWord_1047314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047314).length < 2 ^ (prefixWord ++ tailWord_1047314).sum := by decide
  have hdescent : baseEnd_1047314 < baseStart_1047314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047340 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_1047340 : Nat := 118140960795 + 1047340 * 2 ^ 59
def prefixEnd_1047340 : Nat := 4983230072969 + 3 ^ 40 * 1047340 * 2
def baseEnd_1047340 : Nat := 179262942893345837044459

theorem tailTrace_1047340 : CollatzResearch.WordTrace tailWord_1047340 prefixEnd_1047340 179262942893345837044459 := by
  unfold tailWord_1047340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099814012836763138213737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25466418683782350850951649 19099814012836763138213737)
  ·
    refine ⟨14324860509627572353660303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19099814012836763138213737 14324860509627572353660303)
    ·
      refine ⟨21487290764441358530490455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324860509627572353660303 21487290764441358530490455)
      ·
        refine ⟨32230936146662037795735683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21487290764441358530490455 32230936146662037795735683)
        ·
          refine ⟨48346404219993056693603525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32230936146662037795735683 48346404219993056693603525)
          ·
            refine ⟨9064950791248698130050661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48346404219993056693603525 9064950791248698130050661)
            ·
              refine ⟨1699678273359130899384499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9064950791248698130050661 1699678273359130899384499)
              ·
                refine ⟨2549517410038696349076749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699678273359130899384499 2549517410038696349076749)
                ·
                  refine ⟨956069028764511130903781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2549517410038696349076749 956069028764511130903781)
                  ·
                    refine ⟨179262942893345837044459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956069028764511130903781 179262942893345837044459)
                    ·
                      rfl

theorem cell23_1047340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_1047340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047340 prefixEnd_1047340 := by exact prefixLift 1047340
  have htrace : WordTrace (prefixWord ++ tailWord_1047340) baseStart_1047340 baseEnd_1047340 := by
    simpa [prefixWord, tailWord_1047340, baseEnd_1047340] using wordTrace_append hprefix tailTrace_1047340
  have hstable : (prefixWord ++ tailWord_1047340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047340).length < 2 ^ (prefixWord ++ tailWord_1047340).sum := by decide
  have hdescent : baseEnd_1047340 < baseStart_1047340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047363 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3]
def baseStart_1047363 : Nat := 118140960795 + 1047363 * 2 ^ 59
def prefixEnd_1047363 : Nat := 4983230072969 + 3 ^ 40 * 1047363 * 2
def baseEnd_1047363 : Nat := 537800638735090921145771

theorem tailTrace_1047363 : CollatzResearch.WordTrace tailWord_1047363 prefixEnd_1047363 537800638735090921145771 := by
  unfold tailWord_1047363
  simp only [CollatzResearch.WordTrace]
  refine ⟨38200466904590201204514743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25466977936393467469676495 38200466904590201204514743)
  ·
    refine ⟨57300700356885301806772115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38200466904590201204514743 57300700356885301806772115)
    ·
      refine ⟨85951050535327952710158173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57300700356885301806772115 85951050535327952710158173)
      ·
        refine ⟨32231643950747982266309315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85951050535327952710158173 32231643950747982266309315)
        ·
          refine ⟨48347465926121973399463973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32231643950747982266309315 48347465926121973399463973)
          ·
            refine ⟨9065149861147870012399495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48347465926121973399463973 9065149861147870012399495)
            ·
              refine ⟨13597724791721805018599243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065149861147870012399495 13597724791721805018599243)
              ·
                refine ⟨20396587187582707527898865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597724791721805018599243 20396587187582707527898865)
                ·
                  refine ⟨15297440390687030645924149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20396587187582707527898865 15297440390687030645924149)
                  ·
                    refine ⟨1434135036626909123055389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15297440390687030645924149 1434135036626909123055389)
                    ·
                      refine ⟨537800638735090921145771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1434135036626909123055389 537800638735090921145771)
                      ·
                        rfl

theorem cell23_1047363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_1047363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047363 prefixEnd_1047363 := by exact prefixLift 1047363
  have htrace : WordTrace (prefixWord ++ tailWord_1047363) baseStart_1047363 baseEnd_1047363 := by
    simpa [prefixWord, tailWord_1047363, baseEnd_1047363] using wordTrace_append hprefix tailTrace_1047363
  have hstable : (prefixWord ++ tailWord_1047363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047363).length < 2 ^ (prefixWord ++ tailWord_1047363).sum := by decide
  have hdescent : baseEnd_1047363 < baseStart_1047363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047397 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1047397 : Nat := 118140960795 + 1047397 * 2 ^ 59
def prefixEnd_1047397 : Nat := 4983230072969 + 3 ^ 40 * 1047397 * 2
def baseEnd_1047397 : Nat := 537818097077343788120615

theorem tailTrace_1047397 : CollatzResearch.WordTrace tailWord_1047397 prefixEnd_1047397 537818097077343788120615 := by
  unfold tailWord_1047397
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201706986467025011252445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25467804657644683340834963 38201706986467025011252445)
  ·
    refine ⟨14325640119925134379219667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38201706986467025011252445 14325640119925134379219667)
    ·
      refine ⟨21488460179887701568829501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325640119925134379219667 21488460179887701568829501)
      ·
        refine ⟨8058172567457888088311063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21488460179887701568829501 8058172567457888088311063)
        ·
          refine ⟨12087258851186832132466595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058172567457888088311063 12087258851186832132466595)
          ·
            refine ⟨18130888276780248198699893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12087258851186832132466595 18130888276780248198699893)
            ·
              refine ⟨1699770775948148268628115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18130888276780248198699893 1699770775948148268628115)
              ·
                refine ⟨2549656163922222402942173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699770775948148268628115 2549656163922222402942173)
                ·
                  refine ⟨956121061470833401103315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2549656163922222402942173 956121061470833401103315)
                  ·
                    refine ⟨1434181592206250101654973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 956121061470833401103315 1434181592206250101654973)
                    ·
                      refine ⟨537818097077343788120615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1434181592206250101654973 537818097077343788120615)
                      ·
                        rfl

theorem cell23_1047397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1047397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047397 prefixEnd_1047397 := by exact prefixLift 1047397
  have htrace : WordTrace (prefixWord ++ tailWord_1047397) baseStart_1047397 baseEnd_1047397 := by
    simpa [prefixWord, tailWord_1047397, baseEnd_1047397] using wordTrace_append hprefix tailTrace_1047397
  have hstable : (prefixWord ++ tailWord_1047397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047397).length < 2 ^ (prefixWord ++ tailWord_1047397).sum := by decide
  have hdescent : baseEnd_1047397 < baseStart_1047397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047417 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_1047417 : Nat := 118140960795 + 1047417 * 2 ^ 59
def prefixEnd_1047417 : Nat := 4983230072969 + 3 ^ 40 * 1047417 * 2
def baseEnd_1047417 : Nat := 179276122230144569956841

theorem tailTrace_1047417 : CollatzResearch.WordTrace tailWord_1047417 prefixEnd_1047417 179276122230144569956841 := by
  unfold tailWord_1047417
  simp only [CollatzResearch.WordTrace]
  refine ⟨38202436446394568426980505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25468290964263045617987003 38202436446394568426980505)
  ·
    refine ⟨28651827334795926320235379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38202436446394568426980505 28651827334795926320235379)
    ·
      refine ⟨42977741002193889480353069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28651827334795926320235379 42977741002193889480353069)
      ·
        refine ⟨16116652875822708555132401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42977741002193889480353069 16116652875822708555132401)
        ·
          refine ⟨12087489656867031416349301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16116652875822708555132401 12087489656867031416349301)
          ·
            refine ⟨1133202155331284195282747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12087489656867031416349301 1133202155331284195282747)
            ·
              refine ⟨1699803232996926292924121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133202155331284195282747 1699803232996926292924121)
              ·
                refine ⟨1274852424747694719693091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699803232996926292924121 1274852424747694719693091)
                ·
                  refine ⟨1912278637121542079539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274852424747694719693091 1912278637121542079539637)
                  ·
                    refine ⟨179276122230144569956841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1912278637121542079539637 179276122230144569956841)
                    ·
                      rfl

theorem cell23_1047417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_1047417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047417 prefixEnd_1047417 := by exact prefixLift 1047417
  have htrace : WordTrace (prefixWord ++ tailWord_1047417) baseStart_1047417 baseEnd_1047417 := by
    simpa [prefixWord, tailWord_1047417, baseEnd_1047417] using wordTrace_append hprefix tailTrace_1047417
  have hstable : (prefixWord ++ tailWord_1047417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047417).length < 2 ^ (prefixWord ++ tailWord_1047417).sum := by decide
  have hdescent : baseEnd_1047417 < baseStart_1047417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047420 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_1047420 : Nat := 118140960795 + 1047420 * 2 ^ 59
def prefixEnd_1047420 : Nat := 4983230072969 + 3 ^ 40 * 1047420 * 2
def baseEnd_1047420 : Nat := 537829907132397198133009

theorem tailTrace_1047420 : CollatzResearch.WordTrace tailWord_1047420 prefixEnd_1047420 537829907132397198133009 := by
  unfold tailWord_1047420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19101272932691849969669857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25468363910255799959559809 19101272932691849969669857)
  ·
    refine ⟨14325954699518887477252393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19101272932691849969669857 14325954699518887477252393)
    ·
      refine ⟨10744466024639165607939295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14325954699518887477252393 10744466024639165607939295)
      ·
        refine ⟨16116699036958748411908943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10744466024639165607939295 16116699036958748411908943)
        ·
          refine ⟨24175048555438122617863415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16116699036958748411908943 24175048555438122617863415)
          ·
            refine ⟨36262572833157183926795123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24175048555438122617863415 36262572833157183926795123)
            ·
              refine ⟨54393859249735775890192685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36262572833157183926795123 54393859249735775890192685)
              ·
                refine ⟨20397697218650915958822257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54393859249735775890192685 20397697218650915958822257)
                ·
                  refine ⟨15298272913988186969116693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20397697218650915958822257 15298272913988186969116693)
                  ·
                    refine ⟨717106542843196264177345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15298272913988186969116693 717106542843196264177345)
                    ·
                      refine ⟨537829907132397198133009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 717106542843196264177345 537829907132397198133009)
                      ·
                        rfl

theorem cell23_1047420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_1047420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047420 prefixEnd_1047420 := by exact prefixLift 1047420
  have htrace : WordTrace (prefixWord ++ tailWord_1047420) baseStart_1047420 baseEnd_1047420 := by
    simpa [prefixWord, tailWord_1047420, baseEnd_1047420] using wordTrace_append hprefix tailTrace_1047420
  have hstable : (prefixWord ++ tailWord_1047420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047420).length < 2 ^ (prefixWord ++ tailWord_1047420).sum := by decide
  have hdescent : baseEnd_1047420 < baseStart_1047420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047423 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1047423 : Nat := 118140960795 + 1047423 * 2 ^ 59
def prefixEnd_1047423 : Nat := 4983230072969 + 3 ^ 40 * 1047423 * 2
def baseEnd_1047423 : Nat := 537831447574360686395495

theorem tailTrace_1047423 : CollatzResearch.WordTrace tailWord_1047423 prefixEnd_1047423 537831447574360686395495 := by
  unfold tailWord_1047423
  simp only [CollatzResearch.WordTrace]
  refine ⟨38202655284372831451698923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25468436856248554301132615 38202655284372831451698923)
  ·
    refine ⟨57303982926559247177548385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38202655284372831451698923 57303982926559247177548385)
    ·
      refine ⟨42977987194919435383161289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57303982926559247177548385 42977987194919435383161289)
      ·
        refine ⟨32233490396189576537370967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42977987194919435383161289 32233490396189576537370967)
        ·
          refine ⟨48350235594284364806056451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32233490396189576537370967 48350235594284364806056451)
          ·
            refine ⟨72525353391426547209084677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48350235594284364806056451 72525353391426547209084677)
            ·
              refine ⟨13598503760892477601703377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72525353391426547209084677 13598503760892477601703377)
              ·
                refine ⟨10198877820669358201277533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13598503760892477601703377 10198877820669358201277533)
                ·
                  refine ⟨3824579182751009325479075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10198877820669358201277533 3824579182751009325479075)
                  ·
                    refine ⟨5736868774126513988218613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3824579182751009325479075 5736868774126513988218613)
                    ·
                      refine ⟨537831447574360686395495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5736868774126513988218613 537831447574360686395495)
                      ·
                        rfl

theorem cell23_1047423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1047423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047423 prefixEnd_1047423 := by exact prefixLift 1047423
  have htrace : WordTrace (prefixWord ++ tailWord_1047423) baseStart_1047423 baseEnd_1047423 := by
    simpa [prefixWord, tailWord_1047423, baseEnd_1047423] using wordTrace_append hprefix tailTrace_1047423
  have hstable : (prefixWord ++ tailWord_1047423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047423).length < 2 ^ (prefixWord ++ tailWord_1047423).sum := by decide
  have hdescent : baseEnd_1047423 < baseStart_1047423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047434 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_1047434 : Nat := 118140960795 + 1047434 * 2 ^ 59
def prefixEnd_1047434 : Nat := 4983230072969 + 3 ^ 40 * 1047434 * 2
def baseEnd_1047434 : Nat := 179279031953853381119315

theorem tailTrace_1047434 : CollatzResearch.WordTrace tailWord_1047434 prefixEnd_1047434 179279031953853381119315 := by
  unfold tailWord_1047434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550764121833245082587339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25468704324888653553566237 9550764121833245082587339)
  ·
    refine ⟨14326146182749867623881009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550764121833245082587339 14326146182749867623881009)
    ·
      refine ⟨10744609637062400717910757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14326146182749867623881009 10744609637062400717910757)
      ·
        refine ⟨2014614306949200134608267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10744609637062400717910757 2014614306949200134608267)
        ·
          refine ⟨3021921460423800201912401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014614306949200134608267 3021921460423800201912401)
          ·
            refine ⟨2266441095317850151434301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3021921460423800201912401 2266441095317850151434301)
            ·
              refine ⟨849915410744193806787863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2266441095317850151434301 849915410744193806787863)
              ·
                refine ⟨1274873116116290710181795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849915410744193806787863 1274873116116290710181795)
                ·
                  refine ⟨1912309674174436065272693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1274873116116290710181795 1912309674174436065272693)
                  ·
                    refine ⟨179279031953853381119315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1912309674174436065272693 179279031953853381119315)
                    ·
                      rfl

theorem cell23_1047434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_1047434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047434 prefixEnd_1047434 := by exact prefixLift 1047434
  have htrace : WordTrace (prefixWord ++ tailWord_1047434) baseStart_1047434 baseEnd_1047434 := by
    simpa [prefixWord, tailWord_1047434, baseEnd_1047434] using wordTrace_append hprefix tailTrace_1047434
  have hstable : (prefixWord ++ tailWord_1047434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047434).length < 2 ^ (prefixWord ++ tailWord_1047434).sum := by decide
  have hdescent : baseEnd_1047434 < baseStart_1047434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047447 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 2, 4]
def baseStart_1047447 : Nat := 118140960795 + 1047447 * 2 ^ 59
def prefixEnd_1047447 : Nat := 4983230072969 + 3 ^ 40 * 1047447 * 2
def baseEnd_1047447 : Nat := 179281257036689530831795

theorem tailTrace_1047447 : CollatzResearch.WordTrace tailWord_1047447 prefixEnd_1047447 179281257036689530831795 := by
  unfold tailWord_1047447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38203530636285883550572595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25469020424190589033715063 38203530636285883550572595)
  ·
    refine ⟨57305295954428825325858893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38203530636285883550572595 57305295954428825325858893)
    ·
      refine ⟨21489485982910809497197085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57305295954428825325858893 21489485982910809497197085)
      ·
        refine ⟨8058557243591553561448907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21489485982910809497197085 8058557243591553561448907)
        ·
          refine ⟨12087835865387330342173361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058557243591553561448907 12087835865387330342173361)
          ·
            refine ⟨9065876899040497756630021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087835865387330342173361 9065876899040497756630021)
            ·
              refine ⟨1699851918570093329368129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9065876899040497756630021 1699851918570093329368129)
              ·
                refine ⟨1274888938927569997026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699851918570093329368129 1274888938927569997026097)
                ·
                  refine ⟨956166704195677497769573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1274888938927569997026097 956166704195677497769573)
                  ·
                    refine ⟨179281257036689530831795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956166704195677497769573 179281257036689530831795)
                    ·
                      rfl

theorem cell23_1047447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_1047447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047447 prefixEnd_1047447 := by exact prefixLift 1047447
  have htrace : WordTrace (prefixWord ++ tailWord_1047447) baseStart_1047447 baseEnd_1047447 := by
    simpa [prefixWord, tailWord_1047447, baseEnd_1047447] using wordTrace_append hprefix tailTrace_1047447
  have hstable : (prefixWord ++ tailWord_1047447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047447).length < 2 ^ (prefixWord ++ tailWord_1047447).sum := by decide
  have hdescent : baseEnd_1047447 < baseStart_1047447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047457 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1047457 : Nat := 118140960795 + 1047457 * 2 ^ 59
def prefixEnd_1047457 : Nat := 4983230072969 + 3 ^ 40 * 1047457 * 2
def baseEnd_1047457 : Nat := 537848905916613553370339

theorem tailTrace_1047457 : CollatzResearch.WordTrace tailWord_1047457 prefixEnd_1047457 537848905916613553370339 := by
  unfold tailWord_1047457
  simp only [CollatzResearch.WordTrace]
  refine ⟨38203895366249655258436625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25469263577499770172291083 38203895366249655258436625)
  ·
    refine ⟨28652921524687241443827469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38203895366249655258436625 28652921524687241443827469)
    ·
      refine ⟨10744845571757715541435301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28652921524687241443827469 10744845571757715541435301)
      ·
        refine ⟨2014658544704571664019119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10744845571757715541435301 2014658544704571664019119)
        ·
          refine ⟨3021987817056857496028679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014658544704571664019119 3021987817056857496028679)
          ·
            refine ⟨4532981725585286244043019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021987817056857496028679 4532981725585286244043019)
            ·
              refine ⟨6799472588377929366064529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532981725585286244043019 6799472588377929366064529)
              ·
                refine ⟨5099604441283447024548397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799472588377929366064529 5099604441283447024548397)
                ·
                  refine ⟨1912351665481292634205649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5099604441283447024548397 1912351665481292634205649)
                  ·
                    refine ⟨1434263749110969475654237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1912351665481292634205649 1434263749110969475654237)
                    ·
                      refine ⟨537848905916613553370339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1434263749110969475654237 537848905916613553370339)
                      ·
                        rfl

theorem cell23_1047457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1047457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1047457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1047457 prefixEnd_1047457 := by exact prefixLift 1047457
  have htrace : WordTrace (prefixWord ++ tailWord_1047457) baseStart_1047457 baseEnd_1047457 := by
    simpa [prefixWord, tailWord_1047457, baseEnd_1047457] using wordTrace_append hprefix tailTrace_1047457
  have hstable : (prefixWord ++ tailWord_1047457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047457).length < 2 ^ (prefixWord ++ tailWord_1047457).sum := by decide
  have hdescent : baseEnd_1047457 < baseStart_1047457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
